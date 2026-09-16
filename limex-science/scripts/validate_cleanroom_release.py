"""Validate the bounded LIMEX Science cleanroom candidate without network."""
from __future__ import annotations

import ast
import hashlib
import json
import os
import platform
import re
import stat
import subprocess
import sys
import tempfile
from pathlib import Path


ROOT = Path(__file__).resolve().parent.parent
EVIDENCE = ROOT / "evidence"
STDOUT_LOG = EVIDENCE / "CLEANROOM_TEST_STDOUT.log"
STDERR_LOG = EVIDENCE / "CLEANROOM_TEST_STDERR.log"
REPORT = EVIDENCE / "CLEANROOM_VALIDATION_REPORT.json"
SELF_EXCLUDED = {"PACKAGE_MANIFEST.json", "SHA256SUMS.txt", str(REPORT.relative_to(ROOT))}
MUTABLE_DURING_VALIDATION = {
    "PACKAGE_MANIFEST.json",
    "SHA256SUMS.txt",
    str(REPORT.relative_to(ROOT)),
    str(STDOUT_LOG.relative_to(ROOT)),
    str(STDERR_LOG.relative_to(ROOT)),
}
MAX_FILES = 10_000
MAX_TOTAL_BYTES = 268_435_456
MAX_FILE_BYTES = 67_108_864
MAX_TEST_OUTPUT_BYTES = 1_048_576
FORBIDDEN_IMPORTS = {"socket", "requests", "urllib", "httpx", "ftplib", "smtplib"}
EXPECTED_SERVICE_GATES = [
    {"id": "A0", "name": "PUBLIC_SERVICE_SEPARATION", "status": "PASS_POLICY_ONLY__RUNTIME_UNATTESTED"},
    {"id": "A1", "name": "IDENTITY_AND_ASSERTION_VERIFIERS", "status": "FAIL_CLOSED_NOT_IMPLEMENTED"},
    {"id": "A2", "name": "HOLDER_OF_KEY_VERIFIER", "status": "FAIL_CLOSED_NOT_IMPLEMENTED"},
    {"id": "A3", "name": "SIGNED_ADMISSION_RECEIPT", "status": "FAIL_CLOSED_NOT_IMPLEMENTED"},
    {"id": "A4", "name": "FOUR_EYES_AND_CONFLICT_GOVERNANCE", "status": "FAIL_CLOSED_SOP_UNATTESTED"},
    {"id": "A5", "name": "PROJECT_DUAL_USE_AND_CHANGE_CONTROL", "status": "FAIL_CLOSED_NOT_IMPLEMENTED"},
    {"id": "A6", "name": "SENDER_CONSTRAINED_CAPABILITY_ISSUER", "status": "FAIL_CLOSED_NOT_IMPLEMENTED"},
    {"id": "A7", "name": "GATEWAY_SECRET_AND_COST_CONTROL", "status": "FAIL_CLOSED_NOT_IMPLEMENTED"},
    {"id": "A8", "name": "TENANT_RUNTIME_DATA_AND_EGRESS_CONTROL", "status": "FAIL_CLOSED_NOT_IMPLEMENTED"},
    {"id": "A9", "name": "ATOMIC_BUDGET_AND_SYBIL_CONTROL", "status": "FAIL_CLOSED_NOT_IMPLEMENTED"},
    {"id": "A10", "name": "ONLINE_REVOCATION_AND_EMERGENCY_HOLD", "status": "FAIL_CLOSED_NOT_IMPLEMENTED"},
    {"id": "A11", "name": "PRIVACY_AND_RETENTION", "status": "FAIL_CLOSED_LEGAL_AND_RUNTIME_REVIEW_PENDING"},
    {"id": "A12", "name": "AUDIT_LOG_PRIVACY", "status": "FAIL_CLOSED_NOT_IMPLEMENTED"},
    {"id": "A13", "name": "FAIR_APPEAL_AND_INDEPENDENT_RESEARCHER_PATH", "status": "FAIL_CLOSED_SOP_UNATTESTED"},
    {"id": "A14", "name": "INDEPENDENT_ABUSE_PRIVACY_TEST_AND_BOUNDED_PILOT", "status": "FAIL_CLOSED_NOT_EXECUTED"},
]


def strict_json_loads(text: str, label: str):
    def reject_duplicates(pairs):
        value = {}
        for key, item in pairs:
            if key in value:
                raise RuntimeError(f"FAIL_CLOSED_DUPLICATE_JSON_KEY:{label}:{key}")
            value[key] = item
        return value

    try:
        return json.loads(text, object_pairs_hook=reject_duplicates)
    except RuntimeError:
        raise
    except json.JSONDecodeError as exc:
        raise RuntimeError(f"FAIL_CLOSED_JSON_PARSE:{label}") from exc


def atomic_write(path: Path, body: bytes) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    fd, name = tempfile.mkstemp(prefix=f".{path.name}.", dir=path.parent)
    try:
        with os.fdopen(fd, "wb") as handle:
            handle.write(body)
            handle.flush()
            os.fsync(handle.fileno())
        os.replace(name, path)
        directory_fd = os.open(path.parent, os.O_RDONLY | getattr(os, "O_DIRECTORY", 0))
        try:
            os.fsync(directory_fd)
        finally:
            os.close(directory_fd)
    finally:
        try:
            os.unlink(name)
        except FileNotFoundError:
            pass


def inventory() -> list[Path]:
    files: list[Path] = []
    total = 0
    for path in sorted(ROOT.rglob("*")):
        relative = path.relative_to(ROOT).as_posix()
        info = path.lstat()
        if stat.S_ISLNK(info.st_mode):
            raise RuntimeError(f"FAIL_CLOSED_SYMLINK:{relative}")
        if stat.S_ISDIR(info.st_mode):
            if path.name in {".git", "__pycache__"}:
                raise RuntimeError(f"FAIL_CLOSED_TRANSIENT_DIRECTORY:{relative}")
            continue
        if not stat.S_ISREG(info.st_mode):
            raise RuntimeError(f"FAIL_CLOSED_SPECIAL_FILE:{relative}")
        if path.name == ".DS_Store" or path.suffix in {".pyc", ".pyo"}:
            raise RuntimeError(f"FAIL_CLOSED_TRANSIENT_FILE:{relative}")
        if info.st_size > MAX_FILE_BYTES:
            raise RuntimeError(f"FAIL_CLOSED_FILE_LIMIT:{relative}")
        files.append(path)
        total += info.st_size
        if len(files) > MAX_FILES or total > MAX_TOTAL_BYTES:
            raise RuntimeError("FAIL_CLOSED_PACKAGE_LIMIT")
    return files


def protected_snapshot(files: list[Path]) -> dict:
    entries = []
    for path in files:
        relative = path.relative_to(ROOT).as_posix()
        if relative in MUTABLE_DURING_VALIDATION:
            continue
        fd = os.open(path, os.O_RDONLY | getattr(os, "O_NOFOLLOW", 0) | getattr(os, "O_NONBLOCK", 0))
        try:
            before = os.fstat(fd)
            digest = hashlib.sha256()
            measured = 0
            while True:
                chunk = os.read(fd, min(1024 * 1024, MAX_FILE_BYTES + 1 - measured))
                if not chunk:
                    break
                measured += len(chunk)
                if measured > MAX_FILE_BYTES:
                    raise RuntimeError(f"FAIL_CLOSED_FILE_LIMIT:{relative}")
                digest.update(chunk)
            after = os.fstat(fd)
        finally:
            os.close(fd)
        identity_before = (before.st_dev, before.st_ino, before.st_mode, before.st_size, before.st_mtime_ns, before.st_ctime_ns)
        identity_after = (after.st_dev, after.st_ino, after.st_mode, after.st_size, after.st_mtime_ns, after.st_ctime_ns)
        if identity_before != identity_after or measured != before.st_size:
            raise RuntimeError(f"FAIL_CLOSED_FILE_CHANGED_DURING_READ:{relative}")
        entries.append({"path": relative, "bytes": measured, "sha256": digest.hexdigest()})
    entries.sort(key=lambda entry: entry["path"])
    accumulator = hashlib.sha256(b"LIMEX_SCIENCE_VALIDATED_INPUT_TREE_V1\x00")
    for entry in entries:
        encoded = entry["path"].encode("utf-8")
        accumulator.update(len(encoded).to_bytes(8, "big"))
        accumulator.update(encoded)
        accumulator.update(entry["bytes"].to_bytes(8, "big"))
        accumulator.update(bytes.fromhex(entry["sha256"]))
    return {"entries": entries, "root_sha256": accumulator.hexdigest()}


def scan_sensitive(files: list[Path]) -> None:
    mac_root = "/" + "Users" + "/"
    win_root = "C:" + "\\"
    private_key_marker = "BEGIN " + "PRIVATE KEY"
    patterns = {
        "ABSOLUTE_MAC_USER_PATH": re.compile(re.escape(mac_root)),
        "ABSOLUTE_WINDOWS_PATH": re.compile(re.escape(win_root), re.IGNORECASE),
        "EMAIL_ADDRESS": re.compile(r"\b[A-Z0-9._%+-]+@[A-Z0-9.-]+\.[A-Z]{2,}\b", re.IGNORECASE),
        "PRIVATE_KEY_MATERIAL": re.compile(private_key_marker),
        "LOOPBACK_OR_REMOTE_ENDPOINT": re.compile(r"\b(?:https?|ssh)://(?:127\.0\.0\.1|localhost|\d{1,3}(?:\.\d{1,3}){3})(?::\d+)?", re.IGNORECASE),
    }
    for path in files:
        relative = path.relative_to(ROOT).as_posix()
        if relative in {"PACKAGE_MANIFEST.json", "SHA256SUMS.txt"}:
            continue
        body = path.read_bytes()
        try:
            text = body.decode("utf-8")
        except UnicodeDecodeError as exc:
            raise RuntimeError(f"FAIL_CLOSED_NON_UTF8:{relative}") from exc
        for label, pattern in patterns.items():
            if pattern.search(text):
                raise RuntimeError(f"FAIL_CLOSED_{label}:{relative}")


def parse_sources(files: list[Path]) -> None:
    for path in files:
        if path.suffix == ".json" and path.name not in {"PACKAGE_MANIFEST.json"}:
            try:
                strict_json_loads(path.read_text(encoding="utf-8"), path.relative_to(ROOT).as_posix())
            except RuntimeError as exc:
                raise RuntimeError(f"FAIL_CLOSED_JSON_PARSE:{path.relative_to(ROOT)}") from exc
        if path.suffix != ".py":
            continue
        tree = ast.parse(path.read_text(encoding="utf-8"), filename=str(path.relative_to(ROOT)))
        for node in ast.walk(tree):
            module = None
            if isinstance(node, ast.Import):
                for alias in node.names:
                    if alias.name.split(".")[0] in FORBIDDEN_IMPORTS:
                        raise RuntimeError(f"FAIL_CLOSED_NETWORK_IMPORT:{path.relative_to(ROOT)}:{alias.name}")
            elif isinstance(node, ast.ImportFrom):
                module = (node.module or "").split(".")[0]
                if module in FORBIDDEN_IMPORTS:
                    raise RuntimeError(f"FAIL_CLOSED_NETWORK_IMPORT:{path.relative_to(ROOT)}:{module}")


def policy_gate() -> None:
    gate = strict_json_loads((ROOT / "PUBLIC_RELEASE_GATE.json").read_text(encoding="utf-8"), "PUBLIC_RELEASE_GATE.json")
    if gate != {
        "schema": "limex-science-public-release-gate-v1",
        "publication_status": "BLOCKED__PENDING_POST_FREEZE_AUDIT_AND_DIGEST_CONFIRMATION",
        "external_effect": "DENY",
        "repository_target": "https://github.com/tobias-sproete-ai/limex",
        "sponsored_compute_status": "NOT_IMPLEMENTED__NO_ACCESS_GRANTS",
        "research_payload_status": "BOUND_EXTERNAL_REPOSITORY_TAG__GOLDBACH_V1_8_767__NO_PROOF",
        "release_terms_status": "OWNER_APPROVED__ALL_RIGHTS_RESERVED__NOT_OPEN_SOURCE",
        "privacy_status": "OWNER_APPROVED_PUBLIC_ARTIFACT_BOUNDARY__NO_APPLICANT_DATA__NO_LIVE_SERVICE",
        "closed_prerequisites": [
            "LEGAL_AND_LICENCE_OWNER_DECISION_FOR_EXACT_RELEASE_CLASS",
            "PRIVACY_BOUNDARY_FOR_PUBLIC_ARTIFACT",
            "RESEARCH_PAYLOAD_BUILD_AND_AXIOM_RECEIPTS",
            "BOUND_REPOSITORY_TARGET",
        ],
        "required_before_successor_release": [
            "POST_FREEZE_INDEPENDENT_SECURITY_REVIEW",
            "DIGEST_BOUND_EXECUTIVE_RELEASE_AUTHORITY",
        ],
    }:
        raise RuntimeError("FAIL_CLOSED_PUBLIC_RELEASE_GATE")
    service = strict_json_loads((ROOT / "access" / "SERVICE_GATES.json").read_text(encoding="utf-8"), "access/SERVICE_GATES.json")
    expected_service = {
        "schema": "limex-science-sponsored-compute-service-gates-v1",
        "status": "ALL_LIVE_SERVICE_GATES_FAIL_CLOSED",
        "gates": EXPECTED_SERVICE_GATES,
        "compute_dispatch": "DENY",
        "capability_issuance": "DENY",
        "live_user_accreditation": "DENY",
    }
    if service != expected_service:
        raise RuntimeError("FAIL_CLOSED_SERVICE_GATE_CLOSED_SCHEMA")


def run_tests() -> dict:
    if platform.system() != "Darwin" or not Path("/usr/bin/sandbox-exec").is_file():
        raise RuntimeError("FAIL_CLOSED_NETWORK_SANDBOX_UNAVAILABLE")
    profile = "(version 1) (deny default) (allow process*) (allow file-read*) (allow sysctl-read) (allow mach-lookup) (allow file-write* (subpath \"/tmp\")) (allow file-write* (subpath \"/private/tmp\")) (deny network*)"
    command = [
        "/usr/bin/sandbox-exec", "-p", profile,
        sys.executable, "-m", "unittest", "discover", "-s", str(ROOT / "tests"), "-v",
    ]
    result = subprocess.run(
        command,
        cwd=ROOT,
        env={"PATH": "/usr/bin:/bin", "PYTHONDONTWRITEBYTECODE": "1", "LC_ALL": "C", "TMPDIR": "/tmp"},
        capture_output=True,
        timeout=120,
        check=False,
    )
    if len(result.stdout) > MAX_TEST_OUTPUT_BYTES or len(result.stderr) > MAX_TEST_OUTPUT_BYTES:
        raise RuntimeError("FAIL_CLOSED_TEST_OUTPUT_LIMIT")
    atomic_write(STDOUT_LOG, result.stdout)
    atomic_write(STDERR_LOG, result.stderr)
    combined = (result.stdout + result.stderr).decode("utf-8", errors="replace")
    match = re.search(r"Ran (\d+) tests?", combined)
    count = int(match.group(1)) if match else None
    if result.returncode != 0 or count != 49 or "OK" not in combined:
        raise RuntimeError(f"FAIL_CLOSED_TEST_RUN:exit={result.returncode}:count={count}")
    return {
        "exit_code": result.returncode,
        "test_count": count,
        "stdout_sha256": hashlib.sha256(result.stdout).hexdigest(),
        "stderr_sha256": hashlib.sha256(result.stderr).hexdigest(),
        "network_profile": "MACOS_SANDBOX_DENY_NETWORK",
    }


def main() -> int:
    if (ROOT / "PACKAGE_MANIFEST.json").exists() or (ROOT / "SHA256SUMS.txt").exists():
        print(json.dumps({
            "status": "FAIL_CLOSED_FROZEN_PACKAGE_REQUIRES_SUCCESSOR",
            "scope": "NO_MUTATION_OF_FROZEN_CANDIDATE",
        }, sort_keys=True), file=sys.stderr)
        return 1
    report: dict = {
        "schema": "limex-science-cleanroom-validation-report-v1",
        "status": "FAIL_CLOSED_VALIDATION_INCOMPLETE",
        "scope": "LOCAL_CANDIDATE_ONLY__NO_ACCREDITATION_OR_RELEASE_AUTHORITY",
    }
    try:
        before = inventory()
        before_snapshot = protected_snapshot(before)
        parse_sources(before)
        policy_gate()
        test = run_tests()
        after = inventory()
        after_snapshot = protected_snapshot(after)
        if after_snapshot != before_snapshot:
            raise RuntimeError("FAIL_CLOSED_TESTED_TREE_MUTATED")
        parse_sources(after)
        policy_gate()
        scan_sensitive(after)
        report.update({
            "status": "PASS_WITH_DECLARED_LIMITS",
            "regular_file_count_before_manifest": len(after),
            "test": test,
            "validated_input_regular_file_count": len(after_snapshot["entries"]),
            "validated_input_tree_root_sha256": after_snapshot["root_sha256"],
            "assertions": [
                "CLOSED_SCHEMA_STRUCTURAL_DECIDER",
                "STRONGEST_DECISION_REMAINS_EXTERNAL_VERIFICATION_HOLD",
                "NO_ACCESS_GRANT_OR_COMPUTE_EFFECT",
                "PUBLIC_RELEASE_GATE_BLOCKED",
                "SERVICE_GATES_FAIL_CLOSED",
                "BOUND_PRIVATE_IDENTIFIER_CLASSES_NOT_DETECTED",
            ],
            "nonclaims": [
                "NO_REAL_PERSON_ACCREDITED",
                "NO_EXTERNAL_SIGNATURE_OR_TRUST_CHAIN_VERIFIED",
                "NO_CAPABILITY_ISSUED",
                "NO_COMPUTE_DISPATCHED",
                "NO_PUBLIC_RELEASE_AUTHORIZED",
                "NO_ABSOLUTE_ABUSE_PREVENTION",
            ],
        })
        atomic_write(REPORT, (json.dumps(report, indent=2, sort_keys=True) + "\n").encode("utf-8"))
        print(json.dumps(report, sort_keys=True))
        return 0
    except Exception as exc:
        report["error"] = f"{type(exc).__name__}:{exc}"
        atomic_write(REPORT, (json.dumps(report, indent=2, sort_keys=True) + "\n").encode("utf-8"))
        print(json.dumps(report, sort_keys=True), file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
