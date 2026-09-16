"""Fail-closed local validator for the LIMEX Settle cleanroom candidate."""
from __future__ import annotations

import ast
import hashlib
import json
import os
import re
import resource
import secrets
import stat
import subprocess
import sys
import tempfile
from datetime import datetime, timezone
from pathlib import Path


ROOT = Path(__file__).resolve().parent.parent
EVIDENCE = ROOT / "evidence"
REPORT = EVIDENCE / "CLEANROOM_VALIDATION_REPORT.json"
STDOUT_LOG = EVIDENCE / "CLEANROOM_TEST_STDOUT.log"
STDERR_LOG = EVIDENCE / "CLEANROOM_TEST_STDERR.log"
EXPECTED_TESTS = 107
MAX_PACKAGE_FILES = 10_000
MAX_PACKAGE_BYTES = 268_435_456
MAX_FILE_BYTES = 67_108_864
MAX_TEST_LOG_BYTES = 16_777_216
MUTABLE = {
    "PACKAGE_MANIFEST.json",
    "SHA256SUMS.txt",
    "evidence/CLEANROOM_TEST_STDOUT.log",
    "evidence/CLEANROOM_TEST_STDERR.log",
    "evidence/CLEANROOM_VALIDATION_REPORT.json",
}
PROVENANCE_PATHS = {
    "schemas/limex-llm-execution-attestation-v1.schema.json",
    "scripts/build_manifest.py",
    "scripts/validate_cleanroom_release.py",
    "scripts/verify_frozen_package.py",
    "src/release_seal.py",
    "src/settle_core.py",
    "tests/test_release_seal.py",
    "tests/test_settle_core.py",
}
FORBIDDEN_IMPORTS = {"aiohttp", "ftplib", "http", "requests", "smtplib", "socket", "urllib"}
FORBIDDEN_CALLS = {"eval", "exec"}
FORBIDDEN_TEXT = (
    "BEGIN " + "PRIVATE KEY",
    "BEGIN " + "OPENSSH PRIVATE KEY",
)

FORBIDDEN_PATTERNS = (
    re.compile(r"(?i)https?://[^\s/]*storageshare\.[a-z]{2,}"),
    re.compile(r"(?i)(?:^|[\\/])(?:home|users)[\\/][^\\/\s]+[\\/]"),
    re.compile(r"(?i)\b(?:api[_-]?key|password|passwd|secret[_-]?key)\s*[:=]\s*['\"][^'\"]{4,}"),
)


def sha256_bytes(body: bytes) -> str:
    return hashlib.sha256(body).hexdigest()


def sha256(path: Path) -> str:
    before = path.stat()
    if not stat.S_ISREG(before.st_mode) or before.st_size > 268_435_456:
        raise RuntimeError("HASH_INPUT_BYTE_BOUND_EXCEEDED")
    hasher = hashlib.sha256()
    measured = 0
    with path.open("rb") as handle:
        while True:
            chunk = handle.read(1024 * 1024)
            if not chunk:
                break
            measured += len(chunk)
            if measured > 268_435_456:
                raise RuntimeError("HASH_INPUT_BYTE_BOUND_EXCEEDED")
            hasher.update(chunk)
    after = path.stat()
    if measured != before.st_size or (before.st_dev, before.st_ino, before.st_mtime_ns, before.st_ctime_ns) != (after.st_dev, after.st_ino, after.st_mtime_ns, after.st_ctime_ns):
        raise RuntimeError("HASH_INPUT_CHANGED_DURING_READ")
    return hasher.hexdigest()


def utc_now() -> str:
    return datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%S.%f")[:-3] + "Z"


def atomic_write(path: Path, body: bytes) -> None:
    directory_fd = os.open(
        path.parent,
        os.O_RDONLY | getattr(os, "O_DIRECTORY", 0) | getattr(os, "O_NOFOLLOW", 0),
    )
    temporary_name = f".{path.name}.{os.getpid()}.{secrets.token_hex(8)}"
    descriptor = None
    try:
        descriptor = os.open(
            temporary_name,
            os.O_WRONLY | os.O_CREAT | os.O_EXCL | getattr(os, "O_NOFOLLOW", 0),
            0o600,
            dir_fd=directory_fd,
        )
        written = 0
        while written < len(body):
            written += os.write(descriptor, body[written:])
        os.fsync(descriptor)
        os.close(descriptor)
        descriptor = None
        os.replace(temporary_name, path.name, src_dir_fd=directory_fd, dst_dir_fd=directory_fd)
        os.fsync(directory_fd)
        temporary_name = ""
    finally:
        if descriptor is not None:
            os.close(descriptor)
        if temporary_name:
            try:
                os.unlink(temporary_name, dir_fd=directory_fd)
            except FileNotFoundError:
                pass
        os.close(directory_fd)


def write_report(report: dict) -> None:
    atomic_write(REPORT, (json.dumps(report, indent=2, sort_keys=True) + "\n").encode("utf-8"))


def fail(detail: str) -> int:
    report = {
        "schema": "LIMEX_SETTLE_CLEANROOM_VALIDATION_REPORT_V1",
        "status": "FAIL_CLOSED",
        "detail": detail,
        "observed_at_utc": utc_now(),
        "external_effect": "DENY",
    }
    write_report(report)
    print(json.dumps(report, sort_keys=True))
    return 1


def inventory(root: Path = ROOT) -> list[Path]:
    files = []
    pending = [root]
    total_bytes = 0
    while pending:
        directory = pending.pop()
        for path in sorted(directory.iterdir(), key=lambda item: item.name, reverse=True):
            relative = path.relative_to(root).as_posix()
            info = path.lstat()
            if stat.S_ISLNK(info.st_mode):
                raise RuntimeError(f"SYMLINK_FORBIDDEN:{relative}")
            if stat.S_ISDIR(info.st_mode):
                if path.name in {".git", "__pycache__"}:
                    raise RuntimeError(f"TRANSIENT_DIRECTORY_FORBIDDEN:{relative}")
                pending.append(path)
            elif stat.S_ISREG(info.st_mode):
                if path.name == ".DS_Store" or path.suffix in {".pyc", ".pyo"}:
                    raise RuntimeError(f"TRANSIENT_FILE_FORBIDDEN:{relative}")
                if info.st_size > MAX_FILE_BYTES:
                    raise RuntimeError(f"FILE_BYTE_BOUND_EXCEEDED:{relative}")
                total_bytes += info.st_size
                if len(files) + 1 > MAX_PACKAGE_FILES or total_bytes > MAX_PACKAGE_BYTES:
                    raise RuntimeError("PACKAGE_RESOURCE_BOUND_EXCEEDED")
                files.append(path)
            else:
                raise RuntimeError(f"SPECIAL_FILE_FORBIDDEN:{relative}")
    return sorted(files)


def bounded_read(path: Path, relative: str) -> bytes:
    before = path.lstat()
    if not stat.S_ISREG(before.st_mode) or before.st_size > MAX_FILE_BYTES:
        raise RuntimeError(f"BOUNDED_REGULAR_FILE_REQUIRED:{relative}")
    body = path.read_bytes()
    after = path.lstat()
    before_identity = (before.st_dev, before.st_ino, before.st_mode, before.st_size, before.st_mtime_ns, before.st_ctime_ns)
    after_identity = (after.st_dev, after.st_ino, after.st_mode, after.st_size, after.st_mtime_ns, after.st_ctime_ns)
    if before_identity != after_identity or len(body) != before.st_size:
        raise RuntimeError(f"FILE_CHANGED_DURING_READ:{relative}")
    return body


def tree_identity(files: list[Path]) -> dict:
    entries = []
    for path in files:
        relative = path.relative_to(ROOT).as_posix()
        if relative in MUTABLE:
            continue
        body = bounded_read(path, relative)
        entries.append((relative, len(body), sha256_bytes(body)))
    accumulator = hashlib.sha256(b"LIMEX_SETTLE_CLEANROOM_PROTECTED_TREE_V1\x00")
    for relative, size, digest_value in entries:
        encoded = relative.encode("utf-8")
        accumulator.update(len(encoded).to_bytes(8, "big"))
        accumulator.update(encoded)
        accumulator.update(size.to_bytes(8, "big"))
        accumulator.update(bytes.fromhex(digest_value))
    return {
        "regular_file_count": len(entries),
        "total_bytes": sum(size for _, size, _ in entries),
        "tree_sha256": accumulator.hexdigest(),
    }


def cleanroom_gate(files: list[Path], *, include_generated: bool = False) -> dict:
    findings = []
    scanned = 0
    for path in files:
        relative = path.relative_to(ROOT).as_posix()
        if not include_generated and relative in MUTABLE:
            continue
        try:
            body = bounded_read(path, relative).decode("utf-8")
        except UnicodeDecodeError:
            findings.append({"path": relative, "class": "NON_UTF8_FILE"})
            continue
        scanned += 1
        lowered = body.lower()
        for token in FORBIDDEN_TEXT:
            if token.lower() in lowered:
                findings.append({"path": relative, "class": "FORBIDDEN_IDENTIFIER"})
        for pattern in FORBIDDEN_PATTERNS:
            if pattern.search(body):
                findings.append({"path": relative, "class": "FORBIDDEN_METADATA_OR_SECRET_PATTERN"})
    if findings:
        raise RuntimeError(f"CLEANROOM_FINDINGS:{findings}")
    return {"utf8_files_scanned": scanned, "findings": 0}


def static_source_gate() -> dict:
    paths = sorted((ROOT / "src").glob("*.py")) + sorted((ROOT / "scripts").glob("*.py"))
    findings = []
    for path in paths:
        relative = path.relative_to(ROOT).as_posix()
        body = bounded_read(path, relative).decode("utf-8")
        tree = ast.parse(body, filename=path.name)
        compile(body, path.name, "exec", dont_inherit=True, optimize=0)
        for node in ast.walk(tree):
            imported = []
            if isinstance(node, ast.Import):
                imported = [alias.name.split(".")[0] for alias in node.names]
            elif isinstance(node, ast.ImportFrom):
                imported = [(node.module or "").split(".")[0]]
            for name in imported:
                if name in FORBIDDEN_IMPORTS:
                    findings.append([path.name, getattr(node, "lineno", 0), "NETWORK_IMPORT", name])
            if isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id in FORBIDDEN_CALLS:
                findings.append([path.name, node.lineno, "DYNAMIC_CODE", node.func.id])
    if findings:
        raise RuntimeError(f"STATIC_SOURCE_FINDINGS:{findings}")
    return {"python_files": len(paths), "forbidden_network_imports": 0, "dynamic_code_calls": 0}


def provenance_gate() -> dict:
    document = json.loads((ROOT / "CLEANROOM_PROVENANCE.json").read_text(encoding="utf-8"))
    rows = document.get("rows")
    if not isinstance(rows, list):
        raise RuntimeError("PROVENANCE_ROWS_INVALID")
    observed = [row.get("public_path") for row in rows]
    if len(observed) != len(set(observed)) or set(observed) != PROVENANCE_PATHS:
        raise RuntimeError("PROVENANCE_PATH_SET_MISMATCH")
    for row in rows:
        relative = row["public_path"]
        output = row.get("output_sha256")
        predecessor = row.get("predecessor_sha256")
        if not re.fullmatch(r"[0-9a-f]{64}", output or ""):
            raise RuntimeError(f"OUTPUT_DIGEST_INVALID:{relative}")
        if not re.fullmatch(r"[0-9a-f]{64}", predecessor or ""):
            raise RuntimeError(f"PREDECESSOR_DIGEST_INVALID:{relative}")
        if sha256(ROOT / relative) != output:
            raise RuntimeError(f"PROVENANCE_OUTPUT_MISMATCH:{relative}")
    return {"rows": len(rows), "output_hashes_verified": len(rows)}


def release_gate() -> dict:
    gate = json.loads((ROOT / "PUBLIC_RELEASE_GATE.json").read_text(encoding="utf-8"))
    expected = {
        "external_effect": "DENY",
        "publication_status": "BLOCKED__NO_PUBLIC_RELEASE_DISPATCH",
        "repository_target": None,
    }
    for key, value in expected.items():
        if gate.get(key) != value:
            raise RuntimeError(f"PUBLIC_RELEASE_GATE_OPEN_OR_BOUND:{key}")
    for key in (
        "official_filing_receipt",
        "application_identifier",
        "priority_timestamp",
        "authorized_legal_release_for_exact_bytes",
        "licence_selection",
        "hardware_bound_executive_authorization",
        "technical_release_confirmation",
        "trusted_external_package_root_anchor",
        "immutable_snapshot_or_read_only_source_attestation",
        "signed_independent_security_attestation",
    ):
        if gate.get(key) != "MISSING":
            raise RuntimeError(f"UNVERIFIED_RELEASE_EVIDENCE_PRESENT:{key}")
    return {"status": gate["publication_status"], "external_effect": gate["external_effect"]}


def security_gate(files: list[Path]) -> dict:
    status_path = EVIDENCE / "SECURITY_SCAN_STATUS.json"
    report_path = EVIDENCE / "SECURITY_SCAN_REPORT.json"
    status_relative = status_path.relative_to(ROOT).as_posix()
    report_relative = report_path.relative_to(ROOT).as_posix()
    document = json.loads(bounded_read(status_path, status_relative).decode("utf-8"))
    if document.get("status") not in {"PASS_WITH_LIMITS", "PASS_NO_REPORTABLE_FINDINGS"}:
        raise RuntimeError("SECURITY_SCAN_NOT_FINAL")
    if not re.fullmatch(r"[0-9a-f]{64}", document.get("report_sha256", "")):
        raise RuntimeError("SECURITY_REPORT_DIGEST_INVALID")
    if document.get("scope") != "FULL_CLEANROOM_CANDIDATE":
        raise RuntimeError("SECURITY_SCOPE_MISMATCH")
    if document.get("report_path") != report_relative:
        raise RuntimeError("SECURITY_REPORT_PATH_MISMATCH")
    report_body = bounded_read(report_path, report_relative)
    if sha256_bytes(report_body) != document["report_sha256"]:
        raise RuntimeError("SECURITY_REPORT_DIGEST_MISMATCH")
    report = json.loads(report_body.decode("utf-8"))
    if report.get("schema") != "LIMEX_SETTLE_CLEANROOM_SECURITY_REPORT_V1":
        raise RuntimeError("SECURITY_REPORT_SCHEMA_MISMATCH")
    if report.get("status") != document["status"] or report.get("scope") != document["scope"]:
        raise RuntimeError("SECURITY_REPORT_STATUS_OR_SCOPE_MISMATCH")
    excluded = MUTABLE | {status_relative, report_relative}
    observed_entries = []
    for path in files:
        relative = path.relative_to(ROOT).as_posix()
        if relative in excluded:
            continue
        body = bounded_read(path, relative)
        observed_entries.append({"path": relative, "bytes": len(body), "sha256": sha256_bytes(body)})
    if report.get("reviewed_entries") != observed_entries:
        raise RuntimeError("SECURITY_REVIEWED_BYTES_MISMATCH")
    return {
        "status": document["status"],
        "report_sha256": document["report_sha256"],
        "scope": document["scope"],
    }


def run_tests() -> dict:
    sandbox = Path("/usr/bin/sandbox-exec")
    if not sandbox.is_file():
        raise RuntimeError("MACOS_NETWORK_SANDBOX_UNAVAILABLE")
    command = [
        str(sandbox),
        "-p",
        "(version 1)\n(allow default)\n(deny network*)\n",
        sys.executable,
        "-B",
        "-m",
        "unittest",
        "discover",
        "-s",
        str(ROOT / "tests"),
        "-p",
        "test_*.py",
        "-v",
    ]
    environment = {
        "PATH": "/usr/bin:/bin",
        "LC_ALL": "C",
        "PYTHONDONTWRITEBYTECODE": "1",
        "PYTHONPATH": str(ROOT / "src"),
        "TMPDIR": "/tmp",
    }
    def bound_child_output() -> None:
        resource.setrlimit(resource.RLIMIT_FSIZE, (MAX_TEST_LOG_BYTES, MAX_TEST_LOG_BYTES))

    with tempfile.TemporaryFile() as stdout_file, tempfile.TemporaryFile() as stderr_file:
        result = subprocess.run(
            command,
            cwd=ROOT,
            env=environment,
            stdin=subprocess.DEVNULL,
            stdout=stdout_file,
            stderr=stderr_file,
            timeout=180,
            check=False,
            preexec_fn=bound_child_output,
        )
        for stream in (stdout_file, stderr_file):
            stream.flush()
            if os.fstat(stream.fileno()).st_size > MAX_TEST_LOG_BYTES:
                raise RuntimeError("TEST_LOG_BYTE_BOUND_EXCEEDED")
            stream.seek(0)
        stdout_body = stdout_file.read(MAX_TEST_LOG_BYTES + 1)
        stderr_body = stderr_file.read(MAX_TEST_LOG_BYTES + 1)
    if len(stdout_body) > MAX_TEST_LOG_BYTES or len(stderr_body) > MAX_TEST_LOG_BYTES:
        raise RuntimeError("TEST_LOG_BYTE_BOUND_EXCEEDED")
    atomic_write(STDOUT_LOG, stdout_body)
    atomic_write(STDERR_LOG, stderr_body)
    output_text = stdout_body.decode("utf-8") + stderr_body.decode("utf-8")
    matches = re.findall(r"^Ran (\d+) tests in [0-9.]+s$", output_text, flags=re.MULTILINE)
    observed = int(matches[0]) if len(matches) == 1 else -1
    if result.returncode != 0 or observed != EXPECTED_TESTS:
        raise RuntimeError(f"TEST_GATE_FAILED:exit={result.returncode}:observed={observed}")
    return {
        "exit_code": result.returncode,
        "tests_observed": observed,
        "stdout_sha256": sha256(STDOUT_LOG),
        "stderr_sha256": sha256(STDERR_LOG),
        "sandbox": "MACOS_SANDBOX_EXEC_DENY_NETWORK",
    }


def json_gate(files: list[Path]) -> int:
    count = 0
    for path in files:
        if path.suffix == ".json":
            relative = path.relative_to(ROOT).as_posix()
            json.loads(bounded_read(path, relative).decode("utf-8"))
            count += 1
    return count


def main() -> int:
    EVIDENCE.mkdir(exist_ok=True)
    try:
        files_before = inventory()
        before = tree_identity(files_before)
        cleanroom = cleanroom_gate(files_before)
        source = static_source_gate()
        provenance = provenance_gate()
        release = release_gate()
        security = security_gate(files_before)
        json_documents = json_gate(files_before)
        tests = run_tests()
        files_after = inventory()
        after = tree_identity(files_after)
        if before != after:
            raise RuntimeError("PROTECTED_TREE_DRIFT_DURING_VALIDATION")
    except (OSError, UnicodeError, ValueError, RuntimeError, subprocess.SubprocessError, json.JSONDecodeError) as exc:
        return fail(str(exc))
    report = {
        "schema": "LIMEX_SETTLE_CLEANROOM_VALIDATION_REPORT_V1",
        "status": "PASS_CLEANROOM_TECHNICAL_WITH_PUBLICATION_BLOCKED",
        "observed_at_utc": utc_now(),
        "python_version": sys.version.split()[0],
        "python_binary_sha256": sha256(Path(sys.executable).resolve()),
        "protected_tree_identity": after,
        "cleanroom": cleanroom,
        "static_source": source,
        "provenance": provenance,
        "release_gate": release,
        "security_scan": security,
        "json_documents_parsed": json_documents,
        "tests": tests,
        "external_effect": "DENY",
        "limits": [
            "LOCAL_MACOS_STATIC_AND_FINITE_TEST_EVIDENCE_ONLY",
            "NO_PUBLICATION_AUTHORITY",
            "NO_LEGAL_PATENTABILITY_FTO_REGULATORY_OR_SAFETY_CONCLUSION",
            "NO_PRODUCTIVE_PAYMENT_WALLET_BANK_CHAIN_OR_PROVIDER_OPERATION",
            "NO_UNIVERSAL_SECURITY_OR_CROSS_PLATFORM_CLAIM"
        ]
    }
    write_report(report)
    try:
        final_files = inventory()
        cleanroom_gate(final_files, include_generated=True)
        json_gate(final_files)
    except (OSError, UnicodeError, ValueError, RuntimeError, json.JSONDecodeError) as exc:
        return fail(f"FINAL_GENERATED_OUTPUT_GATE:{exc}")
    print(json.dumps(report, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
