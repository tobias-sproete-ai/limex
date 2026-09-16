"""Non-mutating verifier for the frozen cleanroom package."""
from __future__ import annotations

import hashlib
import json
import os
import re
import stat
from pathlib import Path


ROOT = Path(__file__).resolve().parent.parent
MANIFEST = ROOT / "PACKAGE_MANIFEST.json"
CHECKSUMS = ROOT / "SHA256SUMS.txt"
EXCLUDED = {MANIFEST.name, CHECKSUMS.name}
MAX_PACKAGE_FILES = 10_000
MAX_PACKAGE_BYTES = 268_435_456
MAX_FILE_BYTES = 67_108_864
MANIFEST_KEYS = {
    "schema", "release", "hash_algorithm", "self_exclusion",
    "regular_file_count", "total_bytes", "package_root_sha256",
    "validated_input_tree_root_sha256", "validated_input_regular_file_count",
    "validation_report_sha256", "test_stdout_sha256", "test_stderr_sha256",
    "entries",
}
VALIDATION_REPORT = "evidence/CLEANROOM_VALIDATION_REPORT.json"
TEST_STDOUT = "evidence/CLEANROOM_TEST_STDOUT.log"
TEST_STDERR = "evidence/CLEANROOM_TEST_STDERR.log"
VALIDATION_MUTABLE = {
    MANIFEST.name, CHECKSUMS.name, VALIDATION_REPORT, TEST_STDOUT, TEST_STDERR,
}
EXPECTED_PUBLIC_GATE = {
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
}
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
                raise SystemExit(f"FAIL_CLOSED_DUPLICATE_JSON_KEY:{label}:{key}")
            value[key] = item
        return value

    try:
        return json.loads(text, object_pairs_hook=reject_duplicates)
    except SystemExit:
        raise
    except json.JSONDecodeError as exc:
        raise SystemExit(f"FAIL_CLOSED_JSON_PARSE:{label}") from exc


def bounded_read(path: Path) -> bytes:
    before = path.lstat()
    if not stat.S_ISREG(before.st_mode) or before.st_size > MAX_FILE_BYTES:
        raise SystemExit(f"FAIL_CLOSED_BOUND_FILE:{path.name}")
    body = path.read_bytes()
    after = path.lstat()
    before_identity = (before.st_dev, before.st_ino, before.st_mode, before.st_size, before.st_mtime_ns, before.st_ctime_ns)
    after_identity = (after.st_dev, after.st_ino, after.st_mode, after.st_size, after.st_mtime_ns, after.st_ctime_ns)
    if before_identity != after_identity or len(body) != before.st_size:
        raise SystemExit(f"FAIL_CLOSED_FILE_CHANGED_DURING_READ:{path.name}")
    return body


def collect() -> list[dict]:
    entries = []
    total_bytes = 0

    def directory_identity(info):
        return (info.st_dev, info.st_ino, info.st_mode, info.st_mtime_ns, info.st_ctime_ns)

    def visit(directory_fd: int, prefix: str) -> None:
        nonlocal total_bytes
        before_directory = os.fstat(directory_fd)
        names = sorted(os.listdir(directory_fd))
        for name in names:
            relative = f"{prefix}/{name}" if prefix else name
            info = os.stat(name, dir_fd=directory_fd, follow_symlinks=False)
            if stat.S_ISLNK(info.st_mode):
                raise SystemExit(f"FAIL_CLOSED_SYMLINK_ENTRY:{relative}")
            if stat.S_ISDIR(info.st_mode):
                if name in {".git", "__pycache__"}:
                    raise SystemExit(f"FAIL_CLOSED_TRANSIENT_DIRECTORY:{relative}")
                child_fd = os.open(
                    name,
                    os.O_RDONLY | getattr(os, "O_DIRECTORY", 0) | getattr(os, "O_NOFOLLOW", 0),
                    dir_fd=directory_fd,
                )
                try:
                    visit(child_fd, relative)
                finally:
                    os.close(child_fd)
                continue
            if not stat.S_ISREG(info.st_mode):
                raise SystemExit(f"FAIL_CLOSED_SPECIAL_FILE:{relative}")
            if relative in EXCLUDED:
                continue
            if name == ".DS_Store" or name.endswith((".pyc", ".pyo")):
                raise SystemExit(f"FAIL_CLOSED_TRANSIENT_FILE:{relative}")
            if info.st_size > MAX_FILE_BYTES:
                raise SystemExit(f"FAIL_CLOSED_FILE_BYTE_BOUND:{relative}")
            file_fd = os.open(
                name,
                os.O_RDONLY | getattr(os, "O_NOFOLLOW", 0) | getattr(os, "O_NONBLOCK", 0),
                dir_fd=directory_fd,
            )
            try:
                before_file = os.fstat(file_fd)
                hasher = hashlib.sha256()
                measured = 0
                while True:
                    chunk = os.read(file_fd, min(1024 * 1024, MAX_FILE_BYTES + 1 - measured))
                    if not chunk:
                        break
                    measured += len(chunk)
                    if measured > MAX_FILE_BYTES:
                        raise SystemExit(f"FAIL_CLOSED_FILE_BYTE_BOUND:{relative}")
                    hasher.update(chunk)
                after_file = os.fstat(file_fd)
            finally:
                os.close(file_fd)
            before_identity = (before_file.st_dev, before_file.st_ino, before_file.st_mode, before_file.st_size, before_file.st_mtime_ns, before_file.st_ctime_ns)
            after_identity = (after_file.st_dev, after_file.st_ino, after_file.st_mode, after_file.st_size, after_file.st_mtime_ns, after_file.st_ctime_ns)
            if before_identity != after_identity or measured != before_file.st_size:
                raise SystemExit(f"FAIL_CLOSED_FILE_CHANGED_DURING_READ:{relative}")
            total_bytes += measured
            if len(entries) + 1 > MAX_PACKAGE_FILES or total_bytes > MAX_PACKAGE_BYTES:
                raise SystemExit("FAIL_CLOSED_PACKAGE_RESOURCE_BOUND")
            entries.append({"path": relative, "bytes": measured, "sha256": hasher.hexdigest()})
        if names != sorted(os.listdir(directory_fd)) or directory_identity(before_directory) != directory_identity(os.fstat(directory_fd)):
            raise SystemExit(f"FAIL_CLOSED_DIRECTORY_CHANGED_DURING_SNAPSHOT:{prefix or '.'}")

    root_fd = os.open(
        ROOT,
        os.O_RDONLY | getattr(os, "O_DIRECTORY", 0) | getattr(os, "O_NOFOLLOW", 0),
    )
    try:
        visit(root_fd, "")
    finally:
        os.close(root_fd)
    return sorted(entries, key=lambda entry: entry["path"])


def root_digest(entries: list[dict]) -> str:
    accumulator = hashlib.sha256(b"LIMEX_SCIENCE_CLEANROOM_PACKAGE_MANIFEST_V1\x00")
    for entry in entries:
        relative = entry["path"].encode("utf-8")
        accumulator.update(len(relative).to_bytes(8, "big"))
        accumulator.update(relative)
        accumulator.update(entry["bytes"].to_bytes(8, "big"))
        accumulator.update(bytes.fromhex(entry["sha256"]))
    return accumulator.hexdigest()


def validated_input_digest(entries: list[dict]) -> tuple[str, int]:
    protected = [entry for entry in entries if entry["path"] not in VALIDATION_MUTABLE]
    accumulator = hashlib.sha256(b"LIMEX_SCIENCE_VALIDATED_INPUT_TREE_V1\x00")
    for entry in protected:
        relative = entry["path"].encode("utf-8")
        accumulator.update(len(relative).to_bytes(8, "big"))
        accumulator.update(relative)
        accumulator.update(entry["bytes"].to_bytes(8, "big"))
        accumulator.update(bytes.fromhex(entry["sha256"]))
    return accumulator.hexdigest(), len(protected)


def validate_report(report: object, entry_map: dict[str, dict], document: dict, entries: list[dict]) -> tuple[str, int]:
    expected_report_keys = {
        "schema", "status", "scope", "regular_file_count_before_manifest",
        "test", "validated_input_regular_file_count",
        "validated_input_tree_root_sha256", "assertions", "nonclaims",
    }
    if type(report) is not dict or set(report) != expected_report_keys:
        raise SystemExit("FAIL_CLOSED_VALIDATION_REPORT_CLOSED_SCHEMA")
    if report.get("schema") != "limex-science-cleanroom-validation-report-v1":
        raise SystemExit("FAIL_CLOSED_VALIDATION_REPORT_SCHEMA")
    if report.get("status") != "PASS_WITH_DECLARED_LIMITS":
        raise SystemExit("FAIL_CLOSED_VALIDATION_STATUS")
    if report.get("scope") != "LOCAL_CANDIDATE_ONLY__NO_ACCREDITATION_OR_RELEASE_AUTHORITY":
        raise SystemExit("FAIL_CLOSED_VALIDATION_SCOPE")
    if report.get("assertions") != [
        "CLOSED_SCHEMA_STRUCTURAL_DECIDER",
        "STRONGEST_DECISION_REMAINS_EXTERNAL_VERIFICATION_HOLD",
        "NO_ACCESS_GRANT_OR_COMPUTE_EFFECT",
        "PUBLIC_RELEASE_GATE_BLOCKED",
        "SERVICE_GATES_FAIL_CLOSED",
        "BOUND_PRIVATE_IDENTIFIER_CLASSES_NOT_DETECTED",
    ]:
        raise SystemExit("FAIL_CLOSED_VALIDATION_ASSERTIONS")
    if report.get("nonclaims") != [
        "NO_REAL_PERSON_ACCREDITED",
        "NO_EXTERNAL_SIGNATURE_OR_TRUST_CHAIN_VERIFIED",
        "NO_CAPABILITY_ISSUED",
        "NO_COMPUTE_DISPATCHED",
        "NO_PUBLIC_RELEASE_AUTHORIZED",
        "NO_ABSOLUTE_ABUSE_PREVENTION",
    ]:
        raise SystemExit("FAIL_CLOSED_VALIDATION_NONCLAIMS")
    test = report.get("test")
    if type(test) is not dict or set(test) != {
        "exit_code", "test_count", "stdout_sha256", "stderr_sha256", "network_profile",
    }:
        raise SystemExit("FAIL_CLOSED_VALIDATION_TEST_CLOSED_SCHEMA")
    if test.get("exit_code") != 0 or test.get("test_count") != 49 or test.get("network_profile") != "MACOS_SANDBOX_DENY_NETWORK":
        raise SystemExit("FAIL_CLOSED_VALIDATION_TEST_ATTESTATION")
    if test.get("stdout_sha256") != entry_map[TEST_STDOUT]["sha256"] or document.get("test_stdout_sha256") != entry_map[TEST_STDOUT]["sha256"]:
        raise SystemExit("FAIL_CLOSED_VALIDATION_STDOUT_HASH")
    if test.get("stderr_sha256") != entry_map[TEST_STDERR]["sha256"] or document.get("test_stderr_sha256") != entry_map[TEST_STDERR]["sha256"]:
        raise SystemExit("FAIL_CLOSED_VALIDATION_STDERR_HASH")
    if document.get("validation_report_sha256") != entry_map[VALIDATION_REPORT]["sha256"]:
        raise SystemExit("FAIL_CLOSED_VALIDATION_REPORT_HASH")
    observed_root, observed_count = validated_input_digest(entries)
    if report.get("validated_input_tree_root_sha256") != observed_root or document.get("validated_input_tree_root_sha256") != observed_root:
        raise SystemExit("FAIL_CLOSED_VALIDATED_INPUT_ROOT")
    if report.get("validated_input_regular_file_count") != observed_count or document.get("validated_input_regular_file_count") != observed_count:
        raise SystemExit("FAIL_CLOSED_VALIDATED_INPUT_COUNT")
    if report.get("regular_file_count_before_manifest") != observed_count + 3:
        raise SystemExit("FAIL_CLOSED_VALIDATION_INVENTORY_COUNT")
    return observed_root, observed_count


def main() -> int:
    document = strict_json_loads(bounded_read(MANIFEST).decode("utf-8"), "PACKAGE_MANIFEST.json")
    entries = collect()
    if type(document) is not dict or set(document) != MANIFEST_KEYS:
        raise SystemExit("FAIL_CLOSED_MANIFEST_CLOSED_SCHEMA")
    if document.get("schema") != "LIMEX_SCIENCE_CLEANROOM_PACKAGE_MANIFEST_V1":
        raise SystemExit("FAIL_CLOSED_MANIFEST_SCHEMA")
    if document.get("release") != "LIMEX_SCIENCE_CLEANROOM_V1_0_RC4":
        raise SystemExit("FAIL_CLOSED_MANIFEST_RELEASE")
    if document.get("hash_algorithm") != "SHA-256":
        raise SystemExit("FAIL_CLOSED_MANIFEST_HASH_ALGORITHM")
    if document.get("self_exclusion") != ["PACKAGE_MANIFEST.json", "SHA256SUMS.txt"]:
        raise SystemExit("FAIL_CLOSED_MANIFEST_SELF_EXCLUSION")
    if document.get("entries") != entries:
        raise SystemExit("FAIL_CLOSED_MANIFEST_ENTRY_MISMATCH")
    if document.get("regular_file_count") != len(entries):
        raise SystemExit("FAIL_CLOSED_MANIFEST_COUNT_MISMATCH")
    if document.get("total_bytes") != sum(entry["bytes"] for entry in entries):
        raise SystemExit("FAIL_CLOSED_MANIFEST_BYTE_MISMATCH")
    observed_root = root_digest(entries)
    if document.get("package_root_sha256") != observed_root:
        raise SystemExit("FAIL_CLOSED_PACKAGE_ROOT_MISMATCH")
    expected_lines = "".join(f"{entry['sha256']}  {entry['path']}\n" for entry in entries)
    if bounded_read(CHECKSUMS).decode("utf-8") != expected_lines:
        raise SystemExit("FAIL_CLOSED_CHECKSUM_LIST_MISMATCH")
    entry_map = {entry["path"]: entry for entry in entries}
    for required in (VALIDATION_REPORT, TEST_STDOUT, TEST_STDERR):
        if required not in entry_map:
            raise SystemExit("FAIL_CLOSED_VALIDATION_EVIDENCE_MISSING")
    report = strict_json_loads((ROOT / VALIDATION_REPORT).read_text(encoding="utf-8"), VALIDATION_REPORT)
    observed_validated_root, observed_validated_count = validate_report(report, entry_map, document, entries)
    gate = strict_json_loads((ROOT / "PUBLIC_RELEASE_GATE.json").read_text(encoding="utf-8"), "PUBLIC_RELEASE_GATE.json")
    if gate != EXPECTED_PUBLIC_GATE:
        raise SystemExit("FAIL_CLOSED_PUBLIC_RELEASE_GATE")
    service = strict_json_loads((ROOT / "access" / "SERVICE_GATES.json").read_text(encoding="utf-8"), "access/SERVICE_GATES.json")
    if service != {
        "schema": "limex-science-sponsored-compute-service-gates-v1",
        "status": "ALL_LIVE_SERVICE_GATES_FAIL_CLOSED",
        "gates": EXPECTED_SERVICE_GATES,
        "compute_dispatch": "DENY",
        "capability_issuance": "DENY",
        "live_user_accreditation": "DENY",
    }:
        raise SystemExit("FAIL_CLOSED_SERVICE_GATE_CLOSED_SCHEMA")
    for digest_value in (
        document.get("package_root_sha256"),
        document.get("validated_input_tree_root_sha256"),
        document.get("validation_report_sha256"),
        document.get("test_stdout_sha256"),
        document.get("test_stderr_sha256"),
    ):
        if not re.fullmatch(r"[0-9a-f]{64}", digest_value or ""):
            raise SystemExit("FAIL_CLOSED_DIGEST_FORMAT")
    print(json.dumps({
        "status": "PASS_FROZEN_PACKAGE_IDENTITY_WITH_PUBLICATION_BLOCKED",
        "regular_file_count": len(entries),
        "total_bytes": sum(entry["bytes"] for entry in entries),
        "package_root_sha256": observed_root,
        "validated_input_tree_root_sha256": observed_validated_root,
        "publication_status": gate["publication_status"],
    }, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
