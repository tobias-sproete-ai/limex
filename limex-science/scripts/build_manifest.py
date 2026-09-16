"""Build a self-excluding SHA-256 package manifest and checksum list."""
from __future__ import annotations

import hashlib
import json
import os
import stat
from pathlib import Path


ROOT = Path(__file__).resolve().parent.parent
MANIFEST = ROOT / "PACKAGE_MANIFEST.json"
CHECKSUMS = ROOT / "SHA256SUMS.txt"
EXCLUDED = {MANIFEST.name, CHECKSUMS.name}
VALIDATION_REPORT = ROOT / "evidence" / "CLEANROOM_VALIDATION_REPORT.json"
TEST_STDOUT = ROOT / "evidence" / "CLEANROOM_TEST_STDOUT.log"
TEST_STDERR = ROOT / "evidence" / "CLEANROOM_TEST_STDERR.log"
VALIDATION_MUTABLE = {
    MANIFEST.name,
    CHECKSUMS.name,
    VALIDATION_REPORT.relative_to(ROOT).as_posix(),
    TEST_STDOUT.relative_to(ROOT).as_posix(),
    TEST_STDERR.relative_to(ROOT).as_posix(),
}
MAX_PACKAGE_FILES = 10_000
MAX_PACKAGE_BYTES = 268_435_456
MAX_FILE_BYTES = 67_108_864


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


def exclusive_create(path: Path, body: bytes) -> None:
    """Durably create one output without ever replacing an existing name."""
    directory_fd = os.open(
        path.parent,
        os.O_RDONLY | getattr(os, "O_DIRECTORY", 0) | getattr(os, "O_NOFOLLOW", 0),
    )
    descriptor = None
    try:
        try:
            descriptor = os.open(
                path.name,
                os.O_WRONLY | os.O_CREAT | os.O_EXCL | getattr(os, "O_NOFOLLOW", 0),
                0o600,
                dir_fd=directory_fd,
            )
        except FileExistsError as exc:
            raise SystemExit("FAIL_CLOSED_ALREADY_FROZEN__CREATE_SUCCESSOR") from exc
        written = 0
        while written < len(body):
            written += os.write(descriptor, body[written:])
        os.fsync(descriptor)
        os.close(descriptor)
        descriptor = None
        os.fsync(directory_fd)
    finally:
        if descriptor is not None:
            os.close(descriptor)
        os.close(directory_fd)


def collect_entries(root: Path, excluded: set[str] | None = None) -> list[dict]:
    """Snapshot the tree through retained no-follow directory descriptors."""
    excluded = excluded or set()
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
                if name == "__pycache__" or name.startswith(("science-admission-", "limex-science-")):
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
                raise SystemExit(f"FAIL_CLOSED_NON_REGULAR_ENTRY:{relative}")
            if relative in excluded:
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
        root,
        os.O_RDONLY | getattr(os, "O_DIRECTORY", 0) | getattr(os, "O_NOFOLLOW", 0),
    )
    try:
        visit(root_fd, "")
    finally:
        os.close(root_fd)
    entries.sort(key=lambda entry: entry["path"])
    return entries


def validated_input_root(entries: list[dict]) -> tuple[str, int]:
    protected = [entry for entry in entries if entry["path"] not in VALIDATION_MUTABLE]
    accumulator = hashlib.sha256(b"LIMEX_SCIENCE_VALIDATED_INPUT_TREE_V1\x00")
    for entry in protected:
        relative = entry["path"].encode("utf-8")
        accumulator.update(len(relative).to_bytes(8, "big"))
        accumulator.update(relative)
        accumulator.update(entry["bytes"].to_bytes(8, "big"))
        accumulator.update(bytes.fromhex(entry["sha256"]))
    return accumulator.hexdigest(), len(protected)


def require_validation_evidence(entries: list[dict]) -> dict:
    entry_map = {entry["path"]: entry for entry in entries}
    required = [
        VALIDATION_REPORT.relative_to(ROOT).as_posix(),
        TEST_STDOUT.relative_to(ROOT).as_posix(),
        TEST_STDERR.relative_to(ROOT).as_posix(),
    ]
    if any(relative not in entry_map for relative in required):
        raise SystemExit("FAIL_CLOSED_VALIDATION_EVIDENCE_MISSING")
    try:
        report = strict_json_loads(VALIDATION_REPORT.read_text(encoding="utf-8"), "evidence/CLEANROOM_VALIDATION_REPORT.json")
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise SystemExit("FAIL_CLOSED_VALIDATION_REPORT_PARSE") from exc
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
    if test.get("stdout_sha256") != entry_map[required[1]]["sha256"]:
        raise SystemExit("FAIL_CLOSED_VALIDATION_STDOUT_HASH")
    if test.get("stderr_sha256") != entry_map[required[2]]["sha256"]:
        raise SystemExit("FAIL_CLOSED_VALIDATION_STDERR_HASH")
    observed_root, observed_count = validated_input_root(entries)
    if report.get("validated_input_tree_root_sha256") != observed_root:
        raise SystemExit("FAIL_CLOSED_VALIDATED_INPUT_ROOT")
    if report.get("validated_input_regular_file_count") != observed_count:
        raise SystemExit("FAIL_CLOSED_VALIDATED_INPUT_COUNT")
    if report.get("regular_file_count_before_manifest") != observed_count + 3:
        raise SystemExit("FAIL_CLOSED_VALIDATION_INVENTORY_COUNT")
    return {
        "validated_input_tree_root_sha256": observed_root,
        "validated_input_regular_file_count": observed_count,
        "validation_report_sha256": entry_map[required[0]]["sha256"],
        "test_stdout_sha256": entry_map[required[1]]["sha256"],
        "test_stderr_sha256": entry_map[required[2]]["sha256"],
    }


def main() -> int:
    if MANIFEST.exists() or CHECKSUMS.exists():
        raise SystemExit("FAIL_CLOSED_ALREADY_FROZEN__CREATE_SUCCESSOR")
    entries = collect_entries(ROOT, EXCLUDED)
    validation = require_validation_evidence(entries)

    accumulator = hashlib.sha256(b"LIMEX_SCIENCE_CLEANROOM_PACKAGE_MANIFEST_V1\x00")
    for entry in entries:
        relative = entry["path"].encode("utf-8")
        digest = bytes.fromhex(entry["sha256"])
        accumulator.update(len(relative).to_bytes(8, "big"))
        accumulator.update(relative)
        accumulator.update(entry["bytes"].to_bytes(8, "big"))
        accumulator.update(digest)
    document = {
        "schema": "LIMEX_SCIENCE_CLEANROOM_PACKAGE_MANIFEST_V1",
        "release": "LIMEX_SCIENCE_CLEANROOM_V1_0_RC4",
        "hash_algorithm": "SHA-256",
        "self_exclusion": ["PACKAGE_MANIFEST.json", "SHA256SUMS.txt"],
        "regular_file_count": len(entries),
        "total_bytes": sum(entry["bytes"] for entry in entries),
        "package_root_sha256": accumulator.hexdigest(),
        **validation,
        "entries": entries,
    }
    exclusive_create(CHECKSUMS, "".join(f"{entry['sha256']}  {entry['path']}\n" for entry in entries).encode("utf-8"))
    # The manifest is the sole commit marker.  Publish it last so a crash can
    # leave at most populated checksums beside an explicitly invalid manifest.
    exclusive_create(MANIFEST, (json.dumps(document, indent=2, sort_keys=True) + "\n").encode("utf-8"))
    print(json.dumps({
        "status": "PASS_PACKAGE_IDENTITY_ONLY__NO_RELEASE_AUTHORITY",
        "regular_file_count": document["regular_file_count"],
        "total_bytes": document["total_bytes"],
        "package_root_sha256": document["package_root_sha256"],
        "manifest_sha256": hashlib.sha256(MANIFEST.read_bytes()).hexdigest(),
        "checksums_sha256": hashlib.sha256(CHECKSUMS.read_bytes()).hexdigest(),
    }, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
