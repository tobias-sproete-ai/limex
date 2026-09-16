"""Non-mutating verifier for the frozen cleanroom package."""
from __future__ import annotations

import hashlib
import json
import os
import re
import stat
import sys
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
    "regular_file_count", "total_bytes", "package_root_sha256", "entries",
}


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
    accumulator = hashlib.sha256(b"LIMEX_SETTLE_CLEANROOM_PACKAGE_MANIFEST_V1\x00")
    for entry in entries:
        relative = entry["path"].encode("utf-8")
        accumulator.update(len(relative).to_bytes(8, "big"))
        accumulator.update(relative)
        accumulator.update(entry["bytes"].to_bytes(8, "big"))
        accumulator.update(bytes.fromhex(entry["sha256"]))
    return accumulator.hexdigest()


def main(expected_root_sha256=None) -> int:
    if not re.fullmatch(r"[0-9a-f]{64}", expected_root_sha256 or ""):
        raise SystemExit("FAIL_CLOSED_CALLER_EXPECTED_ROOT_REQUIRED")
    document = json.loads(bounded_read(MANIFEST).decode("utf-8"))
    entries = collect()
    if type(document) is not dict or set(document) != MANIFEST_KEYS:
        raise SystemExit("FAIL_CLOSED_MANIFEST_CLOSED_SCHEMA")
    if document.get("schema") != "LIMEX_SETTLE_CLEANROOM_PACKAGE_MANIFEST_V1":
        raise SystemExit("FAIL_CLOSED_MANIFEST_SCHEMA")
    if document.get("release") != "LIMEX_SETTLE_CLEANROOM_V1_1_RC1":
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
    if expected_root_sha256 != observed_root:
        raise SystemExit("FAIL_CLOSED_CALLER_EXPECTED_ROOT_MISMATCH")
    expected_lines = "".join(f"{entry['sha256']}  {entry['path']}\n" for entry in entries)
    if bounded_read(CHECKSUMS).decode("utf-8") != expected_lines:
        raise SystemExit("FAIL_CLOSED_CHECKSUM_LIST_MISMATCH")
    gate = json.loads((ROOT / "PUBLIC_RELEASE_GATE.json").read_text(encoding="utf-8"))
    if gate.get("publication_status") != "BLOCKED__NO_PUBLIC_RELEASE_DISPATCH":
        raise SystemExit("FAIL_CLOSED_PUBLICATION_GATE_NOT_BLOCKED")
    if gate.get("external_effect") != "DENY" or gate.get("repository_target") is not None:
        raise SystemExit("FAIL_CLOSED_PUBLICATION_EFFECT_OR_TARGET_BOUND")
    for digest_value in (document.get("package_root_sha256"),):
        if not re.fullmatch(r"[0-9a-f]{64}", digest_value or ""):
            raise SystemExit("FAIL_CLOSED_DIGEST_FORMAT")
    print(json.dumps({
        "status": "PASS_FROZEN_PACKAGE_IDENTITY_WITH_PUBLICATION_BLOCKED",
        "regular_file_count": len(entries),
        "total_bytes": sum(entry["bytes"] for entry in entries),
        "package_root_sha256": observed_root,
        "trust_anchor_status": "CALLER_SUPPLIED_EXPECTED_ROOT_MATCH",
        "publication_status": gate["publication_status"],
    }, sort_keys=True))
    return 0


if __name__ == "__main__":
    if len(sys.argv) != 3 or sys.argv[1] != "--expected-root-sha256":
        raise SystemExit("USAGE: verify_frozen_package.py --expected-root-sha256 <trusted-sha256>")
    raise SystemExit(main(sys.argv[2]))
