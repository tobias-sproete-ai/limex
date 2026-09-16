"""Build a self-excluding SHA-256 package manifest and checksum list."""
from __future__ import annotations

import hashlib
import json
import os
import secrets
import stat
from pathlib import Path


ROOT = Path(__file__).resolve().parent.parent
MANIFEST = ROOT / "PACKAGE_MANIFEST.json"
CHECKSUMS = ROOT / "SHA256SUMS.txt"
EXCLUDED = {MANIFEST.name, CHECKSUMS.name}
MAX_PACKAGE_FILES = 10_000
MAX_PACKAGE_BYTES = 268_435_456
MAX_FILE_BYTES = 67_108_864


def atomic_replace(path: Path, body: bytes) -> None:
    """Durably replace one output relative to a retained real-directory fd."""
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
                if name == "__pycache__" or name.startswith(("release-seal-", "limex-settle-release-seal-")):
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


def main() -> int:
    atomic_replace(MANIFEST, (json.dumps({
        "schema": "LIMEX_SETTLE_CLEANROOM_PACKAGE_MANIFEST_V1",
        "status": "INVALIDATED_PENDING_REBUILD__NO_PASS_CLAIM",
    }, indent=2, sort_keys=True) + "\n").encode("utf-8"))
    atomic_replace(CHECKSUMS, b"")
    entries = collect_entries(ROOT, EXCLUDED)

    accumulator = hashlib.sha256(b"LIMEX_SETTLE_CLEANROOM_PACKAGE_MANIFEST_V1\x00")
    for entry in entries:
        relative = entry["path"].encode("utf-8")
        digest = bytes.fromhex(entry["sha256"])
        accumulator.update(len(relative).to_bytes(8, "big"))
        accumulator.update(relative)
        accumulator.update(entry["bytes"].to_bytes(8, "big"))
        accumulator.update(digest)
    document = {
        "schema": "LIMEX_SETTLE_CLEANROOM_PACKAGE_MANIFEST_V1",
        "release": "LIMEX_SETTLE_CLEANROOM_V1_1_RC1",
        "hash_algorithm": "SHA-256",
        "self_exclusion": ["PACKAGE_MANIFEST.json", "SHA256SUMS.txt"],
        "regular_file_count": len(entries),
        "total_bytes": sum(entry["bytes"] for entry in entries),
        "package_root_sha256": accumulator.hexdigest(),
        "entries": entries,
    }
    atomic_replace(CHECKSUMS, "".join(f"{entry['sha256']}  {entry['path']}\n" for entry in entries).encode("utf-8"))
    # The manifest is the sole commit marker.  Publish it last so a crash can
    # leave at most populated checksums beside an explicitly invalid manifest.
    atomic_replace(MANIFEST, (json.dumps(document, indent=2, sort_keys=True) + "\n").encode("utf-8"))
    print(json.dumps({
        "status": "PASS",
        "regular_file_count": document["regular_file_count"],
        "total_bytes": document["total_bytes"],
        "package_root_sha256": document["package_root_sha256"],
        "manifest_sha256": hashlib.sha256(MANIFEST.read_bytes()).hexdigest(),
        "checksums_sha256": hashlib.sha256(CHECKSUMS.read_bytes()).hexdigest(),
    }, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
