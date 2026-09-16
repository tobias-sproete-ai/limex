"""LIMEX Settle release seal.

This module is deliberately separate from the financial/event settlement core.
It performs one local, evidence-bound, no-clobber publication of a release
envelope.  It does not execute payments, create wallets, deploy a chain, or
grant execution authority to an LLM.
"""
from __future__ import annotations

import errno
import hashlib
import json
import os
import re
import selectors
import stat
import subprocess
import sys
import time
from datetime import datetime, timezone
from pathlib import Path, PurePosixPath
from zoneinfo import ZoneInfo

from settle_core import (
    Invalid,
    canonical,
    decode,
    digest,
    identifier,
    sha,
    utc_ms,
    verify_private_fd,
)


VERSION = "LIMEX_SETTLE_RELEASE_SEAL_V1"
RUN_SCHEMA = "LIMEX_SETTLE_RUN_CONFIG_V1"
CONTRACT_SCHEMA = "LIMEX_SETTLE_CONTRACT_V1"
PAYLOAD_SCHEMA = "LIMEX_SETTLE_PAYLOAD_V1"
ENVELOPE_SCHEMA = "LIMEX_SETTLE_ENVELOPE_V1"
TERMINAL_SCHEMA = "LIMEX_SETTLE_TERMINAL_V1"
OPERATION_DOMAIN = "RELEASE_SEAL"
DOMAIN = b"LIMEX_SETTLE_PAYLOAD_V1\x00"
SHA1 = re.compile(r"[0-9a-f]{40}\Z")
MAX_JSON_INPUT_BYTES = 4_194_304
MAX_BOUND_FILE_BYTES = 67_108_864
MAX_GIT_OUTPUT_BYTES = 33_554_432
MAX_EXECUTABLE_BYTES = 268_435_456
MAX_GIT_TRACKED_FILES = 100_000
MAX_GIT_TRACKED_BYTES = 1_073_741_824
MAX_GIT_TRACKED_HASH_SECONDS = 30.0
MAX_GIT_WORKTREE_ENTRIES = 200_000
MAX_GIT_WORKTREE_DEPTH = 64
LOCAL_WITH_OFFSET = re.compile(
    r"\d{4}-\d\d-\d\dT\d\d:\d\d:\d\d(?:\.\d{3})?[+-]\d\d:\d\d\Z"
)
ROLE_SET = {
    "CTO_RELEASE_SEAL_AUTHORIZATION",
    "LEAN_KERNEL_ATTESTATION",
    "PCT_REFERENCE",
    "TOKEN_METRICS",
}
REQUIRED_ASSERTIONS = {
    "LEAN_KERNEL_ATTESTATION": {("/exit_code", "0")},
    "TOKEN_METRICS": {("/causal_savings_status", "UNSUPPORTED")},
}
SCOPE_ASSERTIONS = {
    "LOCAL_SYNTHETIC_TEST": {
        "CTO_RELEASE_SEAL_AUTHORIZATION": {
            ("/authorization_status", "LOCAL_SYNTHETIC_AUTHORITY_REFERENCE_ONLY")
        },
        "PCT_REFERENCE": {
            ("/filing_status", "DRAFT_REVIEW_REQUIRED__NOT_FILING_READY")
        },
    },
    "AUTHORIZATION_ASSERTED_RELEASE_SEAL": {
        "CTO_RELEASE_SEAL_AUTHORIZATION": {
            ("/authorization_status", "EXPLICIT_CTO_RELEASE_SEAL_AUTHORIZATION")
        },
        "PCT_REFERENCE": {
            ("/filing_status", "FILED_CONFIRMED_BY_AUTHORIZED_SOURCE")
        },
    },
}
SCOPE_EVIDENCE_CLASSES = {
    "LOCAL_SYNTHETIC_TEST": {
        "CTO_RELEASE_SEAL_AUTHORIZATION": "LOCAL_SYNTHETIC_AUTHORITY_REFERENCE",
        "LEAN_KERNEL_ATTESTATION": "LOCAL_SYNTHETIC_KERNEL_METADATA",
        "PCT_REFERENCE": "LOCAL_SYNTHETIC_FILING_STATUS",
        "TOKEN_METRICS": "LOCAL_SYNTHETIC_METRIC_STATUS",
    },
    "AUTHORIZATION_ASSERTED_RELEASE_SEAL": {
        "CTO_RELEASE_SEAL_AUTHORIZATION": "CTO_ASSERTION_REFERENCE__AUTHENTICITY_NOT_VERIFIED",
        "LEAN_KERNEL_ATTESTATION": "LOCAL_KERNEL_REPORT_REFERENCE",
        "PCT_REFERENCE": "AUTHORIZED_SOURCE_ASSERTION_REFERENCE__AUTHENTICITY_NOT_VERIFIED",
        "TOKEN_METRICS": "LOCAL_METRICS_REPORT_REFERENCE",
    },
}
RUN_KEYS = (
    "schema",
    "artifact_root",
    "contract_path",
    "git_executable",
    "git_repo_root",
    "limex_root",
    "state_root",
)
CONTRACT_KEYS = (
    "schema",
    "priority_id",
    "settle_at_utc",
    "settle_at_local",
    "settle_timezone",
    "host_clock_evidence_class",
    "execution_scope",
    "runtime_binding",
    "git_binding",
    "llm_interface_binding",
    "artifacts",
)
RUNTIME_KEYS = (
    "release",
    "regular_files",
    "total_bytes",
    "tree_sha256",
    "skill_md_sha256",
    "python_version",
    "python_executable_sha256",
    "git_executable_sha256",
)
GIT_KEYS = (
    "head_commit_sha1",
    "head_tree_sha1",
    "tracked_files",
    "tracked_bytes",
    "tracked_content_sha256",
    "clean_worktree",
)
LLM_KEYS = (
    "mode",
    "schema_version",
    "producer_runtime_sha256",
    "financial_feedback_to_llm",
)
ARTIFACT_KEYS = (
    "role",
    "artifact_id",
    "path",
    "bytes",
    "sha256",
    "evidence_class",
    "json_assertions",
)
MEASURED_ARTIFACT_KEYS = (
    "role",
    "artifact_id",
    "path",
    "bytes",
    "sha256",
    "evidence_class",
)
ASSERTION_KEYS = ("pointer", "expected_scalar")
PAYLOAD_KEYS = (
    "schema",
    "priority_id",
    "contract_sha256",
    "reservation_sha256",
    "settle_at_utc",
    "settled_at_utc",
    "host_clock_evidence_class",
    "execution_scope",
    "runtime",
    "git",
    "llm_interface_binding",
    "artifacts",
    "external_effect",
)


def exact(value, keys, reason="CLOSED_SCHEMA_REQUIRED"):
    if type(value) is not dict or set(value) != set(keys):
        raise Invalid(reason)


def ascii_enum(value, reason="ASCII_ENUM_REQUIRED", maximum=256):
    if (
        type(value) is not str
        or not value
        or len(value.encode("ascii", "ignore")) != len(value)
        or len(value) > maximum
        or not re.fullmatch(r"[A-Z0-9][A-Z0-9_.:-]*", value)
    ):
        raise Invalid(reason)
    return value


def absolute_directory(value, reason):
    if type(value) is not str or not os.path.isabs(value):
        raise Invalid(reason)
    path = Path(value)
    try:
        info = path.lstat()
    except OSError as exc:
        raise Invalid(reason) from exc
    if path.is_symlink() or not stat.S_ISDIR(info.st_mode):
        raise Invalid(reason)
    return path.resolve(strict=True)


def absolute_regular_file(value, reason):
    if type(value) is not str or not os.path.isabs(value):
        raise Invalid(reason)
    path = Path(value)
    try:
        info = path.lstat()
    except OSError as exc:
        raise Invalid(reason) from exc
    if path.is_symlink() or not stat.S_ISREG(info.st_mode):
        raise Invalid(reason)
    return path.resolve(strict=True)


def read_absolute_descriptor_bound(value, reason, maximum_bytes=MAX_JSON_INPUT_BYTES):
    """Read an absolute regular file without following any path-component link."""
    if type(value) is not str or not value.startswith("/") or "\x00" in value:
        raise Invalid(reason)
    parts = Path(value).parts[1:]
    if not parts or any(part in {"", ".", ".."} for part in parts):
        raise Invalid(reason)
    directory_flags = os.O_RDONLY | getattr(os, "O_DIRECTORY", 0) | getattr(os, "O_NOFOLLOW", 0)
    file_flags = os.O_RDONLY | getattr(os, "O_NOFOLLOW", 0) | getattr(os, "O_NONBLOCK", 0)
    descriptors = []
    try:
        current = os.open("/", directory_flags)
        descriptors.append(current)
        for segment in parts[:-1]:
            current = os.open(segment, directory_flags, dir_fd=current)
            descriptors.append(current)
        leaf = os.open(parts[-1], file_flags, dir_fd=current)
        descriptors.append(leaf)
        before = os.fstat(leaf)
        if not stat.S_ISREG(before.st_mode):
            raise Invalid(reason)
        if before.st_size > maximum_bytes:
            raise Invalid("ABSOLUTE_FILE_BYTE_BOUND_EXCEEDED")
        body = bytearray()
        while True:
            chunk = os.read(leaf, min(1024 * 1024, maximum_bytes + 1 - len(body)))
            if not chunk:
                break
            body.extend(chunk)
            if len(body) > maximum_bytes:
                raise Invalid("ABSOLUTE_FILE_BYTE_BOUND_EXCEEDED")
        after = os.fstat(leaf)
        if (
            before.st_dev,
            before.st_ino,
            before.st_mode,
            before.st_size,
            before.st_mtime_ns,
            before.st_ctime_ns,
        ) != (
            after.st_dev,
            after.st_ino,
            after.st_mode,
            after.st_size,
            after.st_mtime_ns,
            after.st_ctime_ns,
        ):
            raise Invalid("ABSOLUTE_FILE_CHANGED_DURING_READ")
        if len(body) != before.st_size:
            raise Invalid("ABSOLUTE_FILE_SHORT_READ")
        return bytes(body)
    except OSError as exc:
        if exc.errno in {errno.ELOOP, errno.ENOTDIR}:
            raise Invalid("SYMLINK_OR_NON_DIRECTORY_REJECTED") from exc
        raise Invalid(reason) from exc
    finally:
        for descriptor in reversed(descriptors):
            try:
                os.close(descriptor)
            except OSError:
                pass


def require_disjoint(left: Path, right: Path):
    if left == right or left in right.parents or right in left.parents:
        raise Invalid("ARTIFACT_AND_STATE_ROOT_NOT_DISJOINT")
    if left.stat().st_dev != right.stat().st_dev:
        raise Invalid("ARTIFACT_AND_STATE_ROOT_FILESYSTEM_MISMATCH")


def relative_posix_file(value):
    if type(value) is not str or not value or not value.isascii():
        raise Invalid("RELATIVE_ASCII_PATH_REQUIRED")
    if "\\" in value or "\x00" in value or ":" in value or value.startswith("/"):
        raise Invalid("RELATIVE_POSIX_PATH_REQUIRED")
    normalized = PurePosixPath(value)
    if normalized.as_posix() != value:
        raise Invalid("CANONICAL_RELATIVE_POSIX_PATH_REQUIRED")
    parts = normalized.parts
    if not parts or any(part in {"", ".", ".."} for part in parts):
        raise Invalid("PATH_TRAVERSAL_REJECTED")
    return parts


def read_descriptor_bound(
    root: Path,
    relative: str,
    maximum_bytes=MAX_BOUND_FILE_BYTES,
    *,
    include_file_identity=False,
    include_stat=False,
):
    """Read one regular file through no-follow descriptors under root."""
    parts = relative_posix_file(relative)
    directory_flags = os.O_RDONLY | getattr(os, "O_DIRECTORY", 0) | getattr(os, "O_NOFOLLOW", 0)
    file_flags = os.O_RDONLY | getattr(os, "O_NOFOLLOW", 0) | getattr(os, "O_NONBLOCK", 0)
    descriptors = []
    try:
        current = os.open(root, directory_flags)
        descriptors.append(current)
        for segment in parts[:-1]:
            current = os.open(segment, directory_flags, dir_fd=current)
            descriptors.append(current)
        leaf = os.open(parts[-1], file_flags, dir_fd=current)
        descriptors.append(leaf)
        before = os.fstat(leaf)
        if not stat.S_ISREG(before.st_mode):
            raise Invalid("ARTIFACT_REGULAR_FILE_REQUIRED")
        if before.st_size > maximum_bytes:
            raise Invalid("BOUND_FILE_BYTE_LIMIT_EXCEEDED")
        body = bytearray()
        while True:
            chunk = os.read(leaf, min(1024 * 1024, maximum_bytes + 1 - len(body)))
            if not chunk:
                break
            body.extend(chunk)
            if len(body) > maximum_bytes:
                raise Invalid("BOUND_FILE_BYTE_LIMIT_EXCEEDED")
        after = os.fstat(leaf)
        identity_before = (
            before.st_dev,
            before.st_ino,
            before.st_mode,
            before.st_size,
            before.st_mtime_ns,
            before.st_ctime_ns,
        )
        identity_after = (
            after.st_dev,
            after.st_ino,
            after.st_mode,
            after.st_size,
            after.st_mtime_ns,
            after.st_ctime_ns,
        )
        if identity_before != identity_after:
            raise Invalid("ARTIFACT_CHANGED_DURING_READ")
        if len(body) != before.st_size:
            raise Invalid("ARTIFACT_SHORT_READ")
        result = bytes(body)
        if include_stat:
            return result, before
        if include_file_identity:
            return result, (before.st_dev, before.st_ino)
        return result
    except OSError as exc:
        if exc.errno in {errno.ELOOP, errno.ENOTDIR}:
            raise Invalid("SYMLINK_OR_NON_DIRECTORY_REJECTED") from exc
        raise
    finally:
        for descriptor in reversed(descriptors):
            try:
                os.close(descriptor)
            except OSError:
                pass


def strict_json_document(body: bytes):
    def pairs(items):
        result = {}
        for key, value in items:
            if key in result:
                raise Invalid("DUPLICATE_JSON_KEY")
            result[key] = value
        return result

    try:
        return json.loads(body.decode("utf-8"), object_pairs_hook=pairs)
    except Invalid:
        raise
    except (UnicodeError, json.JSONDecodeError) as exc:
        raise Invalid("ASSERTION_JSON_INVALID") from exc


def scalar_text(value):
    if value is True:
        return "true"
    if value is False:
        return "false"
    if value is None:
        return "null"
    if type(value) in {str, int}:
        return str(value)
    raise Invalid("ASSERTION_TARGET_NOT_SCALAR")


def json_pointer(document, pointer):
    if type(pointer) is not str or not pointer.startswith("/") or not pointer.isascii():
        raise Invalid("JSON_POINTER_INVALID")
    current = document
    for raw in pointer.split("/")[1:]:
        token = raw.replace("~1", "/").replace("~0", "~")
        if type(current) is dict and token in current:
            current = current[token]
        elif type(current) is list and token.isdigit() and int(token) < len(current):
            current = current[int(token)]
        else:
            raise Invalid("JSON_POINTER_MISSING")
    return current


def verify_assertions(body: bytes, assertions):
    if type(assertions) is not list or len(assertions) > 64:
        raise Invalid("ASSERTION_LIST_INVALID")
    if not assertions:
        return
    document = strict_json_document(body)
    seen = set()
    for assertion in assertions:
        exact(assertion, ASSERTION_KEYS, "ASSERTION_SCHEMA_INVALID")
        pointer = assertion["pointer"]
        expected = assertion["expected_scalar"]
        if pointer in seen or type(expected) is not str or len(expected) > 1024:
            raise Invalid("ASSERTION_INVALID")
        seen.add(pointer)
        if scalar_text(json_pointer(document, pointer)) != expected:
            raise Invalid("ARTIFACT_ASSERTION_MISMATCH")


def list_tree(root: Path):
    files = []
    stack = [root]
    entries_seen = 0
    while stack:
        current = stack.pop()
        for entry in sorted(os.scandir(current), key=lambda item: item.name, reverse=True):
            entries_seen += 1
            if entries_seen > 100_000:
                raise Invalid("LIMEX_TREE_ENTRY_BOUND_EXCEEDED")
            info = entry.stat(follow_symlinks=False)
            if entry.is_symlink():
                raise Invalid("LIMEX_TREE_SYMLINK_REJECTED")
            item = Path(entry.path)
            if stat.S_ISDIR(info.st_mode):
                stack.append(item)
            elif stat.S_ISREG(info.st_mode):
                files.append(item.relative_to(root).as_posix())
            else:
                raise Invalid("LIMEX_TREE_SPECIAL_FILE_REJECTED")
    return sorted(files)


def tree_identity(root: Path):
    files = list_tree(root)
    if len(files) > 100_000:
        raise Invalid("LIMEX_TREE_FILE_BOUND_EXCEEDED")
    hasher = hashlib.sha256()
    total = 0
    for relative in files:
        body = read_descriptor_bound(root, relative)
        total += len(body)
        if total > 1_000_000_000:
            raise Invalid("LIMEX_TREE_BYTE_BOUND_EXCEEDED")
        path_bytes = relative.encode("utf-8")
        hasher.update(len(path_bytes).to_bytes(8, "big"))
        hasher.update(path_bytes)
        hasher.update(len(body).to_bytes(8, "big"))
        hasher.update(body)
    skill = read_descriptor_bound(root, "SKILL.md")
    return {
        "regular_files": len(files),
        "total_bytes": total,
        "tree_sha256": hasher.hexdigest(),
        "skill_md_sha256": sha(skill),
    }


def file_sha256(path: Path):
    descriptor = os.open(path, os.O_RDONLY | getattr(os, "O_NOFOLLOW", 0) | getattr(os, "O_NONBLOCK", 0))
    try:
        before = os.fstat(descriptor)
        if not stat.S_ISREG(before.st_mode) or before.st_size > MAX_EXECUTABLE_BYTES:
            raise Invalid("EXECUTABLE_BYTE_BOUND_EXCEEDED")
        hasher = hashlib.sha256()
        measured = 0
        while True:
            chunk = os.read(descriptor, min(1024 * 1024, MAX_EXECUTABLE_BYTES + 1 - measured))
            if not chunk:
                break
            measured += len(chunk)
            if measured > MAX_EXECUTABLE_BYTES:
                raise Invalid("EXECUTABLE_BYTE_BOUND_EXCEEDED")
            hasher.update(chunk)
        after = os.fstat(descriptor)
        before_identity = (before.st_dev, before.st_ino, before.st_mode, before.st_size, before.st_mtime_ns, before.st_ctime_ns)
        after_identity = (after.st_dev, after.st_ino, after.st_mode, after.st_size, after.st_mtime_ns, after.st_ctime_ns)
        if before_identity != after_identity or measured != before.st_size:
            raise Invalid("EXECUTABLE_CHANGED_DURING_READ")
        return hasher.hexdigest()
    finally:
        os.close(descriptor)


def _run_git_bounded(git_executable: Path, repo: Path, *arguments):
    process = subprocess.Popen(
        [
            str(git_executable),
            "--no-replace-objects",
            "-c", "protocol.allow=never",
            "-c", "protocol.file.allow=never",
            "-c", "protocol.ext.allow=never",
            "-c", "protocol.ssh.allow=never",
            "-c", "protocol.git.allow=never",
            "-c", "protocol.http.allow=never",
            "-c", "protocol.https.allow=never",
            "-c", "credential.helper=",
            "-c", "core.fsmonitor=false",
            "-c", "core.hooksPath=/dev/null",
            "-c", "core.pager=cat",
            "-c", "pager.status=false",
            "-c", "color.ui=false",
            "-C", str(repo),
            *arguments,
        ],
        stdin=subprocess.DEVNULL,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        shell=False,
        env={
            "PATH": "/usr/bin:/bin",
            "LC_ALL": "C",
            "GIT_CONFIG_NOSYSTEM": "1",
            "GIT_CONFIG_GLOBAL": "/dev/null",
            "GIT_NO_LAZY_FETCH": "1",
            "GIT_NO_REPLACE_OBJECTS": "1",
            "GIT_OPTIONAL_LOCKS": "0",
            "GIT_TERMINAL_PROMPT": "0",
            "GCM_INTERACTIVE": "Never",
            "TMPDIR": "/tmp",
        },
    )
    streams = selectors.DefaultSelector()
    output = {"stdout": bytearray(), "stderr": bytearray()}
    try:
        for name, stream in (("stdout", process.stdout), ("stderr", process.stderr)):
            if stream is None:
                raise Invalid("GIT_PIPE_SETUP_FAILED")
            os.set_blocking(stream.fileno(), False)
            streams.register(stream, selectors.EVENT_READ, name)
        deadline = time.monotonic() + 15
        while streams.get_map():
            remaining = deadline - time.monotonic()
            if remaining <= 0:
                raise Invalid("GIT_READBACK_TIMEOUT")
            events = streams.select(remaining)
            if not events:
                raise Invalid("GIT_READBACK_TIMEOUT")
            for key, _ in events:
                chunk = os.read(key.fileobj.fileno(), 65_536)
                if not chunk:
                    streams.unregister(key.fileobj)
                    continue
                target = output[key.data]
                target.extend(chunk)
                if len(target) > MAX_GIT_OUTPUT_BYTES:
                    raise Invalid("GIT_OUTPUT_BYTE_BOUND_EXCEEDED")
        remaining = max(0.001, deadline - time.monotonic())
        return_code = process.wait(timeout=remaining)
        if return_code != 0 or output["stderr"]:
            raise Invalid("GIT_READBACK_FAILED")
        return bytes(output["stdout"])
    except subprocess.TimeoutExpired as exc:
        raise Invalid("GIT_READBACK_TIMEOUT") from exc
    finally:
        streams.close()
        if process.poll() is None:
            process.kill()
            process.wait()
        if process.stdout is not None:
            process.stdout.close()
        if process.stderr is not None:
            process.stderr.close()


def run_git(git_executable: Path, repo: Path, *arguments):
    try:
        return _run_git_bounded(git_executable, repo, *arguments).decode("utf-8").rstrip("\n")
    except UnicodeDecodeError as exc:
        raise Invalid("GIT_OUTPUT_UTF8_REQUIRED") from exc


def run_git_bytes(git_executable: Path, repo: Path, *arguments):
    return _run_git_bounded(git_executable, repo, *arguments)


def validate_root_git_directory(repo: Path):
    """Require the selected worktree root to contain a real `.git` directory."""
    metadata = repo / ".git"
    try:
        info = metadata.lstat()
    except OSError as exc:
        raise Invalid("GIT_ROOT_METADATA_DIRECTORY_REQUIRED") from exc
    if metadata.is_symlink() or not stat.S_ISDIR(info.st_mode):
        raise Invalid("GIT_ROOT_METADATA_DIRECTORY_REQUIRED")


def _parse_git_head_records(listing: bytes):
    records = {}
    for record in (item for item in listing.split(b"\x00") if item):
        try:
            metadata, raw_path = record.split(b"\t", 1)
            mode, kind, object_id = metadata.decode("ascii").split(" ")
            relative = raw_path.decode("utf-8")
        except (ValueError, UnicodeError) as exc:
            raise Invalid("GIT_TREE_RECORD_INVALID") from exc
        relative_posix_file(relative)
        if (
            kind != "blob"
            or mode not in {"100644", "100755"}
            or not SHA1.fullmatch(object_id)
            or relative in records
        ):
            raise Invalid("GIT_TRACKED_ENTRY_UNSUPPORTED")
        records[relative] = (mode, object_id)
    if not records:
        raise Invalid("GIT_HEAD_TRACKED_FILE_REQUIRED")
    if len(records) > MAX_GIT_TRACKED_FILES:
        raise Invalid("GIT_TRACKED_FILE_COUNT_BOUND_EXCEEDED")
    return records


def _parse_git_index_records(listing: bytes):
    records = {}
    for record in (item for item in listing.split(b"\x00") if item):
        try:
            metadata, raw_path = record.split(b"\t", 1)
            mode, object_id, stage = metadata.decode("ascii").split(" ")
            relative = raw_path.decode("utf-8")
        except (ValueError, UnicodeError) as exc:
            raise Invalid("GIT_INDEX_RECORD_INVALID") from exc
        relative_posix_file(relative)
        if (
            stage != "0"
            or mode not in {"100644", "100755"}
            or not SHA1.fullmatch(object_id)
            or relative in records
        ):
            raise Invalid("GIT_INDEX_ENTRY_UNSUPPORTED")
        records[relative] = (mode, object_id)
    return records


def _tracked_flag_paths(listing: bytes, reason: str):
    result = {}
    for record in (item for item in listing.split(b"\x00") if item):
        try:
            prefix, raw_path = record[:1], record[2:]
            if record[1:2] != b" ":
                raise ValueError
            relative = raw_path.decode("utf-8")
        except (ValueError, UnicodeError) as exc:
            raise Invalid(reason) from exc
        relative_posix_file(relative)
        if relative in result:
            raise Invalid(reason)
        result[relative] = prefix
    return result


def inventory_worktree_files(repo: Path):
    """Inventory raw worktree entries without consulting Git attributes/config.

    Only the real root `.git` metadata directory is excluded. Every symlink or
    special entry below the worktree, and every regular file not tracked in
    HEAD/index, remains visible to the caller and is rejected.
    """
    directory_flags = os.O_RDONLY | getattr(os, "O_DIRECTORY", 0) | getattr(os, "O_NOFOLLOW", 0)
    root_descriptor = os.open(repo, directory_flags)
    files = set()
    observed_entries = 0
    deadline = time.monotonic() + MAX_GIT_TRACKED_HASH_SECONDS

    def walk(descriptor, prefix="", depth=0):
        nonlocal observed_entries
        if depth > MAX_GIT_WORKTREE_DEPTH:
            raise Invalid("GIT_WORKTREE_DEPTH_BOUND_EXCEEDED")
        with os.scandir(descriptor) as entries:
            for entry in entries:
                if time.monotonic() > deadline:
                    raise Invalid("GIT_WORKTREE_INVENTORY_DEADLINE_EXCEEDED")
                name = entry.name
                if not prefix and name == ".git":
                    continue
                observed_entries += 1
                if observed_entries > MAX_GIT_WORKTREE_ENTRIES:
                    raise Invalid("GIT_WORKTREE_ENTRY_COUNT_BOUND_EXCEEDED")
                relative = f"{prefix}/{name}" if prefix else name
                try:
                    info = entry.stat(follow_symlinks=False)
                except OSError as exc:
                    raise Invalid("GIT_WORKTREE_INVENTORY_FAILED") from exc
                if stat.S_ISREG(info.st_mode):
                    try:
                        relative_posix_file(relative)
                    except Invalid as exc:
                        raise Invalid("GIT_WORKTREE_ENTRY_UNSUPPORTED") from exc
                    files.add(relative)
                elif stat.S_ISDIR(info.st_mode):
                    try:
                        child = os.open(name, directory_flags, dir_fd=descriptor)
                    except OSError as exc:
                        raise Invalid("GIT_WORKTREE_INVENTORY_FAILED") from exc
                    try:
                        walk(child, relative, depth + 1)
                    finally:
                        os.close(child)
                else:
                    raise Invalid("GIT_WORKTREE_ENTRY_UNSUPPORTED")

    try:
        walk(root_descriptor)
    finally:
        os.close(root_descriptor)
    return files


def validate_head_worktree_bytes(git_executable: Path, repo: Path):
    """Compare every tracked worktree byte string with the committed HEAD blob.

    This deliberately bypasses Git filters and index stat shortcuts. Tracked
    symlinks and submodules are rejected rather than silently assigned regular
    file semantics by the release seal.
    """
    head_records = _parse_git_head_records(
        run_git_bytes(git_executable, repo, "ls-tree", "-r", "-z", "HEAD")
    )
    index_records = _parse_git_index_records(
        run_git_bytes(git_executable, repo, "ls-files", "--stage", "-z")
    )
    if index_records != head_records:
        raise Invalid("GIT_INDEX_HEAD_MISMATCH")
    if inventory_worktree_files(repo) != set(head_records):
        raise Invalid("GIT_WORKTREE_INVENTORY_MISMATCH")
    deadline = time.monotonic() + MAX_GIT_TRACKED_HASH_SECONDS
    total_bytes = 0
    aggregate = hashlib.sha256(b"LIMEX_GIT_TRACKED_CONTENT_V1\x00")
    for relative in sorted(head_records):
        if time.monotonic() > deadline:
            raise Invalid("GIT_TRACKED_HASH_DEADLINE_EXCEEDED")
        mode, object_id = head_records[relative]
        body, worktree_info = read_descriptor_bound(repo, relative, include_stat=True)
        expected_executable = mode == "100755"
        observed_executable = bool(worktree_info.st_mode & stat.S_IXUSR)
        if observed_executable != expected_executable:
            raise Invalid("GIT_TRACKED_WORKTREE_MODE_MISMATCH")
        total_bytes += len(body)
        if total_bytes > MAX_GIT_TRACKED_BYTES:
            raise Invalid("GIT_TRACKED_BYTE_BOUND_EXCEEDED")
        measured = hashlib.sha1(
            b"blob " + str(len(body)).encode("ascii") + b"\x00" + body
        ).hexdigest()
        if measured != object_id:
            raise Invalid("GIT_TRACKED_WORKTREE_BYTE_MISMATCH")
        path_bytes = relative.encode("utf-8")
        aggregate.update(len(path_bytes).to_bytes(8, "big"))
        aggregate.update(path_bytes)
        aggregate.update(mode.encode("ascii"))
        aggregate.update(len(body).to_bytes(8, "big"))
        aggregate.update(body)
    return {
        "tracked_files": len(head_records),
        "tracked_bytes": total_bytes,
        "tracked_content_sha256": aggregate.hexdigest(),
    }


def validate_local_time(contract):
    local = contract["settle_at_local"]
    zone_name = contract["settle_timezone"]
    if type(local) is not str or not LOCAL_WITH_OFFSET.fullmatch(local):
        raise Invalid("SETTLE_LOCAL_TIME_INVALID")
    if type(zone_name) is not str or not zone_name.isascii() or len(zone_name) > 64:
        raise Invalid("SETTLE_TIMEZONE_INVALID")
    try:
        parsed = datetime.fromisoformat(local)
        zoned = parsed.astimezone(ZoneInfo(zone_name))
    except (ValueError, KeyError) as exc:
        raise Invalid("SETTLE_LOCAL_TIME_INVALID") from exc
    if parsed.utcoffset() != zoned.utcoffset():
        raise Invalid("SETTLE_LOCAL_OFFSET_ZONE_MISMATCH")
    expected_utc = parsed.astimezone(timezone.utc).strftime("%Y-%m-%dT%H:%M:%S.%f")[:-3] + "Z"
    if expected_utc != contract["settle_at_utc"]:
        raise Invalid("SETTLE_LOCAL_UTC_MISMATCH")


def validate_contract(contract):
    exact(contract, CONTRACT_KEYS, "CONTRACT_CLOSED_SCHEMA_REQUIRED")
    if contract["schema"] != CONTRACT_SCHEMA:
        raise Invalid("CONTRACT_SCHEMA_UNSUPPORTED")
    identifier(contract["priority_id"])
    utc_ms(contract["settle_at_utc"])
    validate_local_time(contract)
    if contract["host_clock_evidence_class"] != "HOST_CLOCK_OBSERVATION_ONLY":
        raise Invalid("HOST_CLOCK_EVIDENCE_CLASS_REQUIRED")
    if contract["execution_scope"] not in {
        "LOCAL_SYNTHETIC_TEST",
        "AUTHORIZATION_ASSERTED_RELEASE_SEAL",
    }:
        raise Invalid("EXECUTION_SCOPE_INVALID")

    runtime = contract["runtime_binding"]
    exact(runtime, RUNTIME_KEYS, "RUNTIME_BINDING_SCHEMA_INVALID")
    if runtime["release"] != "LIMEX R5.5.17":
        raise Invalid("LIMEX_RELEASE_UNSUPPORTED")
    for field in ("regular_files", "total_bytes"):
        if type(runtime[field]) is not int or runtime[field] < 1:
            raise Invalid("RUNTIME_INTEGER_INVALID")
    for field in ("tree_sha256", "skill_md_sha256", "python_executable_sha256", "git_executable_sha256"):
        digest(runtime[field])
    if type(runtime["python_version"]) is not str or not runtime["python_version"].startswith("3."):
        raise Invalid("PYTHON_VERSION_INVALID")

    git = contract["git_binding"]
    exact(git, GIT_KEYS, "GIT_BINDING_SCHEMA_INVALID")
    if not SHA1.fullmatch(git["head_commit_sha1"]) or not SHA1.fullmatch(git["head_tree_sha1"]):
        raise Invalid("GIT_SHA1_INVALID")
    if type(git["tracked_files"]) is not int or not 1 <= git["tracked_files"] <= MAX_GIT_TRACKED_FILES:
        raise Invalid("GIT_TRACKED_FILE_COUNT_INVALID")
    if type(git["tracked_bytes"]) is not int or not 1 <= git["tracked_bytes"] <= MAX_GIT_TRACKED_BYTES:
        raise Invalid("GIT_TRACKED_BYTE_COUNT_INVALID")
    digest(git["tracked_content_sha256"])
    if git["clean_worktree"] != "REQUIRED":
        raise Invalid("CLEAN_GIT_WORKTREE_REQUIRED")

    interface = contract["llm_interface_binding"]
    exact(interface, LLM_KEYS, "LLM_INTERFACE_SCHEMA_INVALID")
    digest(interface["producer_runtime_sha256"])
    if (
        interface["mode"] != "DECOUPLED_VERSIONED_ATTESTATION_INTERFACE_REQUIRED"
        or interface["schema_version"] != "LIMEX_LLM_EXECUTION_ATTESTATION_V1"
        or interface["financial_feedback_to_llm"] != "DENY"
    ):
        raise Invalid("LLM_INTERFACE_BINDING_INVALID")

    artifacts = contract["artifacts"]
    if type(artifacts) is not list or len(artifacts) != len(ROLE_SET):
        raise Invalid("ARTIFACT_CARDINALITY_INVALID")
    roles, ids, paths = set(), set(), set()
    if artifacts != sorted(artifacts, key=lambda item: (item.get("role", ""), item.get("artifact_id", ""), item.get("path", ""))):
        raise Invalid("ARTIFACT_BINDINGS_CANONICAL_ORDER_REQUIRED")
    for artifact in artifacts:
        exact(artifact, ARTIFACT_KEYS, "ARTIFACT_SCHEMA_INVALID")
        if artifact["role"] not in ROLE_SET:
            raise Invalid("ARTIFACT_ROLE_INVALID")
        identifier(artifact["artifact_id"])
        relative_posix_file(artifact["path"])
        if type(artifact["bytes"]) is not int or artifact["bytes"] < 1:
            raise Invalid("ARTIFACT_BYTES_INVALID")
        digest(artifact["sha256"])
        ascii_enum(artifact["evidence_class"], "EVIDENCE_CLASS_INVALID")
        if artifact["role"] in roles or artifact["artifact_id"] in ids or artifact["path"] in paths:
            raise Invalid("DUPLICATE_ARTIFACT_BINDING")
        roles.add(artifact["role"])
        ids.add(artifact["artifact_id"])
        paths.add(artifact["path"])
        if type(artifact["json_assertions"]) is not list:
            raise Invalid("ASSERTION_LIST_INVALID")
        if artifact["json_assertions"] != sorted(
            artifact["json_assertions"], key=lambda item: (item.get("pointer", ""), item.get("expected_scalar", ""))
        ):
            raise Invalid("ASSERTIONS_CANONICAL_ORDER_REQUIRED")
        present = {(item.get("pointer"), item.get("expected_scalar")) for item in artifact["json_assertions"] if type(item) is dict}
        required = REQUIRED_ASSERTIONS.get(artifact["role"], set()) | SCOPE_ASSERTIONS[
            contract["execution_scope"]
        ].get(artifact["role"], set())
        if not required.issubset(present):
            raise Invalid("REQUIRED_ROLE_ASSERTION_MISSING")
        if artifact["evidence_class"] != SCOPE_EVIDENCE_CLASSES[
            contract["execution_scope"]
        ][artifact["role"]]:
            raise Invalid("ROLE_EVIDENCE_CLASS_MISMATCH")
    if roles != ROLE_SET:
        raise Invalid("REQUIRED_ARTIFACT_ROLE_MISSING")
    return contract


def validate_runtime(contract, limex_root: Path):
    measured = tree_identity(limex_root)
    expected = contract["runtime_binding"]
    for field in ("regular_files", "total_bytes", "tree_sha256", "skill_md_sha256"):
        if measured[field] != expected[field]:
            raise Invalid("LIMEX_RUNTIME_IDENTITY_MISMATCH")
    if sys.version.split()[0] != expected["python_version"]:
        raise Invalid("PYTHON_VERSION_MISMATCH")
    executable = Path(sys.executable).resolve(strict=True)
    if file_sha256(executable) != expected["python_executable_sha256"]:
        raise Invalid("PYTHON_EXECUTABLE_MISMATCH")
    return measured


def validate_git_executable(contract, git_executable: Path):
    if git_executable != Path("/usr/bin/git"):
        raise Invalid("PINNED_SYSTEM_GIT_REQUIRED")
    if file_sha256(git_executable) != contract["runtime_binding"]["git_executable_sha256"]:
        raise Invalid("GIT_EXECUTABLE_MISMATCH")


def validate_git(contract, git_executable: Path, repo: Path):
    validate_root_git_directory(repo)
    expected = contract["git_binding"]
    head = run_git(git_executable, repo, "rev-parse", "HEAD")
    try:
        head_commit = run_git(git_executable, repo, "rev-parse", "--verify", "HEAD^{commit}")
    except Invalid as exc:
        raise Invalid("GIT_HEAD_COMMIT_REQUIRED") from exc
    if head != head_commit:
        raise Invalid("GIT_HEAD_COMMIT_REQUIRED")
    tree = run_git(git_executable, repo, "rev-parse", "HEAD^{tree}")
    assume_flags = _tracked_flag_paths(
        run_git_bytes(git_executable, repo, "ls-files", "-v", "-z"),
        "GIT_INDEX_FLAG_RECORD_INVALID",
    )
    skip_flags = _tracked_flag_paths(
        run_git_bytes(git_executable, repo, "ls-files", "-t", "-z"),
        "GIT_INDEX_FLAG_RECORD_INVALID",
    )
    if (
        set(assume_flags) != set(skip_flags)
        or any(prefix.islower() for prefix in assume_flags.values())
        or any(prefix == b"S" for prefix in skip_flags.values())
    ):
        raise Invalid("GIT_INDEX_CONCEALMENT_FLAG_REJECTED")
    tracked = validate_head_worktree_bytes(git_executable, repo)
    if (
        head != expected["head_commit_sha1"]
        or tree != expected["head_tree_sha1"]
        or tracked["tracked_files"] != expected["tracked_files"]
        or tracked["tracked_bytes"] != expected["tracked_bytes"]
        or tracked["tracked_content_sha256"] != expected["tracked_content_sha256"]
    ):
        raise Invalid("GIT_TREE_STATE_MISMATCH")
    return {
        "head_commit_sha1": head,
        "head_tree_sha1": tree,
        **tracked,
        "clean_worktree": "CONFIRMED",
    }


def validate_artifacts(contract, artifact_root: Path):
    measured = []
    physical_files = set()
    for artifact in sorted(contract["artifacts"], key=lambda item: (item["role"], item["artifact_id"], item["path"])):
        body, file_identity = read_descriptor_bound(
            artifact_root,
            artifact["path"],
            include_file_identity=True,
        )
        if file_identity in physical_files:
            raise Invalid("DUPLICATE_PHYSICAL_ARTIFACT_BINDING")
        physical_files.add(file_identity)
        if len(body) != artifact["bytes"] or sha(body) != artifact["sha256"]:
            raise Invalid("ARTIFACT_IDENTITY_MISMATCH")
        verify_assertions(body, artifact["json_assertions"])
        measured.append({
            "role": artifact["role"],
            "artifact_id": artifact["artifact_id"],
            "path": artifact["path"],
            "bytes": len(body),
            "sha256": sha(body),
            "evidence_class": artifact["evidence_class"],
        })
    return measured


def validate_live_inputs(contract, limex_root: Path, git_executable: Path, git_repo: Path, artifact_root: Path):
    """Remeasure every live input that an accepted release envelope claims to bind."""
    runtime = validate_runtime(contract, limex_root)
    validate_git_executable(contract, git_executable)
    git = validate_git(contract, git_executable, git_repo)
    artifacts = validate_artifacts(contract, artifact_root)
    return runtime, git, artifacts


def payload_sha256(payload):
    body = canonical(payload)
    return sha(DOMAIN + len(body).to_bytes(8, "big") + body)


def build_envelope(contract, contract_sha256, reservation_sha256, runtime, git, artifacts, observed_at_utc):
    payload = {
        "schema": PAYLOAD_SCHEMA,
        "priority_id": contract["priority_id"],
        "contract_sha256": contract_sha256,
        "reservation_sha256": reservation_sha256,
        "settle_at_utc": contract["settle_at_utc"],
        "settled_at_utc": observed_at_utc,
        "host_clock_evidence_class": contract["host_clock_evidence_class"],
        "execution_scope": contract["execution_scope"],
        "runtime": runtime,
        "git": git,
        "llm_interface_binding": contract["llm_interface_binding"],
        "artifacts": artifacts,
        "external_effect": "DENY",
    }
    return {"schema": ENVELOPE_SCHEMA, "payload": payload, "payload_sha256": payload_sha256(payload)}


def validate_reservation(body: bytes, contract, contract_sha256: str):
    reservation = decode(body)
    exact(reservation, ("schema", "priority_id", "contract_sha256", "reserved_at_utc"), "RESERVATION_SCHEMA_INVALID")
    if (
        reservation["schema"] != "LIMEX_SETTLE_RELEASE_SEAL_RESERVATION_V1"
        or reservation["priority_id"] != contract["priority_id"]
        or reservation["contract_sha256"] != contract_sha256
    ):
        raise Invalid("RESERVATION_BINDING_MISMATCH")
    utc_ms(reservation["reserved_at_utc"])
    if utc_ms(reservation["reserved_at_utc"]) < utc_ms(contract["settle_at_utc"]):
        raise Invalid("RESERVATION_PREMATURE")
    return reservation


def expected_measured_artifacts(contract):
    return [
        {key: artifact[key] for key in MEASURED_ARTIFACT_KEYS}
        for artifact in sorted(contract["artifacts"], key=lambda item: (item["role"], item["artifact_id"], item["path"]))
    ]


def validate_envelope(
    body: bytes,
    contract,
    contract_sha256: str,
    reservation_sha256: str,
    reserved_at_utc: str,
):
    envelope = decode(body)
    exact(envelope, ("schema", "payload", "payload_sha256"), "ENVELOPE_SCHEMA_INVALID")
    if envelope["schema"] != ENVELOPE_SCHEMA or payload_sha256(envelope["payload"]) != envelope["payload_sha256"]:
        raise Invalid("ENVELOPE_HASH_INVALID")
    payload = envelope["payload"]
    exact(payload, PAYLOAD_KEYS, "PAYLOAD_CLOSED_SCHEMA_REQUIRED")
    if (
        payload["schema"] != PAYLOAD_SCHEMA
        or payload["priority_id"] != contract["priority_id"]
        or payload["contract_sha256"] != contract_sha256
        or payload["reservation_sha256"] != reservation_sha256
        or payload["settle_at_utc"] != contract["settle_at_utc"]
        or payload["settled_at_utc"] != reserved_at_utc
        or payload["external_effect"] != "DENY"
        or payload["host_clock_evidence_class"] != contract["host_clock_evidence_class"]
        or payload["execution_scope"] != contract["execution_scope"]
        or payload["llm_interface_binding"] != contract["llm_interface_binding"]
    ):
        raise Invalid("EXISTING_RELEASE_SEAL_BINDING_MISMATCH")
    identifier(payload["priority_id"])
    digest(payload["contract_sha256"])
    utc_ms(payload["settle_at_utc"])
    utc_ms(payload["settled_at_utc"])
    if utc_ms(payload["settled_at_utc"]) < utc_ms(payload["settle_at_utc"]):
        raise Invalid("ENVELOPE_SETTLED_TIME_PREMATURE")
    exact(payload["runtime"], ("regular_files", "total_bytes", "tree_sha256", "skill_md_sha256"), "ENVELOPE_RUNTIME_SCHEMA_INVALID")
    for field in ("regular_files", "total_bytes"):
        if type(payload["runtime"][field]) is not int or payload["runtime"][field] < 1:
            raise Invalid("ENVELOPE_RUNTIME_VALUE_INVALID")
    for field in ("tree_sha256", "skill_md_sha256"):
        digest(payload["runtime"][field])
    if payload["runtime"] != {key: contract["runtime_binding"][key] for key in ("regular_files", "total_bytes", "tree_sha256", "skill_md_sha256")}:
        raise Invalid("ENVELOPE_RUNTIME_CONTRACT_MISMATCH")
    exact(payload["git"], GIT_KEYS, "ENVELOPE_GIT_SCHEMA_INVALID")
    if (
        not SHA1.fullmatch(payload["git"]["head_commit_sha1"])
        or not SHA1.fullmatch(payload["git"]["head_tree_sha1"])
        or type(payload["git"]["tracked_files"]) is not int
        or type(payload["git"]["tracked_bytes"]) is not int
        or re.fullmatch(r"[0-9a-f]{64}", payload["git"]["tracked_content_sha256"]) is None
        or payload["git"]["clean_worktree"] != "CONFIRMED"
        or payload["git"] != {**contract["git_binding"], "clean_worktree": "CONFIRMED"}
    ):
        raise Invalid("ENVELOPE_GIT_VALUE_INVALID")
    exact(payload["llm_interface_binding"], LLM_KEYS, "ENVELOPE_LLM_INTERFACE_SCHEMA_INVALID")
    digest(payload["llm_interface_binding"]["producer_runtime_sha256"])
    if (
        payload["llm_interface_binding"]["mode"]
        != "DECOUPLED_VERSIONED_ATTESTATION_INTERFACE_REQUIRED"
        or payload["llm_interface_binding"]["schema_version"]
        != "LIMEX_LLM_EXECUTION_ATTESTATION_V1"
        or payload["llm_interface_binding"]["financial_feedback_to_llm"] != "DENY"
    ):
        raise Invalid("ENVELOPE_LLM_INTERFACE_INVALID")
    artifacts = payload["artifacts"]
    if type(artifacts) is not list or len(artifacts) != len(ROLE_SET):
        raise Invalid("ENVELOPE_ARTIFACT_CARDINALITY_INVALID")
    roles = set()
    for artifact in artifacts:
        exact(artifact, MEASURED_ARTIFACT_KEYS, "ENVELOPE_ARTIFACT_SCHEMA_INVALID")
        if artifact["role"] not in ROLE_SET or artifact["role"] in roles:
            raise Invalid("ENVELOPE_ARTIFACT_ROLE_INVALID")
        roles.add(artifact["role"])
        identifier(artifact["artifact_id"])
        relative_posix_file(artifact["path"])
        if type(artifact["bytes"]) is not int or artifact["bytes"] < 1:
            raise Invalid("ENVELOPE_ARTIFACT_BYTES_INVALID")
        digest(artifact["sha256"])
        ascii_enum(artifact["evidence_class"], "ENVELOPE_EVIDENCE_CLASS_INVALID")
    if roles != ROLE_SET:
        raise Invalid("ENVELOPE_REQUIRED_ARTIFACT_ROLE_MISSING")
    if artifacts != expected_measured_artifacts(contract):
        raise Invalid("ENVELOPE_ARTIFACT_CONTRACT_MISMATCH")
    return envelope


def open_private_state_root(directory: Path):
    flags = os.O_RDONLY | getattr(os, "O_DIRECTORY", 0) | getattr(os, "O_NOFOLLOW", 0)
    descriptor = os.open(directory, flags)
    try:
        info = verify_private_fd(descriptor, directory=True, exact_mode=0o700)
        return descriptor, (info.st_dev, info.st_ino)
    except BaseException:
        os.close(descriptor)
        raise


def verify_retained_state_root(descriptor, identity):
    info = verify_private_fd(descriptor, directory=True, exact_mode=0o700)
    if (info.st_dev, info.st_ino) != identity:
        raise Invalid("STATE_ROOT_DESCRIPTOR_IDENTITY_MISMATCH")
    return info


def verify_state_root_namespace(directory: Path, identity):
    """Require the configured pathname to still address the retained object."""
    flags = os.O_RDONLY | getattr(os, "O_DIRECTORY", 0) | getattr(os, "O_NOFOLLOW", 0)
    try:
        descriptor = os.open(directory, flags)
    except OSError as exc:
        raise Invalid("STATE_ROOT_NAMESPACE_DISPLACED") from exc
    try:
        info = verify_private_fd(descriptor, directory=True, exact_mode=0o700)
        if (info.st_dev, info.st_ino) != identity:
            raise Invalid("STATE_ROOT_NAMESPACE_DISPLACED")
    finally:
        os.close(descriptor)


def _state_leaf_name(name):
    parts = relative_posix_file(name)
    if len(parts) != 1:
        raise Invalid("STATE_ENTRY_NAME_INVALID")
    return name


def state_entry_exists(directory_descriptor, name):
    name = _state_leaf_name(name)
    try:
        os.stat(name, dir_fd=directory_descriptor, follow_symlinks=False)
        return True
    except FileNotFoundError:
        return False


def _open_state_entry(directory_descriptor, name):
    name = _state_leaf_name(name)
    flags = os.O_RDONLY | getattr(os, "O_NOFOLLOW", 0) | getattr(os, "O_NONBLOCK", 0)
    return os.open(name, flags, dir_fd=directory_descriptor)


def state_entry_info(directory_descriptor, name, *, allow_links=(1,)):
    descriptor = _open_state_entry(directory_descriptor, name)
    try:
        return verify_private_fd(
            descriptor,
            directory=False,
            exact_mode=0o400,
            allow_links=allow_links,
        )
    finally:
        os.close(descriptor)


def read_state_entry(
    directory_descriptor,
    name,
    maximum_bytes=MAX_BOUND_FILE_BYTES,
    *,
    allow_links=(1,),
):
    descriptor = _open_state_entry(directory_descriptor, name)
    try:
        before = verify_private_fd(
            descriptor,
            directory=False,
            exact_mode=0o400,
            allow_links=allow_links,
        )
        if before.st_size > maximum_bytes:
            raise Invalid("BOUND_FILE_BYTE_LIMIT_EXCEEDED")
        body = bytearray()
        while True:
            chunk = os.read(descriptor, min(1024 * 1024, maximum_bytes + 1 - len(body)))
            if not chunk:
                break
            body.extend(chunk)
            if len(body) > maximum_bytes:
                raise Invalid("BOUND_FILE_BYTE_LIMIT_EXCEEDED")
        after = verify_private_fd(
            descriptor,
            directory=False,
            exact_mode=0o400,
            allow_links=allow_links,
        )
        before_identity = (
            before.st_dev,
            before.st_ino,
            before.st_mode,
            before.st_nlink,
            before.st_size,
            before.st_mtime_ns,
            before.st_ctime_ns,
        )
        after_identity = (
            after.st_dev,
            after.st_ino,
            after.st_mode,
            after.st_nlink,
            after.st_size,
            after.st_mtime_ns,
            after.st_ctime_ns,
        )
        if before_identity != after_identity or len(body) != before.st_size:
            raise Invalid("STATE_ENTRY_CHANGED_DURING_READ")
        return bytes(body)
    finally:
        os.close(descriptor)


def fsync_directory_descriptor(directory_descriptor):
    os.fsync(directory_descriptor)


def write_exclusive_state_fsync(directory_descriptor, name, body: bytes):
    name = _state_leaf_name(name)
    flags = os.O_RDWR | os.O_CREAT | os.O_EXCL | getattr(os, "O_NOFOLLOW", 0)
    descriptor = os.open(name, flags, 0o600, dir_fd=directory_descriptor)
    try:
        written = 0
        while written < len(body):
            written += os.write(descriptor, body[written:])
        os.fsync(descriptor)
        os.fchmod(descriptor, 0o400)
        os.fsync(descriptor)
        verify_private_fd(descriptor, directory=False, exact_mode=0o400)
        os.lseek(descriptor, 0, os.SEEK_SET)
        readback = bytearray()
        while True:
            chunk = os.read(descriptor, min(1024 * 1024, len(body) + 1 - len(readback)))
            if not chunk:
                break
            readback.extend(chunk)
            if len(readback) > len(body):
                raise Invalid("PERSISTED_READBACK_MISMATCH")
        if bytes(readback) != body:
            raise Invalid("PERSISTED_READBACK_MISMATCH")
    finally:
        os.close(descriptor)


def utc_now_ms():
    return datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%S.%f")[:-3] + "Z"


def terminal(state, reason, priority_id="", payload_sha="", settled_at="", count=0, exit_code=1, scope=""):
    for value in (state, reason):
        ascii_enum(value)
    return {
        "SCHEMA": TERMINAL_SCHEMA,
        "OPERATION_DOMAIN": OPERATION_DOMAIN,
        "EXECUTION_SCOPE": scope,
        "STATE": state,
        "REASON": reason,
        "PRIORITY_ID": priority_id,
        "PAYLOAD_SHA256": payload_sha,
        "SETTLED_AT_UTC": settled_at,
        "INPUT_COUNT": count,
        "EXIT_CODE": exit_code,
    }


def terminal_text(result):
    order = (
        "SCHEMA",
        "OPERATION_DOMAIN",
        "EXECUTION_SCOPE",
        "STATE",
        "REASON",
        "PRIORITY_ID",
        "PAYLOAD_SHA256",
        "SETTLED_AT_UTC",
        "INPUT_COUNT",
        "EXIT_CODE",
    )
    return "".join(f"{key}={result[key]}\n" for key in order)


def _run(config_path, *, observed_at_utc=None, fault=None):
    """Internal testable implementation; test controls are not exposed by run/CLI."""
    priority = ""
    scope = ""
    state_root_descriptor = None
    try:
        config_file = absolute_regular_file(config_path, "RUN_CONFIG_FILE_REQUIRED")
        config = decode(read_absolute_descriptor_bound(config_path, "RUN_CONFIG_READ_FAILED"))
        exact(config, RUN_KEYS, "RUN_CONFIG_CLOSED_SCHEMA_REQUIRED")
        if config["schema"] != RUN_SCHEMA:
            raise Invalid("RUN_CONFIG_SCHEMA_UNSUPPORTED")
        artifact_root = absolute_directory(config["artifact_root"], "ARTIFACT_ROOT_REQUIRED")
        state_root = absolute_directory(config["state_root"], "STATE_ROOT_REQUIRED")
        limex_root = absolute_directory(config["limex_root"], "LIMEX_ROOT_REQUIRED")
        git_repo = absolute_directory(config["git_repo_root"], "GIT_REPO_ROOT_REQUIRED")
        git_executable = absolute_regular_file(config["git_executable"], "GIT_EXECUTABLE_REQUIRED")
        contract_file = absolute_regular_file(config["contract_path"], "CONTRACT_FILE_REQUIRED")
        require_disjoint(artifact_root, state_root)
        state_root_descriptor, state_root_identity = open_private_state_root(state_root)
        verify_state_root_namespace(state_root, state_root_identity)
        contract_body = read_absolute_descriptor_bound(config["contract_path"], "CONTRACT_READ_FAILED")
        contract = validate_contract(decode(contract_body))
        priority = contract["priority_id"]
        scope = contract["execution_scope"]
        contract_hash = sha(contract_body)
        final_name = f"{priority}.release-sealed.json"
        lock_name = f".{priority}.lock"
        stage_name = f".{priority}.staged.json"
        now = observed_at_utc if observed_at_utc is not None else utc_now_ms()
        utc_ms(now)

        if state_entry_exists(state_root_descriptor, final_name):
            if not state_entry_exists(state_root_descriptor, lock_name):
                raise Invalid("RELEASE_SEAL_RESERVATION_MISSING")
            state_entry_info(state_root_descriptor, lock_name)
            state_entry_info(state_root_descriptor, final_name, allow_links=(1, 2))
            if state_entry_exists(state_root_descriptor, stage_name):
                final_info = state_entry_info(state_root_descriptor, final_name, allow_links=(2,))
                stage_info = state_entry_info(state_root_descriptor, stage_name, allow_links=(2,))
                if (final_info.st_dev, final_info.st_ino) != (stage_info.st_dev, stage_info.st_ino):
                    raise Invalid("RELEASE_SEAL_STAGE_FINAL_IDENTITY_MISMATCH")
            if utc_ms(now) < utc_ms(contract["settle_at_utc"]):
                raise Invalid("EXISTING_STATE_BEFORE_SETTLE_TIME")
            reservation_body = read_state_entry(state_root_descriptor, lock_name)
            reservation = validate_reservation(reservation_body, contract, contract_hash)
            if utc_ms(reservation["reserved_at_utc"]) > utc_ms(now):
                raise Invalid("RESERVATION_TIME_AFTER_TRUSTED_OBSERVATION")
            envelope = validate_envelope(
                read_state_entry(
                    state_root_descriptor,
                    final_name,
                    allow_links=(1, 2),
                ),
                contract,
                contract_hash,
                sha(reservation_body),
                reservation["reserved_at_utc"],
            )
            runtime, git, artifacts = validate_live_inputs(
                contract,
                limex_root,
                git_executable,
                git_repo,
                artifact_root,
            )
            measured_runtime = {
                key: runtime[key]
                for key in ("regular_files", "total_bytes", "tree_sha256", "skill_md_sha256")
            }
            if (
                envelope["payload"]["runtime"] != measured_runtime
                or envelope["payload"]["git"] != git
                or envelope["payload"]["artifacts"] != artifacts
            ):
                raise Invalid("EXISTING_ENVELOPE_LIVE_INPUT_MISMATCH")
            verify_retained_state_root(state_root_descriptor, state_root_identity)
            verify_state_root_namespace(state_root, state_root_identity)
            return terminal(
                "ALREADY_SETTLED",
                "VALID_EXISTING_ENVELOPE",
                priority,
                envelope["payload_sha256"],
                envelope["payload"]["settled_at_utc"],
                len(envelope["payload"]["artifacts"]),
                0,
                scope,
            )

        if state_entry_exists(state_root_descriptor, lock_name):
            state_entry_info(state_root_descriptor, lock_name)
            if utc_ms(now) < utc_ms(contract["settle_at_utc"]):
                raise Invalid("EXISTING_STATE_BEFORE_SETTLE_TIME")
            reservation_body = read_state_entry(state_root_descriptor, lock_name)
            reservation = validate_reservation(reservation_body, contract, contract_hash)
            if utc_ms(reservation["reserved_at_utc"]) > utc_ms(now):
                raise Invalid("RESERVATION_TIME_AFTER_TRUSTED_OBSERVATION")
            reserved_at = reservation["reserved_at_utc"]
        else:
            if utc_ms(now) < utc_ms(contract["settle_at_utc"]):
                verify_retained_state_root(state_root_descriptor, state_root_identity)
                return terminal("NOT_DUE", "SETTLE_TIME_NOT_REACHED", priority, exit_code=2, scope=scope)
            reserved_at = now
            reservation_body = canonical({
                "schema": "LIMEX_SETTLE_RELEASE_SEAL_RESERVATION_V1",
                "priority_id": priority,
                "contract_sha256": contract_hash,
                "reserved_at_utc": reserved_at,
            })
            verify_state_root_namespace(state_root, state_root_identity)
            write_exclusive_state_fsync(state_root_descriptor, lock_name, reservation_body)
            fsync_directory_descriptor(state_root_descriptor)
            if fault == "AFTER_LOCK":
                raise Invalid("INJECTED_AFTER_LOCK")

        runtime, git, artifacts = validate_live_inputs(
            contract,
            limex_root,
            git_executable,
            git_repo,
            artifact_root,
        )
        if fault == "AFTER_VALIDATION":
            raise Invalid("INJECTED_AFTER_VALIDATION")
        envelope = build_envelope(contract, contract_hash, sha(reservation_body), runtime, git, artifacts, reserved_at)
        envelope_body = canonical(envelope)
        if state_entry_exists(state_root_descriptor, stage_name):
            state_entry_info(state_root_descriptor, stage_name)
            staged_body = read_state_entry(state_root_descriptor, stage_name)
            if staged_body != envelope_body:
                raise Invalid("RELEASE_SEAL_STAGE_BINDING_MISMATCH")
            validate_envelope(
                staged_body,
                contract,
                contract_hash,
                sha(reservation_body),
                reserved_at,
            )
        else:
            verify_state_root_namespace(state_root, state_root_identity)
            write_exclusive_state_fsync(state_root_descriptor, stage_name, envelope_body)
            if fault == "AFTER_STAGE_FSYNC":
                raise Invalid("INJECTED_AFTER_STAGE_FSYNC")
        verify_state_root_namespace(state_root, state_root_identity)
        try:
            os.link(
                stage_name,
                final_name,
                src_dir_fd=state_root_descriptor,
                dst_dir_fd=state_root_descriptor,
                follow_symlinks=False,
            )
        except FileExistsError as exc:
            raise Invalid("FINAL_RELEASE_SEAL_NO_CLOBBER_COLLISION") from exc
        fsync_directory_descriptor(state_root_descriptor)
        if fault == "AFTER_PUBLISH":
            raise Invalid("INJECTED_AFTER_PUBLISH")
        accepted = validate_envelope(
            read_state_entry(state_root_descriptor, final_name, allow_links=(2,)),
            contract,
            contract_hash,
            sha(reservation_body),
            reserved_at,
        )
        verify_retained_state_root(state_root_descriptor, state_root_identity)
        verify_state_root_namespace(state_root, state_root_identity)
        return terminal(
            "SETTLED",
            "LOCAL_ENVELOPE_PUBLISHED_AND_READ_BACK",
            priority,
            accepted["payload_sha256"],
            accepted["payload"]["settled_at_utc"],
            len(accepted["payload"]["artifacts"]),
            0,
            scope,
        )
    except FileExistsError:
        return terminal("CORRUPTED_HALT", "EXCLUSIVE_STATE_COLLISION", priority, exit_code=1, scope=scope)
    except Invalid as exc:
        return terminal("CORRUPTED_HALT", str(exc), priority, exit_code=1, scope=scope)
    except (OSError, subprocess.SubprocessError) as exc:
        suffix = getattr(exc, "errno", None)
        reason = f"OS_ERROR_{suffix}" if type(suffix) is int else "RUNTIME_IO_FAILURE"
        return terminal("CORRUPTED_HALT", reason, priority, exit_code=1, scope=scope)
    except BaseException:
        return terminal("CORRUPTED_HALT", "UNEXPECTED_RUNTIME_FAILURE", priority, exit_code=1, scope=scope)
    finally:
        if state_root_descriptor is not None:
            try:
                os.close(state_root_descriptor)
            except OSError:
                pass


def run(config_path):
    """Production API: exactly one config path and no injectable clock/fault port."""
    return _run(config_path)


def main(argv=None):
    arguments = list(sys.argv[1:] if argv is None else argv)
    if len(arguments) != 1:
        result = terminal("CORRUPTED_HALT", "EXACTLY_ONE_RUN_CONFIG_PATH_REQUIRED", exit_code=1)
    else:
        result = run(arguments[0])
    sys.stdout.write(terminal_text(result))
    return result["EXIT_CODE"]


if __name__ == "__main__":
    raise SystemExit(main())
