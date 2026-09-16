"""Cleanroom C5 reference implementation. No network or execution authority.

This is not an installed runtime. Only local SQLite measurement and diagnostic
state is persisted. External outcomes are projections over supplied
observations, never authenticated rail evidence.
"""
from __future__ import annotations

import bisect
import ctypes
import hashlib
import json
import os
import re
import sqlite3
import stat
import sys
from contextlib import contextmanager
from datetime import datetime, timezone
from pathlib import Path

VERSION = "LIMEX_C5_LOCAL_CANDIDATE_V1"
MAX_INT = 2**53 - 1
MAX_LEAVES = 4096
MAX_LEDGER_PAGES_DEFAULT = 32_768
MAX_LEDGER_ROWS_PER_TABLE_DEFAULT = 100_000
MAX_EVENT_QUERY_ROWS = 4_096
HASH = re.compile(r"[0-9a-f]{64}\Z")
ID = re.compile(r"[A-Za-z0-9][A-Za-z0-9_.:-]{0,127}\Z")
UTC = re.compile(r"\d{4}-\d\d-\d\dT\d\d:\d\d:\d\d\.\d{3}Z\Z")


class Invalid(ValueError):
    pass


def _acl_library():
    if sys.platform != "darwin":
        raise Invalid("ACL_INSPECTION_UNAVAILABLE")
    libc = ctypes.CDLL(None, use_errno=True)
    acl_get_entry = libc.acl_get_entry
    acl_get_entry.argtypes = (ctypes.c_void_p, ctypes.c_int, ctypes.POINTER(ctypes.c_void_p))
    acl_get_entry.restype = ctypes.c_int
    acl_get_tag_type = libc.acl_get_tag_type
    acl_get_tag_type.argtypes = (ctypes.c_void_p, ctypes.POINTER(ctypes.c_int))
    acl_get_tag_type.restype = ctypes.c_int
    acl_free = libc.acl_free
    acl_free.argtypes = (ctypes.c_void_p,)
    acl_free.restype = ctypes.c_int
    return libc


def _reject_allow_acl_entries(libc, acl, reason):
    """Reject every macOS extended ALLOW ACL entry in one acquired ACL."""
    acl_get_entry = libc.acl_get_entry
    acl_get_tag_type = libc.acl_get_tag_type
    acl_free = libc.acl_free
    try:
        entry = ctypes.c_void_p()
        selector = 0
        while True:
            result = acl_get_entry(acl, selector, ctypes.byref(entry))
            selector = -1
            if result == 1:
                break
            if result != 0:
                raise Invalid(reason)
            tag = ctypes.c_int()
            if acl_get_tag_type(entry, ctypes.byref(tag)) != 0:
                raise Invalid(reason)
            if tag.value == 1:
                raise Invalid("LEDGER_STORAGE_ALLOW_ACL_REJECTED")
    finally:
        acl_free(acl)


def _reject_extended_allow_acl(path, reason):
    """Fail closed on macOS when any extended ALLOW ACL entry is present."""
    libc = _acl_library()
    acl_get_file = libc.acl_get_file
    acl_get_file.argtypes = (ctypes.c_char_p, ctypes.c_int)
    acl_get_file.restype = ctypes.c_void_p
    ctypes.set_errno(0)
    acl = acl_get_file(os.fsencode(path), 0x00000100)
    if not acl:
        if ctypes.get_errno() == 2:  # ENOENT: no extended ACL is attached.
            return
        raise Invalid(reason)
    _reject_allow_acl_entries(libc, acl, reason)


def _reject_extended_allow_acl_fd(descriptor, reason):
    """Descriptor-bound macOS ACL inspection for retained trust roots/files."""
    libc = _acl_library()
    try:
        acl_get_fd_np = libc.acl_get_fd_np
    except AttributeError as exc:
        raise Invalid("ACL_INSPECTION_UNAVAILABLE") from exc
    acl_get_fd_np.argtypes = (ctypes.c_int, ctypes.c_int)
    acl_get_fd_np.restype = ctypes.c_void_p
    ctypes.set_errno(0)
    acl = acl_get_fd_np(descriptor, 0x00000100)
    if not acl:
        if ctypes.get_errno() == 2:  # ENOENT: no extended ACL is attached.
            return
        raise Invalid(reason)
    _reject_allow_acl_entries(libc, acl, reason)


def verify_private_fd(descriptor, *, directory, exact_mode, allow_links=(1,)):
    """Verify an already-open owner-only object without returning to its path."""
    try:
        info = os.fstat(descriptor)
    except OSError as exc:
        raise Invalid("LEDGER_STORAGE_STAT_FAILED") from exc
    expected_kind = stat.S_ISDIR if directory else stat.S_ISREG
    if not expected_kind(info.st_mode):
        raise Invalid("LEDGER_STORAGE_KIND_INVALID")
    get_euid = getattr(os, "geteuid", None)
    if get_euid is None or info.st_uid != get_euid():
        raise Invalid("LEDGER_STORAGE_OWNER_MISMATCH")
    if stat.S_IMODE(info.st_mode) != exact_mode:
        raise Invalid("LEDGER_STORAGE_PERMISSIONS_TOO_BROAD")
    if not directory and info.st_nlink not in allow_links:
        raise Invalid("LEDGER_STORAGE_LINK_COUNT_INVALID")
    _reject_extended_allow_acl_fd(descriptor, "LEDGER_ACL_INSPECTION_FAILED")
    return info


def verify_private_path(path, *, directory, exact_mode, allow_links=(1,)):
    """Verify an owner-only path used as a local trust boundary."""
    path = Path(path)
    try:
        info = path.lstat()
    except OSError as exc:
        raise Invalid("LEDGER_STORAGE_STAT_FAILED") from exc
    expected_kind = stat.S_ISDIR if directory else stat.S_ISREG
    if path.is_symlink() or not expected_kind(info.st_mode):
        raise Invalid("LEDGER_STORAGE_KIND_INVALID")
    get_euid = getattr(os, "geteuid", None)
    if get_euid is None or info.st_uid != get_euid():
        raise Invalid("LEDGER_STORAGE_OWNER_MISMATCH")
    if stat.S_IMODE(info.st_mode) != exact_mode:
        raise Invalid("LEDGER_STORAGE_PERMISSIONS_TOO_BROAD")
    if not directory and info.st_nlink not in allow_links:
        raise Invalid("LEDGER_STORAGE_LINK_COUNT_INVALID")
    _reject_extended_allow_acl(path, "LEDGER_ACL_INSPECTION_FAILED")
    return info


def exact(value, keys):
    if type(value) is not dict or set(value) != set(keys):
        raise Invalid("CLOSED_SCHEMA_REQUIRED")


def integer(value, minimum=0, maximum=MAX_INT):
    if type(value) is not int or not minimum <= value <= maximum:
        raise Invalid("INTEGER_DOMAIN")
    return value


def identifier(value):
    if type(value) is not str or not ID.fullmatch(value):
        raise Invalid("IDENTIFIER_DOMAIN")
    return value


def digest(value):
    if type(value) is not str or not HASH.fullmatch(value):
        raise Invalid("SHA256_DOMAIN")
    return value


def canonical(value):
    """C5_ASCII_JSON_V1: sorted ASCII keys; UTF-8 strings; no floats/null.

    Integers bounded to +/- (2**53-1), no booleans, no surrogates. No Unicode
    normalization: composed/decomposed text is intentionally byte-distinct.
    Domain is narrower than JCS and does not claim RFC8785 conformance.
    """
    def check(v, depth=0):
        if depth > 16:
            raise Invalid("JSON_DEPTH")
        if type(v) is int:
            integer(v, -MAX_INT)
        elif type(v) is str:
            try:
                if len(v.encode("utf-8")) > 65536:
                    raise Invalid("STRING_BOUND")
            except UnicodeEncodeError as exc:
                raise Invalid("INVALID_UNICODE") from exc
        elif type(v) is list:
            if len(v) > MAX_LEAVES:
                raise Invalid("ARRAY_BOUND")
            for x in v:
                check(x, depth + 1)
        elif type(v) is dict:
            if len(v) > 64 or any(type(k) is not str or not k.isascii() for k in v):
                raise Invalid("ASCII_KEYS_REQUIRED")
            for x in v.values():
                check(x, depth + 1)
        else:
            raise Invalid("JSON_TYPE")
    check(value)
    body = json.dumps(value, sort_keys=True, ensure_ascii=False, separators=(",", ":"), allow_nan=False).encode("utf-8")
    if len(body) > 4_194_304:
        raise Invalid("JSON_BYTE_BOUND")
    return body


def decode(body):
    if type(body) is not bytes or len(body) > 4_194_304:
        raise Invalid("CODEC_BYTES")
    def pairs(items):
        result = {}
        for k, v in items:
            if k in result:
                raise Invalid("DUPLICATE_JSON_KEY")
            result[k] = v
        return result
    try:
        value = json.loads(body.decode("utf-8"), object_pairs_hook=pairs)
    except (UnicodeError, json.JSONDecodeError) as exc:
        raise Invalid("INVALID_JSON") from exc
    if canonical(value) != body:
        raise Invalid("NONCANONICAL_JSON")
    return value


def sha(body):
    return hashlib.sha256(body).hexdigest()


def utc_ms(value):
    if type(value) is not str or not UTC.fullmatch(value):
        raise Invalid("CANONICAL_UTC_MILLISECOND_REQUIRED")
    try:
        parsed = datetime.strptime(value, "%Y-%m-%dT%H:%M:%S.%fZ").replace(tzinfo=timezone.utc)
    except ValueError as exc:
        raise Invalid("UTC_CALENDAR") from exc
    delta = parsed - datetime(1970, 1, 1, tzinfo=timezone.utc)
    return delta.days * 86_400_000 + delta.seconds * 1000 + delta.microseconds // 1000


EVENT_KEYS = ("schema", "tenant", "event_id", "measurement", "epoch", "unit", "quantity", "event_time", "execution_receipt_sha256", "custody_receipt_sha256", "evidence_class", "correction_of")
LLM_ATTESTATION_KEYS = (
    "schema",
    "tenant",
    "event_id",
    "measurement",
    "epoch",
    "unit",
    "quantity",
    "event_time",
    "execution_receipt_sha256",
    "custody_receipt_sha256",
    "producer_runtime_sha256",
    "evidence_class",
)


def event_bytes(event):
    exact(event, EVENT_KEYS)
    if event["schema"] != "C5_EVENT_V1" or event["evidence_class"] != "UNATTESTED_REFERENCE":
        raise Invalid("UNATTESTED_INPUT_CLASS_REQUIRED")
    for field in ("tenant", "event_id", "measurement", "unit"):
        identifier(event[field])
    integer(event["epoch"])
    integer(event["quantity"])
    utc_ms(event["event_time"])
    digest(event["execution_receipt_sha256"])
    digest(event["custody_receipt_sha256"])
    if event["correction_of"] != "":
        identifier(event["correction_of"])
        if event["correction_of"] == event["event_id"]:
            raise Invalid("SELF_CORRECTION")
    body = canonical(event)
    if len(body) > 65536:
        raise Invalid("EVENT_BYTE_BOUND")
    return body


def event_key(event):
    event_bytes(event)
    return (event["tenant"], event["event_id"], event["measurement"], event["epoch"])


def llm_attestation_bytes(attestation, expected_producer_runtime_sha256):
    """Validate a byte-bound but unauthenticated LIMEX LLM usage reference.

    This is intentionally not a signature verifier.  The evidence ceiling stays
    UNATTESTED_REFERENCE.  The expected producer runtime must be supplied by the
    caller's separately bound contract.
    """
    exact(attestation, LLM_ATTESTATION_KEYS)
    if attestation["schema"] != "LIMEX_LLM_EXECUTION_ATTESTATION_V1":
        raise Invalid("LLM_ATTESTATION_SCHEMA_UNSUPPORTED")
    if attestation["evidence_class"] != "UNATTESTED_REFERENCE":
        raise Invalid("LLM_ATTESTATION_EVIDENCE_ESCALATION_REJECTED")
    for field in ("tenant", "event_id", "measurement", "unit"):
        identifier(attestation[field])
    integer(attestation["epoch"])
    integer(attestation["quantity"])
    utc_ms(attestation["event_time"])
    for field in ("execution_receipt_sha256", "custody_receipt_sha256", "producer_runtime_sha256"):
        digest(attestation[field])
    digest(expected_producer_runtime_sha256)
    if attestation["producer_runtime_sha256"] != expected_producer_runtime_sha256:
        raise Invalid("LLM_PRODUCER_RUNTIME_BINDING_MISMATCH")
    return canonical(attestation)


def decode_llm_attestation(body, expected_producer_runtime_sha256):
    """Decode the wire representation without duplicate-key normalization."""
    attestation = decode(body)
    llm_attestation_bytes(attestation, expected_producer_runtime_sha256)
    return attestation


def llm_attestation_to_event(attestation, expected_producer_runtime_sha256):
    """Adapt one LLM reference into a C5 event without adding authority.

    The C5 custody hash is the hash of the complete canonical source
    attestation, thereby retaining the producer-runtime and upstream-custody
    binding transitively.  The upstream execution receipt remains explicit.
    """
    source = llm_attestation_bytes(attestation, expected_producer_runtime_sha256)
    event = {
        "schema": "C5_EVENT_V1",
        "tenant": attestation["tenant"],
        "event_id": attestation["event_id"],
        "measurement": attestation["measurement"],
        "epoch": attestation["epoch"],
        "unit": attestation["unit"],
        "quantity": attestation["quantity"],
        "event_time": attestation["event_time"],
        "execution_receipt_sha256": attestation["execution_receipt_sha256"],
        "custody_receipt_sha256": sha(source),
        "evidence_class": "UNATTESTED_REFERENCE",
        "correction_of": "",
    }
    event_bytes(event)
    return event


def leaf(body):
    return hashlib.sha256(b"\x00" + len(body).to_bytes(8, "big") + body).digest()


def node(left, right):
    return hashlib.sha256(b"\x01" + left + right).digest()


def root_commit(count, top):
    return sha(b"\x02" + count.to_bytes(8, "big") + top)


class MerkleBatch:
    """Binary ordered tree, odd-last duplication, count-bound root.

    Input order is sorted unique canonical event keys. Batch caller must bind
    root and metadata to a trusted outside anchor; membership alone is not truth.
    """
    def __init__(self, events):
        if type(events) is not list or len(events) > MAX_LEAVES:
            raise Invalid("BATCH_BOUND")
        ordered = sorted((event_key(e), event_bytes(e)) for e in events)
        if len({key for key, _ in ordered}) != len(ordered):
            raise Invalid("DUPLICATE_EVENT_KEY")
        self.keys = tuple(key for key, _ in ordered)
        self.bodies = tuple(body for _, body in ordered)
        levels = [[leaf(body) for body in self.bodies]]
        while len(levels[-1]) > 1:
            current = levels[-1]
            levels.append([node(current[i], current[min(i + 1, len(current) - 1)]) for i in range(0, len(current), 2)])
        self.levels = tuple(tuple(level) for level in levels)
        self.root = root_commit(len(self.bodies), self.levels[-1][0] if self.bodies else b"")

    def proof(self, index):
        integer(index, 0, len(self.bodies) - 1)
        position = index
        path = []
        for level in self.levels[:-1]:
            sibling = position ^ 1
            path.append({"side": "LEFT" if position & 1 else "RIGHT", "sha256": level[min(sibling, len(level) - 1)].hex()})
            position //= 2
        return {"schema": "C5_BINARY_MERKLE_PROOF_V1", "count": len(self.bodies), "index": index, "root": self.root, "leaf_sha256": leaf(self.bodies[index]).hex(), "siblings": path}


def verify_proof(event, proof, expected_root):
    """Fail-closed for malformed input. expected_root must be independently bound."""
    try:
        digest(expected_root)
        exact(proof, ("schema", "count", "index", "root", "leaf_sha256", "siblings"))
        if proof["schema"] != "C5_BINARY_MERKLE_PROOF_V1" or proof["root"] != expected_root:
            return False
        count = integer(proof["count"], 1, MAX_LEAVES)
        position = integer(proof["index"], 0, count - 1)
        current = leaf(event_bytes(event))
        if current.hex() != digest(proof["leaf_sha256"]) or type(proof["siblings"]) is not list:
            return False
        width = count
        for item in proof["siblings"]:
            if width <= 1:
                return False
            exact(item, ("side", "sha256"))
            sibling = bytes.fromhex(digest(item["sha256"]))
            if item["side"] != ("LEFT" if position & 1 else "RIGHT"):
                return False
            if not position & 1 and position + 1 == width and sibling != current:
                return False
            current = node(sibling, current) if position & 1 else node(current, sibling)
            width = (width + 1) // 2
            position //= 2
        return width == 1 and root_commit(count, current) == expected_root
    except (Invalid, TypeError, ValueError, OverflowError):
        return False


class IntervalIndex:
    """Immutable per-scope snapshot; nonoverlap validated before any lookup.

    O(n log n) construction, O(log n) bisect lookup; gaps yield None. Concurrent
    readers keep their object snapshot. Publishing a new snapshot is external.
    """
    def __init__(self, scope, rules):
        self.scope = identifier(scope)
        if type(rules) is not list or not 1 <= len(rules) <= 100_000:
            raise Invalid("RULE_COUNT")
        rows = []
        ids = set()
        for rule in rules:
            exact(rule, ("rule_id", "valid_from", "valid_to"))
            rid = identifier(rule["rule_id"])
            start, end = utc_ms(rule["valid_from"]), utc_ms(rule["valid_to"])
            if start >= end or rid in ids:
                raise Invalid("RULE_INTERVAL_OR_ID")
            ids.add(rid)
            rows.append((start, end, rid))
        rows.sort()
        if any(a[1] > b[0] for a, b in zip(rows, rows[1:])):
            raise Invalid("RULE_OVERLAP")
        self.rows = tuple(rows)
        self.starts = tuple(row[0] for row in rows)
        # All indexed content is bound without mutable original input aliases.
        self.sha256 = sha(canonical({"schema": "C5_INTERVAL_SNAPSHOT_V1", "scope": scope, "rows": [list(r) for r in rows]})) if len(rows) <= MAX_LEAVES else sha(b"C5_INTERVAL_SNAPSHOT_V1\0" + scope.encode("ascii") + b"\0" + b"\n".join(canonical(list(r)) for r in rows))
        self._frozen = True

    def __setattr__(self, key, value):
        if getattr(self, "_frozen", False):
            raise AttributeError("IMMUTABLE_INTERVAL_SNAPSHOT")
        object.__setattr__(self, key, value)

    def lookup(self, scope, timestamp):
        if scope != self.scope:
            raise Invalid("RULE_SCOPE_MISMATCH")
        instant = utc_ms(timestamp)
        index = bisect.bisect_right(self.starts, instant) - 1
        if index >= 0 and instant < self.rows[index][1]:
            return self.rows[index][2]
        return None


def build_batch_record(events, rule_index, cutoff):
    boundary = utc_ms(cutoff)
    tree = MerkleBatch(events)
    bindings = []
    for body in tree.bodies:
        event = decode(body)
        if utc_ms(event["event_time"]) >= boundary:
            raise Invalid("EVENT_AT_OR_AFTER_CUTOFF")
        rule = rule_index.lookup(event["measurement"], event["event_time"])
        if rule is None:
            raise Invalid("EVENT_RULE_GAP")
        bindings.append({"key": list(event_key(event)), "event_sha256": sha(body), "rule_id": rule})
    manifest = {"schema": "C5_BATCH_MANIFEST_V1", "event_root": tree.root, "count": len(tree.bodies), "cutoff_exclusive": cutoff, "rule_snapshot_sha256": rule_index.sha256, "bindings": bindings, "evidence_class": "LOCAL_CANDIDATE_ONLY"}
    return {"manifest": manifest, "batch_commitment": sha(b"C5_BATCH_MANIFEST_V1\0" + canonical(manifest))}


SIGNALS = {"RESERVE", "RECORD_SEND_ATTEMPT", "PENDING", "TIMEOUT", "TRANSPORT_ERROR", "CRASH_AFTER_SEND", "UNKNOWN_READBACK", "COMMITTED", "KNOWN_NOT_COMMITTED", "CONTRADICTORY", "REVERSED", "DISPUTED"}


def initial_disposition():
    return {"local_phase": "AVAILABLE", "projected_outcome": "UNOBSERVED", "capability_phase": "UNRESERVED", "retry": "NO_AUTOMATIC_RETRY"}


def project_transition(state, signal, elapsed_ms, timeout_ms):
    exact(state, ("local_phase", "projected_outcome", "capability_phase", "retry"))
    integer(elapsed_ms)
    integer(timeout_ms, 1, 86_400_000)
    if signal not in SIGNALS:
        raise Invalid("SIGNAL_UNKNOWN")
    valid = {("AVAILABLE", "UNOBSERVED", "UNRESERVED"), ("RESERVED", "UNOBSERVED", "RESERVED")}
    valid |= {("SENT", outcome, "RESERVED") for outcome in ("UNOBSERVED", "PENDING", "UNKNOWN_EFFECT", "KNOWN_NOT_COMMITTED")}
    valid |= {("SENT", outcome, "CONSUMED_PROJECTED") for outcome in ("COMMITTED", "REVERSED", "DISPUTED")}
    valid |= {("SENT", "UNKNOWN_EFFECT", "CONSUMED_PROJECTED")}
    if (state["local_phase"], state["projected_outcome"], state["capability_phase"]) not in valid or state["retry"] != "NO_AUTOMATIC_RETRY":
        raise Invalid("STATE_INVALID")
    result = dict(state)
    phase, prior = state["local_phase"], state["projected_outcome"]
    if signal == "RESERVE":
        if phase != "AVAILABLE":
            raise Invalid("ALREADY_RESERVED")
        result.update(local_phase="RESERVED", capability_phase="RESERVED")
    elif signal == "RECORD_SEND_ATTEMPT":
        if phase != "RESERVED":
            raise Invalid("SEND_NOT_ELIGIBLE")
        result["local_phase"] = "SENT"
    elif phase != "SENT":
        raise Invalid("READBACK_WITHOUT_SEND")
    elif signal in {"REVERSED", "DISPUTED"}:
        if prior not in {"COMMITTED", signal}:
            raise Invalid("NO_COMMIT_FOR_REVERSAL")
        result["projected_outcome"] = signal
    elif signal == "TIMEOUT" and elapsed_ms < timeout_ms:
        raise Invalid("TIMEOUT_NOT_REACHED")
    elif signal in {"TIMEOUT", "TRANSPORT_ERROR", "CRASH_AFTER_SEND", "UNKNOWN_READBACK"}:
        if prior not in {"COMMITTED", "REVERSED", "DISPUTED", "KNOWN_NOT_COMMITTED"}:
            result["projected_outcome"] = "UNKNOWN_EFFECT"
    elif signal == "CONTRADICTORY":
        result["projected_outcome"] = "UNKNOWN_EFFECT"
    elif signal == "PENDING":
        if prior in {"UNOBSERVED", "PENDING"}:
            result["projected_outcome"] = "PENDING"
    elif signal in {"COMMITTED", "KNOWN_NOT_COMMITTED"}:
        if (signal == "KNOWN_NOT_COMMITTED" and state["capability_phase"] == "CONSUMED_PROJECTED") or (prior in {"COMMITTED", "KNOWN_NOT_COMMITTED", "REVERSED", "DISPUTED"} and prior != signal):
            result["projected_outcome"] = "UNKNOWN_EFFECT"
        else:
            result["projected_outcome"] = signal
            if signal == "COMMITTED":
                result["capability_phase"] = "CONSUMED_PROJECTED"
    return result


def adapter_contract(adapter_id, timeout_ms):
    identifier(adapter_id)
    integer(timeout_ms, 1, 86_400_000)
    return {"schema": "C5_OFFLINE_ADAPTER_CONTRACT_V1", "adapter_id": adapter_id, "timeout_ms": timeout_ms, "transport": "NONE", "provider_binding": "UNBOUND", "evidence_class": "LOCAL_CANDIDATE_ONLY", "external_effect": "DENY", "automatic_retry": "DENY"}


class LocalLedger:
    """One local SQLite file, WAL + synchronous FULL, one writer transaction.

    No multi-node ownership, no live dispatch, no claim of power-loss safety on
    untested filesystems. Append-only triggers protect normal SQL, not a hostile
    DB owner able to drop triggers. Bounded busy timeout; no automatic retry.
    """
    def __init__(
        self,
        db_path,
        *,
        initialize=False,
        max_pages=MAX_LEDGER_PAGES_DEFAULT,
        max_rows_per_table=MAX_LEDGER_ROWS_PER_TABLE_DEFAULT,
        max_query_rows=MAX_EVENT_QUERY_ROWS,
    ):
        self.path = Path(db_path).absolute()
        integer(max_pages, 64, 1_048_576)
        integer(max_rows_per_table, 1, 10_000_000)
        integer(max_query_rows, 1, MAX_EVENT_QUERY_ROWS)
        self.max_pages = max_pages
        self.max_rows_per_table = max_rows_per_table
        self.max_query_rows = max_query_rows
        if (
            self.path.parent.resolve() != self.path.parent
            or not self.path.parent.is_dir()
            or self.path.is_symlink()
            or (self.path.exists() and not self.path.is_file())
            or (not initialize and not self.path.is_file())
        ):
            raise Invalid("DB_PATH")
        self._verify_owner_mode(self.path.parent, directory=True)
        if initialize:
            if self.path.exists():
                raise Invalid("DB_ALREADY_EXISTS")
            flags = os.O_RDWR | os.O_CREAT | os.O_EXCL | getattr(os, "O_NOFOLLOW", 0)
            descriptor = os.open(self.path, flags, 0o600)
            try:
                os.fchmod(descriptor, 0o600)
                os.fsync(descriptor)
            finally:
                os.close(descriptor)
        self._verify_owner_mode(self.path, directory=False)
        mode = "rw"
        uri = self.path.as_uri() + f"?mode={mode}&nofollow=1"
        try:
            self.db = sqlite3.connect(uri, timeout=2.5, isolation_level=None, uri=True)
        except sqlite3.OperationalError as exc:
            raise Invalid("DB_OPEN_NOFOLLOW_FAILED") from exc
        self.db.execute("PRAGMA foreign_keys=ON")
        self.db.execute("PRAGMA busy_timeout=2500")
        self.db.execute("PRAGMA synchronous=FULL")
        self.db.execute(f"PRAGMA max_page_count={self.max_pages}")
        if self.db.execute("PRAGMA page_count").fetchone()[0] > self.max_pages:
            self.close()
            raise Invalid("LEDGER_PAGE_QUOTA_EXCEEDED")
        if initialize:
            self.db.execute("PRAGMA journal_mode=WAL")
            self.db.executescript("""
            CREATE TABLE IF NOT EXISTS events(tenant TEXT NOT NULL,event_id TEXT NOT NULL,measurement TEXT NOT NULL,epoch INTEGER NOT NULL,payload BLOB NOT NULL,payload_sha TEXT NOT NULL,quantity INTEGER NOT NULL,PRIMARY KEY(tenant,event_id,measurement,epoch));
            CREATE TABLE IF NOT EXISTS conflicts(id INTEGER PRIMARY KEY,event_key BLOB NOT NULL,original_sha TEXT NOT NULL,incoming_sha TEXT NOT NULL,UNIQUE(event_key,incoming_sha));
            CREATE TABLE IF NOT EXISTS dispositions(id TEXT PRIMARY KEY,root TEXT NOT NULL,adapter TEXT NOT NULL,idem TEXT NOT NULL UNIQUE,timeout_ms INTEGER NOT NULL,state BLOB NOT NULL);
            CREATE TABLE IF NOT EXISTS disposition_events(id INTEGER PRIMARY KEY,disposition_id TEXT NOT NULL REFERENCES dispositions(id),signal TEXT NOT NULL,observation BLOB NOT NULL,state BLOB NOT NULL);
            CREATE TRIGGER IF NOT EXISTS events_no_update BEFORE UPDATE ON events BEGIN SELECT RAISE(ABORT,'APPEND_ONLY'); END;
            CREATE TRIGGER IF NOT EXISTS events_no_delete BEFORE DELETE ON events BEGIN SELECT RAISE(ABORT,'APPEND_ONLY'); END;
            CREATE TRIGGER IF NOT EXISTS conflicts_no_update BEFORE UPDATE ON conflicts BEGIN SELECT RAISE(ABORT,'APPEND_ONLY'); END;
            CREATE TRIGGER IF NOT EXISTS conflicts_no_delete BEFORE DELETE ON conflicts BEGIN SELECT RAISE(ABORT,'APPEND_ONLY'); END;
            CREATE TRIGGER IF NOT EXISTS history_no_update BEFORE UPDATE ON disposition_events BEGIN SELECT RAISE(ABORT,'APPEND_ONLY'); END;
            CREATE TRIGGER IF NOT EXISTS history_no_delete BEFORE DELETE ON disposition_events BEGIN SELECT RAISE(ABORT,'APPEND_ONLY'); END;
            """)
        if self.db.execute("PRAGMA journal_mode").fetchone()[0] != "wal":
            self.close()
            raise Invalid("WAL_REQUIRED")
        self._verify_storage_permissions()

    @staticmethod
    def _verify_owner_mode(path, *, directory):
        return verify_private_path(
            path,
            directory=directory,
            exact_mode=0o700 if directory else 0o600,
        )

    def _verify_storage_permissions(self):
        self._verify_owner_mode(self.path.parent, directory=True)
        self._verify_owner_mode(self.path, directory=False)
        for suffix in ("-wal", "-shm"):
            sidecar = Path(str(self.path) + suffix)
            if sidecar.exists():
                self._verify_owner_mode(sidecar, directory=False)

    def _require_row_capacity(self, table):
        if table not in {"events", "conflicts", "dispositions", "disposition_events"}:
            raise Invalid("LEDGER_TABLE_INVALID")
        count = self.db.execute(f"SELECT COUNT(*) FROM {table}").fetchone()[0]
        if count >= self.max_rows_per_table:
            raise Invalid("LEDGER_ROW_QUOTA_EXCEEDED")

    def close(self):
        self.db.close()

    @contextmanager
    def transaction(self):
        self._verify_storage_permissions()
        self.db.execute("BEGIN IMMEDIATE")
        try:
            yield
        except BaseException:
            self.db.execute("ROLLBACK")
            raise
        self.db.execute("COMMIT")
        self._verify_storage_permissions()

    def ingest(self, event):
        body = event_bytes(event)
        key = event_key(event)
        with self.transaction():
            prior = self.db.execute("SELECT payload,payload_sha FROM events WHERE tenant=? AND event_id=? AND measurement=? AND epoch=?", key).fetchone()
            if prior:
                if bytes(prior[0]) == body:
                    return "DUPLICATE"
                existing = self.db.execute(
                    "SELECT 1 FROM conflicts WHERE event_key=? AND incoming_sha=?",
                    (canonical(list(key)), sha(body)),
                ).fetchone()
                if not existing:
                    self._require_row_capacity("conflicts")
                self.db.execute("INSERT OR IGNORE INTO conflicts(event_key,original_sha,incoming_sha) VALUES(?,?,?)", (canonical(list(key)), prior[1], sha(body)))
                return "CONFLICT"
            if event["correction_of"] and not self.db.execute("SELECT 1 FROM events WHERE tenant=? AND event_id=? AND measurement=? AND epoch=?", (key[0], event["correction_of"], key[2], key[3])).fetchone():
                raise Invalid("CORRECTION_PARENT_MISSING")
            self._require_row_capacity("events")
            self.db.execute("INSERT INTO events VALUES(?,?,?,?,?,?,?)", (*key, body, sha(body), event["quantity"]))
            return "MEASURED_LOCAL_UNATTESTED"

    def ingest_llm_attestation(self, attestation, expected_producer_runtime_sha256):
        """Validate, adapt, and ingest an untrusted LLM usage reference."""
        return self.ingest(llm_attestation_to_event(attestation, expected_producer_runtime_sha256))

    def ingest_llm_attestation_bytes(self, body, expected_producer_runtime_sha256):
        """Wire-safe LLM ingestion; canonical bytes are mandatory."""
        return self.ingest_llm_attestation(
            decode_llm_attestation(body, expected_producer_runtime_sha256),
            expected_producer_runtime_sha256,
        )

    def events(self):
        self._verify_storage_permissions()
        rows = self.db.execute(
            "SELECT payload FROM events ORDER BY tenant,event_id,measurement,epoch LIMIT ?",
            (self.max_query_rows + 1,),
        ).fetchall()
        if len(rows) > self.max_query_rows:
            raise Invalid("EVENT_RESULT_LIMIT_EXCEEDED")
        return [decode(bytes(row[0])) for row in rows]

    def create_disposition(self, disposition_id, root, adapter_id, idem, timeout_ms):
        identifier(disposition_id); digest(root); identifier(idem)
        adapter_contract(adapter_id, timeout_ms)
        state = initial_disposition()
        with self.transaction():
            self._require_row_capacity("dispositions")
            self.db.execute("INSERT INTO dispositions VALUES(?,?,?,?,?,?)", (disposition_id, root, adapter_id, idem, timeout_ms, canonical(state)))
        return state

    def state(self, disposition_id):
        self._verify_storage_permissions()
        row = self.db.execute("SELECT state FROM dispositions WHERE id=?", (disposition_id,)).fetchone()
        if not row:
            raise Invalid("DISPOSITION_MISSING")
        return decode(bytes(row[0]))

    def observe(self, disposition_id, observation):
        exact(observation, ("root", "adapter_id", "idempotency_key", "signal", "elapsed_ms", "evidence_class"))
        if observation["evidence_class"] != "LOCAL_UNVERIFIED_OBSERVATION":
            raise Invalid("EXTERNAL_ATTESTATION_NOT_IMPLEMENTED")
        with self.transaction():
            row = self.db.execute("SELECT root,adapter,idem,timeout_ms,state FROM dispositions WHERE id=?", (disposition_id,)).fetchone()
            if not row or tuple(observation[k] for k in ("root", "adapter_id", "idempotency_key")) != row[:3]:
                raise Invalid("READBACK_BINDING_MISMATCH")
            result = project_transition(decode(bytes(row[4])), observation["signal"], observation["elapsed_ms"], row[3])
            self._require_row_capacity("disposition_events")
            self.db.execute("UPDATE dispositions SET state=? WHERE id=?", (canonical(result), disposition_id))
            self.db.execute("INSERT INTO disposition_events(disposition_id,signal,observation,state) VALUES(?,?,?,?)", (disposition_id, observation["signal"], canonical(observation), canonical(result)))
        return {"state": result, "evidence_class": "LOCAL_DIAGNOSTIC_PROJECTION", "external_effect_allowed": False, "external_commit_attested": False}

    def request_plan(self, disposition_id):
        self._verify_storage_permissions()
        row = self.db.execute("SELECT root,adapter,idem,timeout_ms,state FROM dispositions WHERE id=?", (disposition_id,)).fetchone()
        if not row or decode(bytes(row[4]))["local_phase"] != "RESERVED":
            raise Invalid("PLAN_NOT_RESERVED")
        return {"schema": "C5_LOCAL_REQUEST_PLAN_V1", "disposition_id": disposition_id, "root": row[0], "adapter_id": row[1], "idempotency_key": row[2], "contract": adapter_contract(row[1], row[3]), "dispatch": "DENY_EXTERNAL_ADAPTER_UNBOUND"}
