"""Local actual SQLite tests and synthetic protocol fixtures; no external I/O."""
import copy
import hashlib
import json
import os
import sqlite3
import subprocess
import sys
import tempfile
import threading
import time
import unittest
from datetime import datetime, timedelta, timezone
from pathlib import Path

from settle_core import *

ROOT = Path(__file__).resolve().parent
SOURCE = ROOT.parent / "src"
METRICS = {}


def sample(n=0):
    return {"schema": "C5_EVENT_V1", "tenant": "tenant-1", "event_id": f"event-{n:04d}", "measurement": "cpu-ms", "epoch": 1, "unit": "ms", "quantity": 10, "event_time": "2026-09-11T12:00:00.000Z", "execution_receipt_sha256": "a" * 64, "custody_receipt_sha256": "b" * 64, "evidence_class": "UNATTESTED_REFERENCE", "correction_of": ""}


def rules():
    return [{"rule_id": "r1", "valid_from": "2026-09-11T00:00:00.000Z", "valid_to": "2026-09-12T00:00:00.000Z"}, {"rule_id": "r2", "valid_from": "2026-09-12T00:00:00.000Z", "valid_to": "2026-09-13T00:00:00.000Z"}]


def llm_attestation():
    return {
        "schema": "LIMEX_LLM_EXECUTION_ATTESTATION_V1",
        "tenant": "tenant-1",
        "event_id": "llm-event-0001",
        "measurement": "inference-token",
        "epoch": 1,
        "unit": "token",
        "quantity": 17,
        "event_time": "2026-09-11T12:00:00.000Z",
        "execution_receipt_sha256": "c" * 64,
        "custody_receipt_sha256": "d" * 64,
        "producer_runtime_sha256": "e" * 64,
        "evidence_class": "UNATTESTED_REFERENCE",
    }


class CodecTests(unittest.TestCase):
    def test_roundtrip_nonascii(self):
        value = {"z": "ö😀", "a": [0, -1, "e\u0301"]}
        self.assertEqual(decode(canonical(value)), value)

    def test_noncanonical_duplicate_float_surrogate_bool(self):
        for body in (b'{"a":1,"a":2}', b'{ "a":1}', b'{"a":1.0}', b'{"a":true}', b'{"a":null}', b'"\\ud800"', b'{"a":NaN}'):
            with self.subTest(body=body), self.assertRaises(Invalid):
                decode(body)

    def test_event_domain_and_evidence_ceiling(self):
        for field, value in (("quantity", -1), ("epoch", True), ("event_time", "2026-09-11T14:00:00+02:00"), ("evidence_class", "RUNTIME_ATTESTED"), ("execution_receipt_sha256", "bad")):
            with self.subTest(field=field), self.assertRaises(Invalid):
                event_bytes(dict(sample(), **{field: value}))

    def test_llm_adapter_preserves_untrusted_ceiling_and_byte_binding(self):
        source = llm_attestation()
        event = llm_attestation_to_event(source, "e" * 64)
        self.assertEqual(event["evidence_class"], "UNATTESTED_REFERENCE")
        self.assertEqual(event["execution_receipt_sha256"], source["execution_receipt_sha256"])
        self.assertEqual(event["custody_receipt_sha256"], sha(canonical(source)))

    def test_llm_adapter_rejects_runtime_mismatch_and_evidence_escalation(self):
        with self.assertRaises(Invalid):
            llm_attestation_to_event(llm_attestation(), "f" * 64)
        escalated = dict(llm_attestation(), evidence_class="PROVIDER_ATTESTED")
        with self.assertRaises(Invalid):
            llm_attestation_to_event(escalated, "e" * 64)

    def test_llm_adapter_rejects_financial_or_unknown_fields(self):
        with self.assertRaises(Invalid):
            llm_attestation_to_event(dict(llm_attestation(), price_cents=1), "e" * 64)
        with self.assertRaises(Invalid):
            decode_llm_attestation(b'{"schema":"LIMEX_LLM_EXECUTION_ATTESTATION_V1","schema":"LIMEX_LLM_EXECUTION_ATTESTATION_V1"}', "e" * 64)


class MerkleTests(unittest.TestCase):
    def test_empty_reference_vector(self):
        expected = hashlib.sha256(b"\x02" + bytes(8)).hexdigest()
        self.assertEqual(MerkleBatch([]).root, expected)
        with self.assertRaises(Invalid):
            MerkleBatch([]).proof(0)

    def test_single_reference_vector(self):
        event = sample()
        raw = event_bytes(event)
        expected_leaf = hashlib.sha256(b"\x00" + len(raw).to_bytes(8, "big") + raw).digest()
        expected_root = hashlib.sha256(b"\x02" + (1).to_bytes(8, "big") + expected_leaf).hexdigest()
        tree = MerkleBatch([event])
        self.assertEqual(tree.root, expected_root)
        self.assertEqual(tree.proof(0)["siblings"], [])
        self.assertTrue(verify_proof(event, tree.proof(0), expected_root))

    def test_even_and_odd_all_members(self):
        for count in (2, 3, 5, 16, 31):
            tree = MerkleBatch([sample(n) for n in range(count)])
            for i, body in enumerate(tree.bodies):
                proof = decode(canonical(tree.proof(i)))
                self.assertTrue(verify_proof(decode(body), proof, tree.root))

    def test_order_deterministic_input_mutation_no_alias(self):
        events = [sample(n) for n in range(5)]
        tree = MerkleBatch(events)
        self.assertEqual(tree.root, MerkleBatch(list(reversed(events))).root)
        events[0]["quantity"] = 99
        self.assertEqual(decode(tree.bodies[0])["quantity"], 10)

    def test_duplicate_key_and_bound(self):
        with self.assertRaises(Invalid):
            MerkleBatch([sample(), sample()])
        with self.assertRaises(Invalid):
            MerkleBatch([sample()] * 4097)

    def test_tamper_every_proof_field(self):
        tree = MerkleBatch([sample(i) for i in range(3)])
        proof = tree.proof(2)
        variants = []
        for key, val in (("schema", "other"), ("count", 4), ("index", 1), ("root", "0" * 64), ("leaf_sha256", "0" * 64), ("extra", 1)):
            altered = copy.deepcopy(proof); altered[key] = val; variants.append(altered)
        altered = copy.deepcopy(proof); altered["siblings"].pop(); variants.append(altered)
        altered = copy.deepcopy(proof); altered["siblings"].append(proof["siblings"][0]); variants.append(altered)
        altered = copy.deepcopy(proof); altered["siblings"][0]["side"] = "LEFT"; variants.append(altered)
        altered = copy.deepcopy(proof); altered["siblings"][0]["sha256"] = "0" * 64; variants.append(altered)
        for val in variants:
            self.assertFalse(verify_proof(sample(2), val, tree.root))
        self.assertFalse(verify_proof(dict(sample(2), quantity=11), proof, tree.root))
        self.assertFalse(verify_proof(sample(2), proof, "f" * 64))

    def test_malformed_total_verifier(self):
        for value in (None, [], {}, "bad", 3, True):
            self.assertFalse(verify_proof(sample(), value, "a" * 64))

    def test_batch_rule_and_cutoff_binding(self):
        index = IntervalIndex("cpu-ms", rules())
        batch = build_batch_record([sample()], index, "2026-09-12T00:00:00.000Z")
        other = build_batch_record([sample()], index, "2026-09-12T00:00:01.000Z")
        self.assertNotEqual(batch["batch_commitment"], other["batch_commitment"])
        self.assertEqual(batch["manifest"]["bindings"][0]["rule_id"], "r1")
        with self.assertRaises(Invalid):
            build_batch_record([sample()], index, sample()["event_time"])
        with self.assertRaises(Invalid):
            build_batch_record([dict(sample(), event_time="2026-09-10T12:00:00.000Z")], index, "2026-09-12T00:00:00.000Z")


class IntervalTests(unittest.TestCase):
    def test_boundary_and_gap(self):
        index = IntervalIndex("cpu-ms", rules())
        self.assertEqual(index.lookup("cpu-ms", "2026-09-12T00:00:00.000Z"), "r2")
        self.assertEqual(index.lookup("cpu-ms", "2026-09-11T23:59:59.999Z"), "r1")
        self.assertIsNone(index.lookup("cpu-ms", "2026-09-13T00:00:00.000Z"))
        self.assertIsNone(index.lookup("cpu-ms", "2026-09-10T23:59:59.999Z"))

    def test_overlap_duplicate_reverse_invalid_date(self):
        cases = []
        a = rules(); a[1]["valid_from"] = "2026-09-11T23:59:59.999Z"; cases.append(a)
        a = rules(); a[1]["rule_id"] = "r1"; cases.append(a)
        a = rules(); a[0]["valid_to"] = a[0]["valid_from"]; cases.append(a)
        a = rules(); a[0]["valid_from"] = "2026-02-30T00:00:00.000Z"; cases.append(a)
        for a in cases:
            with self.assertRaises(Invalid):
                IntervalIndex("cpu-ms", a)

    def test_snapshot_immutable_and_scope(self):
        raw = rules(); index = IntervalIndex("cpu-ms", raw); before = index.sha256
        raw[0]["rule_id"] = "changed"
        self.assertEqual(index.lookup("cpu-ms", sample()["event_time"]), "r1")
        self.assertEqual(index.sha256, before)
        with self.assertRaises(AttributeError):
            index.rows = ()
        with self.assertRaises(Invalid):
            index.lookup("other", sample()["event_time"])

    def test_reproducible_load_corpus(self):
        start = datetime(2026, 1, 1, tzinfo=timezone.utc)
        fmt = lambda d: d.isoformat(timespec="milliseconds").replace("+00:00", "Z")
        raw = [{"rule_id": f"r{i}", "valid_from": fmt(start + timedelta(seconds=i)), "valid_to": fmt(start + timedelta(seconds=i + 1))} for i in range(10_000)]
        index = IntervalIndex("cpu-ms", raw)
        samples = []
        for i in range(10_000):
            stamp = raw[(i * 7919) % 10_000]["valid_from"]
            t = time.perf_counter_ns()
            result = index.lookup("cpu-ms", stamp)
            samples.append(time.perf_counter_ns() - t)
            self.assertEqual(result, f"r{(i * 7919) % 10_000}")
        samples.sort()
        METRICS["interval_lookup"] = {"intervals": 10_000, "lookups": 10_000, "corpus_sha256": index.sha256, "p50_ns": samples[4999], "p95_ns": samples[9499], "p99_ns": samples[9899], "max_ns": samples[-1], "scope": "ONE_LOCAL_RUN_INCLUDING_UTC_PARSE_NOT_SLA"}


class LedgerTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="test-db-", dir=ROOT)
        self.path = Path(self.temp.name) / "ledger.sqlite"
        self.ledger = LocalLedger(self.path, initialize=True)

    def tearDown(self):
        self.ledger.close(); self.temp.cleanup()

    def test_idempotency_conflict_and_restart(self):
        self.assertEqual(self.ledger.ingest(sample()), "MEASURED_LOCAL_UNATTESTED")
        self.assertEqual(self.ledger.ingest(sample()), "DUPLICATE")
        self.assertEqual(self.ledger.ingest(dict(sample(), quantity=99)), "CONFLICT")
        self.assertEqual(self.ledger.ingest(dict(sample(), quantity=99)), "CONFLICT")
        self.assertEqual(self.ledger.db.execute("SELECT COUNT(*) FROM conflicts").fetchone()[0], 1)
        self.ledger.close(); self.ledger = LocalLedger(self.path)
        self.assertEqual(len(self.ledger.events()), 1)
        self.assertEqual(self.ledger.events()[0]["quantity"], 10)
        self.assertEqual(self.ledger.ingest(sample()), "DUPLICATE")

    def test_llm_attestation_ingestion_is_local_unattested_and_idempotent(self):
        source = llm_attestation()
        body = canonical(source)
        self.assertEqual(self.ledger.ingest_llm_attestation_bytes(body, "e" * 64), "MEASURED_LOCAL_UNATTESTED")
        self.assertEqual(self.ledger.ingest_llm_attestation_bytes(body, "e" * 64), "DUPLICATE")
        stored = self.ledger.events()[0]
        self.assertEqual(stored["custody_receipt_sha256"], sha(canonical(source)))

    def test_llm_attestation_tamper_creates_conflict_not_overwrite(self):
        source = llm_attestation()
        self.ledger.ingest_llm_attestation(source, "e" * 64)
        changed = dict(source, quantity=18)
        self.assertEqual(self.ledger.ingest_llm_attestation(changed, "e" * 64), "CONFLICT")
        self.assertEqual(self.ledger.events()[0]["quantity"], 17)

    def test_key_partition(self):
        for changes in ({}, {"tenant": "tenant-2"}, {"measurement": "io-ms"}, {"epoch": 2}):
            self.ledger.ingest(dict(sample(), **changes))
        self.assertEqual(len(self.ledger.events()), 4)

    def test_database_leaf_symlink_is_rejected(self):
        target = Path(self.temp.name) / "other.sqlite"
        other = LocalLedger(target, initialize=True)
        other.close()
        link = Path(self.temp.name) / "linked.sqlite"
        link.symlink_to(target)
        with self.assertRaises(Invalid):
            LocalLedger(link, initialize=True)

    def test_ledger_rejects_broad_database_permissions(self):
        self.ledger.close()
        os.chmod(self.path, 0o644)
        with self.assertRaisesRegex(Invalid, "LEDGER_STORAGE_PERMISSIONS_TOO_BROAD"):
            LocalLedger(self.path)
        os.chmod(self.path, 0o600)
        self.ledger = LocalLedger(self.path)

    def test_ledger_rejects_broad_parent_permissions(self):
        self.ledger.close()
        os.chmod(Path(self.temp.name), 0o755)
        with self.assertRaisesRegex(Invalid, "LEDGER_STORAGE_PERMISSIONS_TOO_BROAD"):
            LocalLedger(self.path)
        os.chmod(Path(self.temp.name), 0o700)
        self.ledger = LocalLedger(self.path)

    @unittest.skipUnless(sys.platform == "darwin", "Darwin ACL adapter test")
    def test_ledger_rejects_extended_allow_acl(self):
        self.ledger.close()
        subprocess.run(
            ["/bin/chmod", "+a", "everyone allow read", self.temp.name],
            check=True,
            capture_output=True,
        )
        try:
            with self.assertRaisesRegex(Invalid, "LEDGER_STORAGE_ALLOW_ACL_REJECTED"):
                LocalLedger(self.path)
        finally:
            subprocess.run(["/bin/chmod", "-N", self.temp.name], check=True, capture_output=True)
        self.ledger = LocalLedger(self.path)

    def test_row_quota_fails_before_second_unique_event(self):
        limited_path = Path(self.temp.name) / "limited.sqlite"
        limited = LocalLedger(limited_path, initialize=True, max_rows_per_table=1)
        try:
            self.assertEqual(limited.ingest(sample()), "MEASURED_LOCAL_UNATTESTED")
            with self.assertRaisesRegex(Invalid, "LEDGER_ROW_QUOTA_EXCEEDED"):
                limited.ingest(dict(sample(), event_id="event-2"))
            self.assertEqual(len(limited.events()), 1)
        finally:
            limited.close()

    def test_event_query_refuses_unbounded_materialization(self):
        bounded_path = Path(self.temp.name) / "bounded-query.sqlite"
        bounded = LocalLedger(bounded_path, initialize=True, max_query_rows=1)
        try:
            bounded.ingest(sample())
            bounded.ingest(dict(sample(), event_id="event-2"))
            with self.assertRaisesRegex(Invalid, "EVENT_RESULT_LIMIT_EXCEEDED"):
                bounded.events()
        finally:
            bounded.close()

    def test_append_only_and_correction_parent(self):
        with self.assertRaises(Invalid):
            self.ledger.ingest(dict(sample(1), correction_of="missing"))
        self.ledger.ingest(sample())
        self.ledger.ingest(dict(sample(1), correction_of=sample()["event_id"]))
        self.assertEqual(len(self.ledger.events()), 2)
        for sql in ("UPDATE events SET quantity=77", "DELETE FROM events"):
            with self.assertRaises(sqlite3.IntegrityError):
                self.ledger.db.execute(sql)

    def test_concurrent_local_connections(self):
        barrier = threading.Barrier(12); outcomes = []; errors = []
        def worker():
            connection = LocalLedger(self.path)
            try:
                barrier.wait(timeout=10); outcomes.append(connection.ingest(sample()))
            except BaseException as exc:
                errors.append(repr(exc))
            finally:
                connection.close()
        threads = [threading.Thread(target=worker) for _ in range(12)]
        for t in threads: t.start()
        for t in threads: t.join(timeout=15)
        self.assertFalse(any(t.is_alive() for t in threads)); self.assertEqual(errors, [])
        self.assertEqual(outcomes.count("MEASURED_LOCAL_UNATTESTED"), 1)
        self.assertEqual(outcomes.count("DUPLICATE"), 11)
        self.assertEqual(len(self.ledger.events()), 1)

    def test_writer_contention_bounded_no_retry(self):
        other = LocalLedger(self.path); other.db.execute("PRAGMA busy_timeout=30")
        self.ledger.db.execute("BEGIN IMMEDIATE")
        before = time.monotonic()
        try:
            with self.assertRaises(sqlite3.OperationalError): other.ingest(sample())
            self.assertLess(time.monotonic() - before, 1.0)
        finally:
            self.ledger.db.execute("ROLLBACK"); other.close()
        self.assertEqual(self.ledger.events(), [])

    def test_process_crash_uncommitted_and_committed(self):
        script = Path(__file__).resolve()
        for mode, expected in (("UNCOMMITTED", 0), ("COMMITTED", 1)):
            child_env = dict(os.environ)
            child_env["PYTHONPATH"] = str(SOURCE)
            child_env["PYTHONDONTWRITEBYTECODE"] = "1"
            run = subprocess.run([sys.executable, "-B", str(script), "--crash-child", str(self.path), mode], cwd=ROOT, env=child_env, capture_output=True, timeout=10)
            self.assertEqual(run.returncode, 71, run.stderr.decode("utf-8", "replace"))
            self.assertEqual(len(self.ledger.events()), expected)
        self.assertEqual(self.ledger.ingest(sample()), "DUPLICATE")
        self.assertEqual(self.ledger.db.execute("PRAGMA integrity_check").fetchone()[0], "ok")

    def test_disposition_durable_unknown_and_bound_request(self):
        root = MerkleBatch([sample()]).root
        self.ledger.create_disposition("d1", root, "offline", "key1", 30000)
        def obs(signal, elapsed=0, **changes):
            return dict(root=root, adapter_id="offline", idempotency_key="key1", signal=signal, elapsed_ms=elapsed, evidence_class="LOCAL_UNVERIFIED_OBSERVATION", **changes)
        self.ledger.observe("d1", obs("RESERVE"))
        self.assertEqual(self.ledger.request_plan("d1")["dispatch"], "DENY_EXTERNAL_ADAPTER_UNBOUND")
        self.ledger.observe("d1", obs("RECORD_SEND_ATTEMPT"))
        self.ledger.observe("d1", obs("TIMEOUT", 30000))
        self.ledger.close(); self.ledger = LocalLedger(self.path)
        self.assertEqual(self.ledger.state("d1")["projected_outcome"], "UNKNOWN_EFFECT")
        with self.assertRaises(Invalid): self.ledger.observe("d1", obs("RESERVE"))
        with self.assertRaises(Invalid): self.ledger.request_plan("d1")
        bad = obs("COMMITTED"); bad["idempotency_key"] = "other"
        with self.assertRaises(Invalid): self.ledger.observe("d1", bad)
        bad = obs("COMMITTED"); bad["evidence_class"] = "AUTHENTIC_PROVIDER"
        with self.assertRaises(Invalid): self.ledger.observe("d1", bad)
        response = self.ledger.observe("d1", obs("COMMITTED"))
        self.assertFalse(response["external_effect_allowed"])
        self.assertFalse(response["external_commit_attested"])
        self.assertEqual(response["state"]["capability_phase"], "CONSUMED_PROJECTED")
        self.assertEqual(self.ledger.db.execute("SELECT COUNT(*) FROM disposition_events").fetchone()[0], 4)


class TransitionTests(unittest.TestCase):
    def sent(self):
        return project_transition(project_transition(initial_disposition(), "RESERVE", 0, 100), "RECORD_SEND_ATTEMPT", 0, 100)

    def test_no_readback_before_send(self):
        for signal in ("COMMITTED", "KNOWN_NOT_COMMITTED", "PENDING", "TIMEOUT"):
            with self.assertRaises(Invalid): project_transition(initial_disposition(), signal, 100, 100)

    def test_timeout_boundary_and_errors(self):
        with self.assertRaises(Invalid): project_transition(self.sent(), "TIMEOUT", 99, 100)
        self.assertEqual(project_transition(self.sent(), "TIMEOUT", 100, 100)["projected_outcome"], "UNKNOWN_EFFECT")
        for signal in ("TRANSPORT_ERROR", "CRASH_AFTER_SEND", "UNKNOWN_READBACK", "CONTRADICTORY"):
            self.assertEqual(project_transition(self.sent(), signal, 0, 100)["projected_outcome"], "UNKNOWN_EFFECT")

    def test_pending_is_not_unknown_and_late_commit(self):
        pending = project_transition(self.sent(), "PENDING", 0, 100)
        self.assertEqual(pending["projected_outcome"], "PENDING")
        unknown = project_transition(pending, "TIMEOUT", 100, 100)
        commit = project_transition(unknown, "COMMITTED", 200, 100)
        self.assertEqual(commit["projected_outcome"], "COMMITTED")
        self.assertEqual(commit["retry"], "NO_AUTOMATIC_RETRY")

    def test_negative_commit_and_conflicting_terminal(self):
        negative = project_transition(self.sent(), "KNOWN_NOT_COMMITTED", 0, 100)
        self.assertEqual(negative["capability_phase"], "RESERVED")
        self.assertEqual(project_transition(negative, "COMMITTED", 0, 100)["projected_outcome"], "UNKNOWN_EFFECT")
        committed = project_transition(self.sent(), "COMMITTED", 0, 100)
        disputed = project_transition(committed, "KNOWN_NOT_COMMITTED", 0, 100)
        self.assertEqual(disputed["projected_outcome"], "UNKNOWN_EFFECT")
        self.assertEqual(disputed["capability_phase"], "CONSUMED_PROJECTED")
        still = project_transition(disputed, "KNOWN_NOT_COMMITTED", 0, 100)
        self.assertEqual(still["projected_outcome"], "UNKNOWN_EFFECT")

    def test_reversal_and_dispute_separate(self):
        with self.assertRaises(Invalid): project_transition(self.sent(), "REVERSED", 0, 100)
        commit = project_transition(self.sent(), "COMMITTED", 0, 100)
        for signal in ("REVERSED", "DISPUTED"):
            result = project_transition(commit, signal, 0, 100)
            self.assertEqual(result["projected_outcome"], signal)
            self.assertEqual(result["capability_phase"], "CONSUMED_PROJECTED")

    def test_invalid_state_timeout_signal(self):
        for state, signal, timeout in (({}, "PENDING", 100), (initial_disposition(), "unknown", 100), (initial_disposition(), "RESERVE", 0)):
            with self.assertRaises(Invalid): project_transition(state, signal, 0, timeout)


def crash_child(path, mode):
    ledger = LocalLedger(path)
    if mode == "COMMITTED":
        ledger.ingest(sample())
    else:
        event = sample(); body = event_bytes(event)
        ledger.db.execute("BEGIN IMMEDIATE")
        ledger.db.execute("INSERT INTO events VALUES(?,?,?,?,?,?,?)", (*event_key(event), body, sha(body), event["quantity"]))
    os._exit(71)


if __name__ == "__main__":
    if len(sys.argv) > 1 and sys.argv[1] == "--crash-child":
        crash_child(sys.argv[2], sys.argv[3])
    else:
        suite = unittest.defaultTestLoader.loadTestsFromModule(sys.modules[__name__])
        result = unittest.TextTestRunner(verbosity=2).run(suite)
        report = {"schema": "C5_LOCAL_TEST_REPORT_V1", "tests_run": result.testsRun, "failures": [(str(t), x) for t, x in result.failures], "errors": [(str(t), x) for t, x in result.errors], "passed": result.wasSuccessful(), "exit_code": 0 if result.wasSuccessful() else 1, "python": sys.version, "sqlite": sqlite3.sqlite_version, "metrics": METRICS, "evidence_class": "LOCAL_EXECUTED_SQLITE_AND_SYNTHETIC_PROTOCOL_TESTS", "external_calls": 0, "provider_attested": False, "multi_node_attested": False}
        print(json.dumps(report, indent=2, sort_keys=True))
        if len(sys.argv) == 3 and sys.argv[1] == "--report":
            target = Path(sys.argv[2]).resolve()
            if not target.is_relative_to(ROOT) or target.exists():
                raise Invalid("FRESH_CONFINED_REPORT_REQUIRED")
            target.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")
        sys.exit(report["exit_code"])
