import { createHash } from "node:crypto";
import { performance } from "node:perf_hooks";
import { readFileSync, writeFileSync } from "node:fs";
import {
  bindDefectProjectionEventV4,
  createDefectProjectionStateV4,
  projectDefectEventBatchV4,
} from "../scripts/defect_event_projector_v4.mjs";
import { parseBoundedJsonCarrierV4 } from "../scripts/canonical_state_v2.mjs";

const QUEST = "FUZZI-SFH-SOFTWARE-STRESS-V1";
const GATE = "FUNCTIONAL-CORE-STRESS";
const CORRELATION = "FUZZI-SFH-PUBLIC-CAPSULE-20260912-001";
const MAX_BATCH = 256;
const ARTIFACT_LIMIT_BYTES = 65_536;
const sha256 = (value) => createHash("sha256").update(value).digest("hex");
const carrier = (value) => parseBoundedJsonCarrierV4(JSON.stringify(value));
const projectBatch = (state, events) => projectDefectEventBatchV4(state, carrier(events));
const executionBoundary = process.env.FUZZI_EXECUTION_BOUNDARY ?? "UNDECLARED";
const projectorBytes = readFileSync(new URL("../scripts/defect_event_projector_v4.mjs", import.meta.url));
const canonicalStateBytes = readFileSync(new URL("../scripts/canonical_state_v2.mjs", import.meta.url));

function check(condition, vectorId, message, actual = null) {
  if (!condition) {
    const error = new Error(`${vectorId}:${message}`);
    error.vector_id = vectorId;
    error.actual = actual;
    throw error;
  }
}

function initialState() {
  return createDefectProjectionStateV4(QUEST, GATE, CORRELATION);
}

function localEvent(index, suffix = "base") {
  const defectId = `defect-${suffix}-${String(index).padStart(4, "0")}`;
  return bindDefectProjectionEventV4(carrier({
    schema_version: "limex-defect-projection-event-v4.0.0",
    quest_id: QUEST,
    gate_id: GATE,
    correlation_id: CORRELATION,
    event_id: `event-${suffix}-${String(index).padStart(4, "0")}`,
    kind: "LOCAL_MODULE_DEFECT",
    payload: {
      affected_branch_id: `branch-${String(index % 17).padStart(2, "0")}`,
      defect_fingerprint_sha256: sha256(`defect:${suffix}:${index}`),
      defect_id: defectId,
      reopen_fingerprint_sha256: sha256(`reopen:${suffix}:${index}`),
    },
  }));
}

function artifactBinding(bytes, label) {
  const payload = Buffer.alloc(bytes, label.charCodeAt(0));
  return {
    sha256: sha256(payload),
    utf8_base64: payload.toString("base64"),
    utf8_bytes: bytes,
  };
}

function closureEvent(defectId, eventId, bytes) {
  const artifact = artifactBinding(bytes, "a");
  return bindDefectProjectionEventV4(carrier({
    schema_version: "limex-defect-projection-event-v4.0.0",
    quest_id: QUEST,
    gate_id: GATE,
    correlation_id: CORRELATION,
    event_id: eventId,
    kind: "DEFECT_CLOSURE_REVALIDATED",
    payload: {
      defect_id: defectId,
      root_cause: artifact,
      regression_guard: artifact,
      correction: artifact,
      complete_reaudit: artifact,
      independent_acceptance: {
        acceptance_decision: "PASS",
        artifact,
        attestation_kind: "INDEPENDENT_READ_ONLY_REAUDIT_ACCEPTANCE",
        auditor_identity: "auditor-r5",
        builder_identity: "builder-r5",
        independence_marker: "AUDITOR_DISTINCT_FROM_BUILDER__READ_ONLY",
        subject_correlation_id: CORRELATION,
        subject_defect_id: defectId,
        subject_gate_id: GATE,
        subject_quest_id: QUEST,
      },
    },
  }));
}

function duration(run) {
  const start = performance.now();
  const result = run();
  return { result, duration_ms: performance.now() - start };
}

const vectors = [];
const failures = [];
let assertions = 0;

function record(vectorId, profile, run) {
  try {
    const observed = run();
    vectors.push({ vector_id: vectorId, profile, status: "PASS", ...observed });
  } catch (error) {
    failures.push({
      vector_id: error.vector_id ?? vectorId,
      profile,
      status: "FAIL",
      reason: error.message,
      actual: error.actual ?? null,
    });
  }
}

for (const count of [1, 2, 4, 8, 16, 32, 64, 128, 255, 256]) {
  record(`DENSITY_${count}`, "LOGICAL_PACKET_DENSITY_SWEEP", () => {
    const events = Array.from({ length: count }, (_, index) => localEvent(index, `d${count}`));
    const measured = duration(() => projectBatch(initialState(), events));
    assertions += 5;
    check(measured.result.decision === "PASS", `DENSITY_${count}`, "batch rejected", measured.result.reason);
    check(measured.result.state_prime.accepted_events.length === count, `DENSITY_${count}`, "event loss", measured.result.state_prime.accepted_events.length);
    check(measured.result.effectful_action_allowed === false, `DENSITY_${count}`, "effectful authority leaked");
    check(measured.result.diagnostic_authority === "NONE", `DENSITY_${count}`, "diagnostic authority leaked");
    check(measured.result.authorized_transition === null, `DENSITY_${count}`, "authorized transition leaked");
    return {
      input_events: count,
      accepted_events: measured.result.state_prime.accepted_events.length,
      duration_ms: Number(measured.duration_ms.toFixed(3)),
      adapter_actions: measured.result.required_adapter_actions,
    };
  });
}

record("DENSITY_257_REJECT", "BATCH_UPPER_BOUND", () => {
  const events = Array.from({ length: MAX_BATCH + 1 }, (_, index) => localEvent(index, "over"));
  const state = initialState();
  const measured = duration(() => projectBatch(state, events));
  assertions += 5;
  check(measured.result.decision === "DENY", "DENSITY_257_REJECT", "oversize batch accepted");
  check(measured.result.reason === "DEFECT_PROJECTION_EVENT_BATCH_INVALID", "DENSITY_257_REJECT", "wrong denial reason", measured.result.reason);
  check(JSON.stringify(measured.result.state_prime) === JSON.stringify(state), "DENSITY_257_REJECT", "state mutated on denial");
  check(JSON.stringify(measured.result.required_adapter_actions) === JSON.stringify([{ kind: "NO_OP" }]), "DENSITY_257_REJECT", "non-NO_OP action on denial", measured.result.required_adapter_actions);
  check(measured.result.effectful_action_allowed === false, "DENSITY_257_REJECT", "effectful authority leaked");
  return { input_events: 257, duration_ms: Number(measured.duration_ms.toFixed(3)), denial_reason: measured.result.reason };
});

record("PHASE_ORDER_REVERSAL", "DETERMINISTIC_PHASE_NOISE", () => {
  const events = Array.from({ length: 128 }, (_, index) => localEvent(index, "phase"));
  const forward = duration(() => projectBatch(initialState(), events));
  const reverse = duration(() => projectBatch(initialState(), [...events].reverse()));
  assertions += 4;
  check(forward.result.decision === "PASS" && reverse.result.decision === "PASS", "PHASE_ORDER_REVERSAL", "permutation rejected");
  check(JSON.stringify(forward.result.state_prime) === JSON.stringify(reverse.result.state_prime), "PHASE_ORDER_REVERSAL", "state depends on event order");
  check(JSON.stringify(forward.result.required_adapter_actions) === JSON.stringify(reverse.result.required_adapter_actions), "PHASE_ORDER_REVERSAL", "terminal actions depend on event order");
  check(forward.result.effectful_action_allowed === false && reverse.result.effectful_action_allowed === false, "PHASE_ORDER_REVERSAL", "authority leaked");
  return {
    input_events_each: 128,
    forward_duration_ms: Number(forward.duration_ms.toFixed(3)),
    reverse_duration_ms: Number(reverse.duration_ms.toFixed(3)),
  };
});

record("FRAME_FRAGMENTATION", "LOGICAL_BATCH_FRAGMENTATION", () => {
  const events = Array.from({ length: 256 }, (_, index) => localEvent(index, "frag"));
  const whole = duration(() => projectBatch(initialState(), events));
  let fragmentedState = initialState();
  const slices = [1, 7, 31, 89, 128];
  let offset = 0;
  const fragmentLatencies = [];
  for (const size of slices) {
    const measured = duration(() => projectBatch(fragmentedState, events.slice(offset, offset + size)));
    check(measured.result.decision === "PASS", "FRAME_FRAGMENTATION", `fragment ${size} rejected`, measured.result.reason);
    fragmentedState = measured.result.state_prime;
    fragmentLatencies.push(Number(measured.duration_ms.toFixed(3)));
    offset += size;
  }
  assertions += 4;
  check(offset === 256, "FRAME_FRAGMENTATION", "fragment sizes do not cover batch", offset);
  check(whole.result.decision === "PASS", "FRAME_FRAGMENTATION", "whole batch rejected", whole.result.reason);
  check(JSON.stringify(whole.result.state_prime) === JSON.stringify(fragmentedState), "FRAME_FRAGMENTATION", "fragmented final state differs");
  check(fragmentedState.accepted_events.length === 256, "FRAME_FRAGMENTATION", "fragment drop detected", fragmentedState.accepted_events.length);
  return {
    logical_frames: 256,
    fragments: slices,
    dropped_frames: 0,
    whole_duration_ms: Number(whole.duration_ms.toFixed(3)),
    fragment_duration_ms: fragmentLatencies,
  };
});

record("DROPOUT_UNKNOWN_REFERENCE", "SIGNAL_DROPOUT", () => {
  const missing = bindDefectProjectionEventV4(carrier({
    schema_version: "limex-defect-projection-event-v4.0.0",
    quest_id: QUEST,
    gate_id: GATE,
    correlation_id: CORRELATION,
    event_id: "event-dropout-0001",
    kind: "DEFECT_RECURRENCE",
    payload: { defect_id: "missing-defect", recurrence_fingerprint_sha256: sha256("missing") },
  }));
  const state = initialState();
  const measured = duration(() => projectBatch(state, [missing]));
  assertions += 4;
  check(measured.result.decision === "DENY", "DROPOUT_UNKNOWN_REFERENCE", "dropout accepted");
  check(measured.result.reason === "DEFECT_REFERENCE_NOT_FOUND", "DROPOUT_UNKNOWN_REFERENCE", "wrong denial reason", measured.result.reason);
  check(JSON.stringify(measured.result.state_prime) === JSON.stringify(state), "DROPOUT_UNKNOWN_REFERENCE", "state mutated on dropout");
  check(JSON.stringify(measured.result.required_adapter_actions) === JSON.stringify([{ kind: "NO_OP" }]), "DROPOUT_UNKNOWN_REFERENCE", "action leaked on dropout", measured.result.required_adapter_actions);
  return { duration_ms: Number(measured.duration_ms.toFixed(3)), denial_reason: measured.result.reason };
});

record("HASH_CORRUPTION_ATOMIC", "BOUNDARY_JITTER_AND_TAMPERING", () => {
  const events = Array.from({ length: 64 }, (_, index) => localEvent(index, "tamper"));
  events[32] = { ...events[32], event_sha256: "0".repeat(64) };
  const state = initialState();
  const measured = duration(() => projectBatch(state, events));
  assertions += 4;
  check(measured.result.decision === "DENY", "HASH_CORRUPTION_ATOMIC", "tampered batch accepted");
  check(measured.result.reason === "DEFECT_PROJECTION_EVENT_HASH_MISMATCH", "HASH_CORRUPTION_ATOMIC", "wrong denial reason", measured.result.reason);
  check(JSON.stringify(measured.result.state_prime) === JSON.stringify(state), "HASH_CORRUPTION_ATOMIC", "partial state leaked from rejected batch");
  check(JSON.stringify(measured.result.required_adapter_actions) === JSON.stringify([{ kind: "NO_OP" }]), "HASH_CORRUPTION_ATOMIC", "historical action leaked", measured.result.required_adapter_actions);
  return { input_events: 64, tampered_index: 32, duration_ms: Number(measured.duration_ms.toFixed(3)), denial_reason: measured.result.reason };
});

for (const bytes of [ARTIFACT_LIMIT_BYTES - 1, ARTIFACT_LIMIT_BYTES]) {
  record(`CLOSURE_BYTES_${bytes}`, "CLOSURE_ARTIFACT_BOUNDARY", () => {
    const declaration = localEvent(bytes, `artifact-${bytes}`);
    const defectId = declaration.payload.defect_id;
    const closure = closureEvent(defectId, `event-close-${bytes}`, bytes);
    const measured = duration(() => projectBatch(initialState(), [declaration, closure]));
    assertions += 4;
    check(measured.result.decision === "PASS", `CLOSURE_BYTES_${bytes}`, "valid boundary rejected", measured.result.reason);
    check(measured.result.state_prime.defects[0].status === "RESOLVED", `CLOSURE_BYTES_${bytes}`, "defect not resolved");
    check(measured.result.state_prime.blocked_branches.length === 0, `CLOSURE_BYTES_${bytes}`, "branch remains blocked");
    check(measured.result.effectful_action_allowed === false, `CLOSURE_BYTES_${bytes}`, "effectful authority leaked");
    return { artifact_bytes_each: bytes, duration_ms: Number(measured.duration_ms.toFixed(3)), terminal_actions: measured.result.required_adapter_actions };
  });
}

record("CLOSURE_BYTES_65537_REJECT", "CLOSURE_ARTIFACT_UPPER_BOUND", () => {
  const declaration = localEvent(9999, "artifact-over");
  let rejected = false;
  let reason = null;
  const measured = duration(() => {
    try {
      closureEvent(declaration.payload.defect_id, "event-close-65537", ARTIFACT_LIMIT_BYTES + 1);
    } catch (error) {
      rejected = true;
      reason = error.message;
    }
  });
  assertions += 2;
  check(rejected, "CLOSURE_BYTES_65537_REJECT", "oversize closure draft accepted");
  check(reason === "DEFECT_PROJECTION_EVENT_DRAFT_INVALID", "CLOSURE_BYTES_65537_REJECT", "wrong rejection reason", reason);
  return { artifact_bytes_each: 65_537, duration_ms: Number(measured.duration_ms.toFixed(3)), rejection_reason: reason };
});

const durations = vectors.flatMap((entry) => {
  const values = [];
  for (const [key, value] of Object.entries(entry)) {
    if (key.endsWith("duration_ms") && typeof value === "number") values.push(value);
    if (key.endsWith("duration_ms") && Array.isArray(value)) values.push(...value);
  }
  return values;
});

const report = {
  schema_version: "limex-fuzzi-sfh-software-stress-v1.0.0",
  created_at_utc: new Date().toISOString(),
  status: failures.length === 0 ? "PASS_SOFTWARE_FUNCTIONAL_CORE_ONLY" : "FAIL_SOFTWARE_FUNCTIONAL_CORE",
  evidence_class: "LOCAL_USERSPACE_DETERMINISTIC_PROJECTOR_STRESS",
  target: {
    module: "defect_event_projector_v4.mjs",
    module_sha256: sha256(projectorBytes),
    canonical_state_module: "canonical_state_v2.mjs",
    canonical_state_sha256: sha256(canonicalStateBytes),
    node: process.version,
    platform: `${process.platform}_${process.arch}`,
  },
  execution_boundary: {
    declared_by_invoker: executionBoundary,
    deterministic_runtime_path: process.execPath,
    network_calls_in_harness_source: 0,
    boundary_is_external_to_process: true,
  },
  statistics: {
    vector_runs: vectors.length + failures.length,
    passed: vectors.length,
    failed: failures.length,
    assertions,
    maximum_logical_events_in_accepted_batch: 256,
    rejected_overlimit_batch_events: 257,
    logical_fragmentation_frames: 256,
    logical_fragment_drops: failures.some((entry) => entry.vector_id === "FRAME_FRAGMENTATION") ? null : 0,
    latency_ms_min: durations.length ? Math.min(...durations) : null,
    latency_ms_max: durations.length ? Math.max(...durations) : null,
  },
  vectors,
  failures,
  physical_test_gate: {
    state: "NOT_ARMED_FAIL_CLOSED",
    reasons: [
      "FUZZI_SFH_PHYSICAL_INTERFACE_AND_FREQUENCY_BAND_CONTRACT_NOT_BOUND",
      "NO_PACKET_CAPTURE_OR_KERNEL_SYSCALL_TRACE",
      "NO_BOUND_SENSOR_VOLTAGE_RATE_OR_PACKET_DENSITY_LIMITS",
      "NO_TARGET_HARDWARE_ADAPTER_BOUND",
    ],
  },
  non_implications: [
    "NO_PHYSICAL_SENSOR_OR_IO_HARDWARE_STRESS_EXECUTED",
    "NO_HZ_VOLTAGE_THERMAL_OR_REAL_TIME_CERTIFICATION",
    "NO_KERNEL_OR_DRIVER_MONITORING_EXECUTED",
    "NO_PACKET_CAPTURE_OR_KERNEL_SYSCALL_TRACE",
    "NO_PRODUCT_RUNTIME_BINDING_OR_ACTIVE_SKILL_MUTATION",
    "NO_PRODUCTION_RELEASE_AUTHORITY",
  ],
};

const serialized = `${JSON.stringify(report, null, 2)}\n`;
if (process.argv[2]) writeFileSync(process.argv[2], serialized, { encoding: "utf8", flag: "wx" });
process.stdout.write(serialized);
process.exitCode = failures.length === 0 ? 0 : 1;
