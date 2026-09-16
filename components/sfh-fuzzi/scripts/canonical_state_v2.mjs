import { createHash } from "node:crypto";
import { types as utilTypes } from "node:util";

const SHA256 = /^[0-9a-f]{64}$/;
const IDENTIFIER = /^[A-Za-z0-9][A-Za-z0-9._:/-]{0,127}$/;
const CANONICALIZATION = "LIMEX_STATE_CANONICAL_JSON_V2";
const MAX_ARRAY_LENGTH = 20_000;
const MAX_OBJECT_KEYS = 256;
const MAX_DEPTH = 32;
const MAX_VISITED_NODES = 1_000_000;
const MAX_CANONICAL_UTF8_BYTES = 16 * 1024 * 1024;
const MAX_STRING_UTF8_BYTES = 8 * 1024 * 1024;
const MAX_KEY_UTF8_BYTES = 512;
const MAX_TOTAL_KEY_UTF8_BYTES = 8 * 1024 * 1024;
const Q_KIND = "GOAL_LOCKED_EVIDENCE_SHA256_MATCH_RATIO_PPM";
const TRUSTED_CANONICAL_NODES = new WeakSet();

const exactKeys = (value, expected) => {
  const descriptors = plainDataRecordDescriptors(value);
  return descriptors !== null
    && JSON.stringify(Reflect.ownKeys(descriptors).sort()) === JSON.stringify([...expected].sort());
};
const safeInt = (value, min = 0, max = Number.MAX_SAFE_INTEGER) => Number.isSafeInteger(value)
  && value >= min && value <= max;
const id = (value) => typeof value === "string" && IDENTIFIER.test(value);
const sha = (value) => typeof value === "string" && SHA256.test(value);

function validUnicodeScalarString(value) {
  if (typeof value !== "string" || value !== value.normalize("NFC")) return false;
  for (let index = 0; index < value.length; index += 1) {
    const unit = value.charCodeAt(index);
    if (unit >= 0xd800 && unit <= 0xdbff) {
      const next = value.charCodeAt(index + 1);
      if (!(next >= 0xdc00 && next <= 0xdfff)) return false;
      index += 1;
    } else if (unit >= 0xdc00 && unit <= 0xdfff) return false;
  }
  return true;
}

function jsonQuotedUtf8Bytes(value) {
  let bytes = 2;
  for (let index = 0; index < value.length; index += 1) {
    const unit = value.charCodeAt(index);
    if (unit === 0x22 || unit === 0x5c || unit === 0x08 || unit === 0x09
      || unit === 0x0a || unit === 0x0c || unit === 0x0d) {
      bytes += 2;
    } else if (unit <= 0x1f) {
      bytes += 6;
    } else if (unit <= 0x7f) {
      bytes += 1;
    } else if (unit <= 0x7ff) {
      bytes += 2;
    } else if (unit >= 0xd800 && unit <= 0xdbff) {
      bytes += 4;
      index += 1;
    } else {
      bytes += 3;
    }
  }
  return bytes;
}

function denseDataArray(value) {
  if (utilTypes.isProxy(value) || !Array.isArray(value)
    || Object.getPrototypeOf(value) !== Array.prototype
    || value.length > MAX_ARRAY_LENGTH) return false;
  const ownKeys = Reflect.ownKeys(value);
  if (ownKeys.length !== value.length + 1 || ownKeys.at(-1) !== "length") return false;
  for (let index = 0; index < value.length; index += 1) {
    const key = String(index);
    if (ownKeys[index] !== key) return false;
    const descriptor = Object.getOwnPropertyDescriptor(value, key);
    if (!descriptor || !("value" in descriptor) || descriptor.enumerable !== true) return false;
  }
  const lengthDescriptor = Object.getOwnPropertyDescriptor(value, "length");
  return Boolean(lengthDescriptor && "value" in lengthDescriptor
    && lengthDescriptor.value === value.length && lengthDescriptor.enumerable === false);
}

function plainDataRecordDescriptors(value) {
  if (value === null || typeof value !== "object" || utilTypes.isProxy(value)) return null;
  if (Array.isArray(value)) return null;
  const prototype = Object.getPrototypeOf(value);
  if (prototype !== Object.prototype && prototype !== null) return null;
  const ownKeys = Reflect.ownKeys(value);
  if (ownKeys.length > MAX_OBJECT_KEYS || ownKeys.some((key) => typeof key !== "string"
    || !validUnicodeScalarString(key))) return null;
  const descriptors = Object.getOwnPropertyDescriptors(value);
  for (const key of ownKeys) {
    const descriptor = descriptors[key];
    if (!descriptor || !("value" in descriptor) || descriptor.enumerable !== true) return null;
  }
  return descriptors;
}

function inspectCanonicalDomainUnchecked(value) {
  const seen = new WeakSet();
  const usage = {
    canonical_utf8_bytes: 0,
    maximum_depth: 0,
    maximum_key_utf8_bytes: 0,
    maximum_string_utf8_bytes: 0,
    total_key_utf8_bytes: 0,
    visited_nodes: 0,
  };
  let reason = null;

  const addCanonicalBytes = (amount) => {
    usage.canonical_utf8_bytes += amount;
    if (usage.canonical_utf8_bytes > MAX_CANONICAL_UTF8_BYTES) {
      reason = "CANONICAL_UTF8_BYTES_LIMIT_EXCEEDED";
      return false;
    }
    return true;
  };

  function visit(current, depth, isKey = false) {
    usage.visited_nodes += 1;
    usage.maximum_depth = Math.max(usage.maximum_depth, depth);
    if (usage.visited_nodes > MAX_VISITED_NODES) {
      reason = "VISITED_NODES_LIMIT_EXCEEDED";
      return false;
    }
    if (depth > MAX_DEPTH) {
      reason = "DEPTH_LIMIT_EXCEEDED";
      return false;
    }
    if (current === null) return addCanonicalBytes(4);
    if (typeof current === "boolean") return addCanonicalBytes(current ? 4 : 5);
    if (typeof current === "number") {
      if (!safeInt(current, -Number.MAX_SAFE_INTEGER, Number.MAX_SAFE_INTEGER)
        || Object.is(current, -0)) {
        reason = "NUMBER_OUTSIDE_SAFE_CANONICAL_DOMAIN";
        return false;
      }
      return addCanonicalBytes(String(current).length);
    }
    if (typeof current === "string") {
      const utf8Bytes = Buffer.byteLength(current, "utf8");
      const limit = isKey ? MAX_KEY_UTF8_BYTES : MAX_STRING_UTF8_BYTES;
      if (utf8Bytes > limit) {
        reason = isKey ? "KEY_UTF8_BYTES_LIMIT_EXCEEDED" : "STRING_UTF8_BYTES_LIMIT_EXCEEDED";
        return false;
      }
      if (!validUnicodeScalarString(current)) {
        reason = "STRING_NOT_NFC_OR_INVALID_UNICODE_SCALAR_SEQUENCE";
        return false;
      }
      if (isKey) {
        usage.maximum_key_utf8_bytes = Math.max(usage.maximum_key_utf8_bytes, utf8Bytes);
        usage.total_key_utf8_bytes += utf8Bytes;
        if (usage.total_key_utf8_bytes > MAX_TOTAL_KEY_UTF8_BYTES) {
          reason = "TOTAL_KEY_UTF8_BYTES_LIMIT_EXCEEDED";
          return false;
        }
      } else {
        usage.maximum_string_utf8_bytes = Math.max(usage.maximum_string_utf8_bytes, utf8Bytes);
      }
      return addCanonicalBytes(jsonQuotedUtf8Bytes(current));
    }
    if (typeof current !== "object") {
      reason = "UNSUPPORTED_CANONICAL_TYPE";
      return false;
    }
    if (utilTypes.isProxy(current)) {
      reason = "PROXY_REJECTED";
      return false;
    }
    if (seen.has(current)) {
      reason = "REPEATED_OBJECT_IDENTITY_OR_CYCLE_REJECTED";
      return false;
    }
    seen.add(current);
    if (Array.isArray(current)) {
      if (!denseDataArray(current)) {
        reason = "ARRAY_SHAPE_INVALID";
        return false;
      }
      if (!addCanonicalBytes(2 + Math.max(0, current.length - 1))) return false;
      for (let index = 0; index < current.length; index += 1) {
        const descriptor = Object.getOwnPropertyDescriptor(current, String(index));
        if (!visit(descriptor.value, depth + 1)) return false;
      }
      return true;
    }
    const descriptors = plainDataRecordDescriptors(current);
    if (descriptors === null) {
      reason = "PLAIN_DATA_RECORD_REQUIRED";
      return false;
    }
    const keys = Reflect.ownKeys(descriptors).sort();
    if (!addCanonicalBytes(2 + Math.max(0, keys.length - 1))) return false;
    for (const key of keys) {
      if (!visit(key, depth + 1, true) || !addCanonicalBytes(1)
        || !visit(descriptors[key].value, depth + 1)) return false;
    }
    return true;
  }

  const ok = visit(value, 0);
  return { ok, reason: ok ? null : reason ?? "CANONICAL_DOMAIN_INVALID", usage };
}

export function validateCanonicalDomainV3(value) {
  if (value !== null && typeof value === "object" && !TRUSTED_CANONICAL_NODES.has(value)) return false;
  return inspectCanonicalDomainUnchecked(value).ok;
}

function canonicalJsonValidated(value) {
  if (value === null || typeof value === "boolean" || typeof value === "number"
      || typeof value === "string") return JSON.stringify(value);
  if (Array.isArray(value)) {
    const entries = [];
    for (let index = 0; index < value.length; index += 1) {
      entries.push(canonicalJsonValidated(Object.getOwnPropertyDescriptor(value, String(index)).value));
    }
    return `[${entries.join(",")}]`;
  }
  const descriptors = Object.getOwnPropertyDescriptors(value);
  return `{${Object.keys(descriptors).sort().map((key) =>
    `${JSON.stringify(key)}:${canonicalJsonValidated(descriptors[key].value)}`).join(",")}}`;
}

export function canonicalJsonV2(value) {
  if (value !== null && typeof value === "object" && !TRUSTED_CANONICAL_NODES.has(value)) {
    throw new Error("CANONICAL_DOMAIN_INVALID:UNTRUSTED_RAW_OBJECT_CARRIER");
  }
  const inspection = inspectCanonicalDomainUnchecked(value);
  if (!inspection.ok) throw new Error(`CANONICAL_DOMAIN_INVALID:${inspection.reason}`);
  return canonicalJsonValidated(value);
}

function markTrustedAndFreeze(value) {
  if (value === null || typeof value !== "object") return value;
  const descriptors = Object.getOwnPropertyDescriptors(value);
  for (const key of Reflect.ownKeys(descriptors)) {
    const descriptor = descriptors[key];
    if (key !== "length" && descriptor && "value" in descriptor) markTrustedAndFreeze(descriptor.value);
  }
  Object.freeze(value);
  TRUSTED_CANONICAL_NODES.add(value);
  return value;
}

function trustConstructedTree(value) {
  const inspection = inspectCanonicalDomainUnchecked(value);
  if (!inspection.ok) throw new Error(`INTERNAL_CANONICAL_DOMAIN_INVALID:${inspection.reason}`);
  return markTrustedAndFreeze(value);
}

function canonicalJsonConstructed(value) {
  const trusted = trustConstructedTree(value);
  return canonicalJsonValidated(trusted);
}

function sha256CanonicalConstructed(value) {
  return createHash("sha256").update(canonicalJsonConstructed(value), "utf8").digest("hex");
}

export function parseBoundedJsonCarrierV4(canonicalUtf8Text) {
  if (typeof canonicalUtf8Text !== "string") throw new Error("CANONICAL_CARRIER_TEXT_REQUIRED");
  const inputBytes = Buffer.byteLength(canonicalUtf8Text, "utf8");
  if (inputBytes < 1 || inputBytes > MAX_CANONICAL_UTF8_BYTES) {
    throw new Error("CANONICAL_CARRIER_UTF8_BYTES_LIMIT_EXCEEDED");
  }
  let parsed;
  try { parsed = JSON.parse(canonicalUtf8Text); } catch { throw new Error("CANONICAL_CARRIER_JSON_INVALID"); }
  const inspection = inspectCanonicalDomainUnchecked(parsed);
  if (!inspection.ok) throw new Error(`CANONICAL_DOMAIN_INVALID:${inspection.reason}`);
  return markTrustedAndFreeze(parsed);
}

export function sha256BoundedJsonTextV4(canonicalUtf8Text) {
  return sha256CanonicalV2(parseBoundedJsonCarrierV4(canonicalUtf8Text));
}

export function sha256CanonicalV2(value) {
  return createHash("sha256").update(canonicalJsonV2(value), "utf8").digest("hex");
}

function sortedUniqueById(items) {
  if (!denseDataArray(items)) return false;
  const ids = items.map((entry) => entry?.id);
  return ids.every(id) && new Set(ids).size === ids.length
    && JSON.stringify(ids) === JSON.stringify([...ids].sort());
}

function validateHardInvariants(items) {
  return sortedUniqueById(items) && items.length >= 1 && items.length <= 64
    && items.every((entry) => {
      if (!exactKeys(entry, [
        "expected_evidence_sha256", "id", "observed_evidence_sha256",
        "observed_utf8_base64", "observed_utf8_bytes",
      ]) || !sha(entry.expected_evidence_sha256) || !sha(entry.observed_evidence_sha256)
        || typeof entry.observed_utf8_base64 !== "string"
        || !safeInt(entry.observed_utf8_bytes, 1, 65_536)) return false;
      const bytes = Buffer.from(entry.observed_utf8_base64, "base64");
      return bytes.length === entry.observed_utf8_bytes
        && bytes.toString("base64") === entry.observed_utf8_base64
        && createHash("sha256").update(bytes).digest("hex") === entry.observed_evidence_sha256;
    });
}

function validateBudget(items) {
  return denseDataArray(items) && sortedUniqueById(items) && items.length <= 64
    && items.every((entry) => exactKeys(entry, ["id", "limit", "observed", "unit"])
      && safeInt(entry.observed) && safeInt(entry.limit, 1) && id(entry.unit));
}

function progressEvidencePreimage(diagnostics) {
  return {
    schema_version: "limex-objective-progress-evidence-v2.0.0",
    measurement_kind: Q_KIND,
    hard_invariants: diagnostics.hard_invariants.map((entry) => ({
      expected_evidence_sha256: entry.expected_evidence_sha256,
      id: entry.id,
      observed_evidence_sha256: entry.observed_evidence_sha256,
      observed_utf8_base64: entry.observed_utf8_base64,
      observed_utf8_bytes: entry.observed_utf8_bytes,
    })),
  };
}

function progressGoalLockPreimage(diagnostics) {
  return {
    schema_version: "limex-objective-progress-goal-lock-v2.0.0",
    measurement_kind: Q_KIND,
    expectations: diagnostics.hard_invariants.map((entry) => ({
      expected_evidence_sha256: entry.expected_evidence_sha256,
      id: entry.id,
    })),
  };
}

function invariantPassed(entry) {
  return entry.observed_evidence_sha256 === entry.expected_evidence_sha256;
}

export function objectiveProgressEvidenceRootV2(diagnostics) {
  if (!validateCanonicalDomainV3(diagnostics)
    || !exactKeys(diagnostics, ["hard_invariants", "resource_budget"])
    || !validateHardInvariants(diagnostics.hard_invariants)
    || !validateBudget(diagnostics.resource_budget)) throw new Error("PROGRESS_EVIDENCE_SOURCE_INVALID");
  return sha256CanonicalConstructed(progressEvidencePreimage(diagnostics));
}

export function objectiveProgressGoalLockSha256V2(diagnostics) {
  if (!validateCanonicalDomainV3(diagnostics)
    || !exactKeys(diagnostics, ["hard_invariants", "resource_budget"])
    || !validateHardInvariants(diagnostics.hard_invariants)
    || !validateBudget(diagnostics.resource_budget)) throw new Error("PROGRESS_GOAL_LOCK_SOURCE_INVALID");
  return sha256CanonicalConstructed(progressGoalLockPreimage(diagnostics));
}

export function objectiveProgressQV2(stateVector) {
  if (!validateStateVectorZkV2(stateVector)) throw new Error("STATE_VECTOR_ZK_INVALID");
  const items = stateVector.diagnostics.hard_invariants;
  const passed = items.reduce((count, entry) => count + (invariantPassed(entry) ? 1 : 0), 0);
  return Math.floor((passed * 1_000_000) / items.length);
}

export function createObjectiveProgressDescriptorV2(diagnostics, tolerancePpm = 0) {
  if (!safeInt(tolerancePpm, 0, 1_000_000)) throw new Error("PROGRESS_TOLERANCE_INVALID");
  return trustConstructedTree({
    direction: "HIGHER_IS_BETTER",
    indicator_id: "hard_invariant_pass_ratio_ppm",
    indicator_version: "v2",
    measurement_kind: Q_KIND,
    source_evidence_root_sha256: objectiveProgressEvidenceRootV2(diagnostics),
    tolerance_ppm: tolerancePpm,
  });
}

function validateProgress(progress, diagnostics) {
  return exactKeys(progress, [
    "direction", "indicator_id", "indicator_version", "measurement_kind",
    "source_evidence_root_sha256", "tolerance_ppm",
  ])
    && progress.direction === "HIGHER_IS_BETTER"
    && progress.indicator_id === "hard_invariant_pass_ratio_ppm"
    && progress.indicator_version === "v2"
    && progress.measurement_kind === Q_KIND
    && safeInt(progress.tolerance_ppm, 0, 1_000_000)
    && sha(progress.source_evidence_root_sha256)
    && progress.source_evidence_root_sha256 === objectiveProgressEvidenceRootV2(diagnostics);
}

export function validateStateVectorZkV2(value) {
  try {
    if (!validateCanonicalDomainV3(value) || !exactKeys(value, [
      "bindings", "canonicalization", "diagnostics", "execution", "identity",
      "metric_sample_sha256", "progress", "schema_version", "volatile_exclusions",
    ]) || value.schema_version !== "limex-state-vector-zk-v2.0.0"
      || value.canonicalization !== CANONICALIZATION) return false;
    if (!exactKeys(value.identity, [
      "branch_id", "correlation_id", "gate_id", "quest_id", "step_index", "trajectory_id",
    ]) || !["branch_id", "correlation_id", "gate_id", "quest_id", "trajectory_id"]
      .every((key) => id(value.identity[key])) || !safeInt(value.identity.step_index)) return false;
    if (!exactKeys(value.bindings, [
      "authority_scope_sha256", "candidate_artifact_sha256", "goal_lock_sha256",
      "parent_state_vector_sha256", "proposal_sha256",
    ]) || !["authority_scope_sha256", "candidate_artifact_sha256", "goal_lock_sha256", "proposal_sha256"]
      .every((key) => sha(value.bindings[key]))
      || !(value.bindings.parent_state_vector_sha256 === null
        || sha(value.bindings.parent_state_vector_sha256))) return false;
    if (!exactKeys(value.diagnostics, ["hard_invariants", "resource_budget"])
      || !validateHardInvariants(value.diagnostics.hard_invariants)
      || !validateBudget(value.diagnostics.resource_budget)) return false;
    if (value.bindings.goal_lock_sha256 !== objectiveProgressGoalLockSha256V2(value.diagnostics)) return false;
    if (!validateProgress(value.progress, value.diagnostics)) return false;
    if (!exactKeys(value.execution, ["adapter_action", "host_mutation_count", "phase", "pre_effect"])
      || !["PRE_EFFECT", "POST_EFFECT_OBSERVATION"].includes(value.execution.phase)
      || typeof value.execution.pre_effect !== "boolean"
      || !safeInt(value.execution.host_mutation_count)
      || !id(value.execution.adapter_action)) return false;
    if (!(value.metric_sample_sha256 === null || sha(value.metric_sample_sha256))) return false;
    if (JSON.stringify(value.volatile_exclusions) !== JSON.stringify([
      "absolute_path", "hostname", "pid", "random_nonce", "wall_clock_timestamp",
    ])) return false;
    return true;
  } catch {
    return false;
  }
}

export function bindStateVectorZkV2(value) {
  if (!validateStateVectorZkV2(value)) throw new Error("STATE_VECTOR_ZK_INVALID");
  const canonicalUtf8 = Buffer.from(canonicalJsonV2(value), "utf8");
  return Object.freeze({
    schema_version: "limex-state-vector-zk-binding-v2.0.0",
    canonicalization: CANONICALIZATION,
    canonical_utf8: canonicalUtf8,
    bytes: canonicalUtf8.length,
    sha256: createHash("sha256").update(canonicalUtf8).digest("hex"),
  });
}

export function createStateStorageRecordV2(value) {
  const binding = bindStateVectorZkV2(value);
  const record = trustConstructedTree({
    schema_version: "limex-state-vector-zk-storage-record-v2.0.0",
    encoding: "BASE64_OF_LIMEX_STATE_CANONICAL_JSON_V2_UTF8",
    state_vector_sha256: binding.sha256,
    canonical_utf8_bytes: binding.bytes,
    canonical_utf8_base64: binding.canonical_utf8.toString("base64"),
  });
  if (!verifyStateStorageRecordV2(record)) throw new Error("STATE_STORAGE_RECORD_SELF_VERIFICATION_FAILED");
  return record;
}

export function decodeStateStorageRecordV2(record) {
  try {
    if (!validateCanonicalDomainV3(record) || !exactKeys(record, [
      "canonical_utf8_base64", "canonical_utf8_bytes", "encoding", "schema_version", "state_vector_sha256",
    ]) || record.schema_version !== "limex-state-vector-zk-storage-record-v2.0.0"
      || record.encoding !== "BASE64_OF_LIMEX_STATE_CANONICAL_JSON_V2_UTF8"
      || !sha(record.state_vector_sha256) || !safeInt(record.canonical_utf8_bytes, 1)
      || typeof record.canonical_utf8_base64 !== "string") return null;
    const bytes = Buffer.from(record.canonical_utf8_base64, "base64");
    if (bytes.length !== record.canonical_utf8_bytes
      || bytes.toString("base64") !== record.canonical_utf8_base64
      || createHash("sha256").update(bytes).digest("hex") !== record.state_vector_sha256) return null;
    const parsed = parseBoundedJsonCarrierV4(bytes.toString("utf8"));
    if (!validateStateVectorZkV2(parsed) || canonicalJsonV2(parsed) !== bytes.toString("utf8")) return null;
    return parsed;
  } catch {
    return null;
  }
}

export function verifyStateStorageRecordV2(record) {
  return decodeStateStorageRecordV2(record) !== null;
}

export function materialCycleProjectionV2(value) {
  if (!validateStateVectorZkV2(value)) throw new Error("STATE_VECTOR_ZK_INVALID");
  return trustConstructedTree({
    schema_version: "limex-material-cycle-projection-v2.0.0",
    identity: {
      quest_id: value.identity.quest_id,
      gate_id: value.identity.gate_id,
      branch_id: value.identity.branch_id,
      trajectory_id: value.identity.trajectory_id,
      correlation_id: value.identity.correlation_id,
    },
    bindings: {
      goal_lock_sha256: value.bindings.goal_lock_sha256,
      candidate_artifact_sha256: value.bindings.candidate_artifact_sha256,
      authority_scope_sha256: value.bindings.authority_scope_sha256,
    },
    progress: {
      indicator_id: value.progress.indicator_id,
      indicator_version: value.progress.indicator_version,
      measurement_kind: value.progress.measurement_kind,
      direction: value.progress.direction,
      value_ppm: objectiveProgressQV2(value),
      tolerance_ppm: value.progress.tolerance_ppm,
    },
    execution: value.execution,
    diagnostics: {
      hard_invariants: value.diagnostics.hard_invariants.map((entry) => ({
        id: entry.id,
        passed: invariantPassed(entry),
      })),
      resource_budget: value.diagnostics.resource_budget,
    },
  });
}

export function bindMaterialCycleFingerprintV2(value) {
  const projection = materialCycleProjectionV2(value);
  return trustConstructedTree({
    schema_version: "limex-material-cycle-fingerprint-v2.0.0",
    excluded_fields: [
      "identity.step_index", "bindings.parent_state_vector_sha256", "bindings.proposal_sha256",
      "diagnostics.hard_invariants[*].evidence_sha256", "metric_sample_sha256",
      "progress.source_evidence_root_sha256",
    ],
    sha256: sha256CanonicalV2(projection),
    projection,
  });
}

function progressDeny(reason) {
  return {
    schema_version: "limex-monotone-progress-decision-v2.0.0",
    decision: "DENY",
    reason,
    monotone_within_tolerance: false,
    minimum_transition_margin_ppm: null,
    net_improvement_ppm: null,
    derived_samples: null,
  };
}

export function evaluateMonotoneProgressFromStateRecordsV2(records, contract) {
  try {
    if (!validateCanonicalDomainV3(records) || !validateCanonicalDomainV3(contract)
      || !exactKeys(contract, [
      "branch_id", "correlation_id", "direction", "gate_id", "goal_lock_sha256", "indicator_id", "indicator_version",
      "minimum_net_improvement_ppm", "quest_id", "tolerance_ppm", "trajectory_id", "window_size",
    ]) || contract.direction !== "HIGHER_IS_BETTER"
      || contract.indicator_id !== "hard_invariant_pass_ratio_ppm"
      || contract.indicator_version !== "v2"
      || !["branch_id", "correlation_id", "gate_id", "quest_id", "trajectory_id"].every((key) => id(contract[key]))
      || !sha(contract.goal_lock_sha256)
      || !safeInt(contract.tolerance_ppm, 0, 1_000_000)
      || !safeInt(contract.minimum_net_improvement_ppm, 1, 1_000_000)
      || !safeInt(contract.window_size, 2, 10_000)
      || !Array.isArray(records) || records.length !== contract.window_size) {
      return progressDeny("MONOTONE_PROGRESS_INPUT_INVALID");
    }
    const states = records.map(decodeStateStorageRecordV2);
    if (states.some((state) => state === null)) return progressDeny("MONOTONE_PROGRESS_STATE_RECORD_INVALID");
    const firstStep = states[0].identity.step_index;
    const samples = states.map((state, ordinal) => {
      const identityMatches = ["branch_id", "correlation_id", "gate_id", "quest_id", "trajectory_id"]
        .every((key) => state.identity[key] === contract[key]);
      if (!identityMatches || state.identity.step_index !== firstStep + ordinal
        || state.bindings.goal_lock_sha256 !== contract.goal_lock_sha256
        || state.progress.indicator_id !== contract.indicator_id
        || state.progress.indicator_version !== contract.indicator_version
        || state.progress.tolerance_ppm !== contract.tolerance_ppm) throw new Error("MONOTONE_PROGRESS_STATE_BINDING_INVALID");
      return {
        ordinal,
        step_index: state.identity.step_index,
        state_vector_sha256: records[ordinal].state_vector_sha256,
        source_evidence_root_sha256: state.progress.source_evidence_root_sha256,
        value_ppm: objectiveProgressQV2(state),
      };
    });
    let minimumMargin = Number.MAX_SAFE_INTEGER;
    for (let index = 1; index < samples.length; index += 1) {
      const margin = samples[index].value_ppm + contract.tolerance_ppm - samples[index - 1].value_ppm;
      minimumMargin = Math.min(minimumMargin, margin);
      if (margin < 0) return {
        ...progressDeny("MONOTONICITY_VIOLATION"),
        minimum_transition_margin_ppm: minimumMargin,
        net_improvement_ppm: samples.at(-1).value_ppm - samples[0].value_ppm,
        derived_samples: samples,
      };
    }
    const net = samples.at(-1).value_ppm - samples[0].value_ppm;
    if (net < contract.minimum_net_improvement_ppm) return {
      ...progressDeny("MINIMUM_NET_IMPROVEMENT_NOT_REACHED"),
      monotone_within_tolerance: true,
      minimum_transition_margin_ppm: minimumMargin,
      net_improvement_ppm: net,
      derived_samples: samples,
    };
    return {
      schema_version: "limex-monotone-progress-decision-v2.0.0",
      decision: "PASS",
      reason: "Q_DERIVED_FROM_GOAL_LOCKED_EVIDENCE_SHA256_MATCH_WINDOW",
      monotone_within_tolerance: true,
      minimum_transition_margin_ppm: minimumMargin,
      net_improvement_ppm: net,
      derived_samples: samples,
    };
  } catch {
    return progressDeny("MONOTONE_PROGRESS_STATE_BINDING_INVALID");
  }
}

export const stateCanonicalizationIdV2 = CANONICALIZATION;
export const stateCanonicalArrayCapacityV2 = MAX_ARRAY_LENGTH;
export const objectiveProgressKindV2 = Q_KIND;
export const canonicalResourceLimitsV3 = Object.freeze({
  max_array_length: MAX_ARRAY_LENGTH,
  max_canonical_utf8_bytes: MAX_CANONICAL_UTF8_BYTES,
  max_depth: MAX_DEPTH,
  max_key_utf8_bytes: MAX_KEY_UTF8_BYTES,
  max_object_keys: MAX_OBJECT_KEYS,
  max_string_utf8_bytes: MAX_STRING_UTF8_BYTES,
  max_total_key_utf8_bytes: MAX_TOTAL_KEY_UTF8_BYTES,
  max_visited_nodes: MAX_VISITED_NODES,
  public_object_carrier: "PARSED_FROM_PREBOUNDED_JSON_UTF8_ONLY",
});
