import {
  closeSync,
  existsSync,
  fsyncSync,
  lstatSync,
  mkdirSync,
  openSync,
  readFileSync,
  renameSync,
  rmSync,
  writeFileSync,
} from "node:fs";
import { dirname, isAbsolute, join, resolve } from "node:path";
import { createHash, createPublicKey, verify } from "node:crypto";
import { fileURLToPath } from "node:url";
import process from "node:process";
import { strictJsonParse } from "./strict_json.mjs";
import { validateDefectProjectionStateV4 } from "./defect_event_projector_v4.mjs";
import { parseBoundedJsonCarrierV4 } from "./canonical_state_v2.mjs";

const STATE_SCHEMA = "limex-global-hold-release-adapter-state-v1.0.0";
const CONFIG_SCHEMA = "limex-global-hold-release-adapter-config-v1.0.0";
const TARGET_SCHEMA = "limex-global-hold-reference-target-v1.0.0";
const REQUEST_SCHEMA = "limex-global-hold-release-request-v1.0.0";
const REOPEN_SCHEMA = "limex-global-hold-reopen-event-v1.0.0";
const ACK_SCHEMA = "limex-global-hold-release-postcondition-ack-v1.0.0";
const SHA256 = /^[0-9a-f]{64}$/;
const IDENTIFIER = /^[A-Za-z0-9][A-Za-z0-9._:/-]{0,127}$/;
const MAX_FILE_BYTES = 2 * 1024 * 1024;
const MAX_CLOCK_SKEW_MS = 5 * 60 * 1000;
const MAX_AUTHORITY_WINDOW_MS = 24 * 60 * 60 * 1000;
const PRODUCTION_KEY_ID = "SFH-LIMEX-ED25519-7C26D961C89DF5BF";
const PRODUCTION_SPKI_SHA256 = "7c26d961c89df5bf5a6ce6a5150a601048e8c2e84a3acc43bb8d9b9f732057dc";
const TEST_FAULTS = new Set([
  "NONE",
  "CRASH_AFTER_INTENT_PERSIST",
  "CRASH_AFTER_TARGET_RELEASE_BEFORE_ACK",
  "CRASH_AFTER_ACK_PERSIST",
  "CRASH_AFTER_TARGET_REHOLD_BEFORE_STATE",
]);

const id = (value) => typeof value === "string" && IDENTIFIER.test(value);
const sha = (value) => typeof value === "string" && SHA256.test(value);
const safeInt = (value, minimum = 0) => Number.isSafeInteger(value) && value >= minimum;
const checkedAdvance = (value, amount = 1) => {
  if (!safeInt(value) || !safeInt(amount, 1) || value > Number.MAX_SAFE_INTEGER - amount) {
    throw new Error("ADAPTER_COUNTER_EXHAUSTED");
  }
  return value + amount;
};
const exactKeys = (value, expected) => value !== null && typeof value === "object"
  && !Array.isArray(value)
  && JSON.stringify(Object.keys(value).sort()) === JSON.stringify([...expected].sort());

export function stableJson(value) {
  if (Array.isArray(value)) return `[${value.map(stableJson).join(",")}]`;
  if (value && typeof value === "object") {
    return `{${Object.keys(value).sort().map((key) => `${JSON.stringify(key)}:${stableJson(value[key])}`).join(",")}}`;
  }
  return JSON.stringify(value);
}

export function sha256(value) {
  return createHash("sha256").update(value).digest("hex");
}

function resolveObservedNow(suppliedNowMs) {
  if (!safeInt(suppliedNowMs)) throw new Error("RELEASE_REQUEST_INVALID");
  const observedNowMs = Date.now();
  if (!safeInt(observedNowMs)) throw new Error("LOCAL_TIME_REFERENCE_INVALID");
  if (Math.abs(observedNowMs - suppliedNowMs) > MAX_CLOCK_SKEW_MS) {
    throw new Error("RELEASE_TIME_REFERENCE_MISMATCH");
  }
  return observedNowMs;
}

function publicKeyFingerprint(publicKeyPem) {
  const key = createPublicKey(publicKeyPem);
  if (key.asymmetricKeyType !== "ed25519") throw new Error("AUTHORITY_PUBLIC_KEY_NOT_ED25519");
  return sha256(key.export({ type: "spki", format: "der" }));
}

function validatedRoot(root) {
  if (typeof root !== "string" || !isAbsolute(root) || resolve(root) !== root) {
    throw new Error("ADAPTER_ROOT_MUST_BE_NORMALIZED_ABSOLUTE_PATH");
  }
  if (existsSync(root) && lstatSync(root).isSymbolicLink()) throw new Error("ADAPTER_ROOT_SYMLINK_REJECTED");
  return root;
}

function ensureNoSymlink(path) {
  if (existsSync(path) && lstatSync(path).isSymbolicLink()) throw new Error("ADAPTER_FILE_SYMLINK_REJECTED");
}

function readBoundedText(path) {
  ensureNoSymlink(path);
  const bytes = readFileSync(path);
  if (bytes.length < 1 || bytes.length > MAX_FILE_BYTES) throw new Error("ADAPTER_FILE_SIZE_INVALID");
  return bytes.toString("utf8");
}

function envelope(payload) {
  return {
    payload,
    payload_sha256: sha256(Buffer.from(stableJson(payload), "utf8")),
  };
}

function readEnvelope(path) {
  const parsed = strictJsonParse(readBoundedText(path));
  if (!exactKeys(parsed, ["payload", "payload_sha256"]) || !sha(parsed.payload_sha256)) {
    throw new Error("ADAPTER_ENVELOPE_SHAPE_INVALID");
  }
  const actual = sha256(Buffer.from(stableJson(parsed.payload), "utf8"));
  if (actual !== parsed.payload_sha256) throw new Error("ADAPTER_ENVELOPE_HASH_MISMATCH");
  return parsed;
}

function fsyncDirectory(path) {
  const fd = openSync(path, "r");
  try { fsyncSync(fd); } finally { closeSync(fd); }
}

function atomicWriteEnvelope(path, payload) {
  ensureNoSymlink(path);
  mkdirSync(dirname(path), { recursive: true, mode: 0o700 });
  const tmp = `${path}.tmp-${process.pid}-${sha256(Buffer.from(stableJson(payload))).slice(0, 16)}`;
  const bytes = Buffer.from(`${JSON.stringify(envelope(payload), null, 2)}\n`, "utf8");
  const fd = openSync(tmp, "wx", 0o600);
  try {
    writeFileSync(fd, bytes);
    fsyncSync(fd);
  } finally {
    closeSync(fd);
  }
  renameSync(tmp, path);
  fsyncDirectory(dirname(path));
}

function paths(root) {
  const safeRoot = validatedRoot(root);
  return {
    root: safeRoot,
    config: join(safeRoot, "adapter_config.json"),
    state: join(safeRoot, "adapter_state.json"),
    target: join(safeRoot, "reference_target_hold.json"),
    lock: join(safeRoot, ".adapter-lock"),
  };
}

function withLock(root, execute) {
  const p = paths(root);
  mkdirSync(p.root, { recursive: true, mode: 0o700 });
  ensureNoSymlink(p.lock);
  const ownerToken = sha256(Buffer.from(`${process.pid}:${process.hrtime.bigint()}`));
  const candidate = `${p.lock}.candidate-${process.pid}-${ownerToken.slice(0, 12)}`;
  const ownerPath = join(p.lock, "owner.json");
  mkdirSync(candidate, { mode: 0o700 });
  writeFileSync(join(candidate, "owner.json"), `${JSON.stringify({ pid: process.pid, owner_token: ownerToken })}\n`, {
    encoding: "utf8", mode: 0o600, flag: "wx",
  });
  fsyncDirectory(candidate);
  let acquired = false;
  for (let attempt = 0; attempt < 2 && !acquired; attempt += 1) {
    try {
      renameSync(candidate, p.lock);
      fsyncDirectory(p.root);
      acquired = true;
    } catch (error) {
      if (!["EEXIST", "ENOTEMPTY"].includes(error?.code)) {
        rmSync(candidate, { recursive: true, force: true });
        throw error;
      }
      let stale = false;
      let owner = null;
      try {
        owner = strictJsonParse(readBoundedText(ownerPath));
      } catch {
        stale = true;
      }
      if (!stale && (!safeInt(owner?.pid, 1) || !sha(owner?.owner_token))) stale = true;
      if (!stale) {
        try { process.kill(owner.pid, 0); } catch (probeError) {
          if (probeError?.code === "ESRCH") stale = true;
          else if (probeError?.code === "EPERM") stale = false;
          else {
            rmSync(candidate, { recursive: true, force: true });
            throw probeError;
          }
        }
      }
      if (!stale) {
        rmSync(candidate, { recursive: true, force: true });
        throw new Error("ADAPTER_LOCK_HELD");
      }
      rmSync(p.lock, { recursive: true, force: true });
      fsyncDirectory(p.root);
    }
  }
  if (!acquired) {
    rmSync(candidate, { recursive: true, force: true });
    throw new Error("ADAPTER_LOCK_ACQUISITION_FAILED");
  }
  try {
    return execute(p);
  } finally {
    try {
      const owner = strictJsonParse(readBoundedText(ownerPath));
      if (owner.owner_token === ownerToken && owner.pid === process.pid) {
        rmSync(p.lock, { recursive: true, force: true });
        fsyncDirectory(p.root);
      }
    } catch {
      // Never remove a lock whose ownership cannot be re-established.
    }
  }
}

function validateTrustAnchor(trustAnchor, evidenceClass) {
  if (!exactKeys(trustAnchor, ["key_id", "public_key_pem", "public_key_spki_sha256"])
    || !id(trustAnchor.key_id) || !sha(trustAnchor.public_key_spki_sha256)
    || typeof trustAnchor.public_key_pem !== "string") throw new Error("TRUST_ANCHOR_INVALID");
  if (publicKeyFingerprint(trustAnchor.public_key_pem) !== trustAnchor.public_key_spki_sha256) {
    throw new Error("TRUST_ANCHOR_FINGERPRINT_MISMATCH");
  }
  if (evidenceClass === "RUNTIME_AUTHORITY"
    && (trustAnchor.key_id !== PRODUCTION_KEY_ID
      || trustAnchor.public_key_spki_sha256 !== PRODUCTION_SPKI_SHA256)) {
    throw new Error("RUNTIME_AUTHORITY_NOT_PINNED_PRODUCTION_KEY");
  }
  if (evidenceClass === "SYNTHETIC_TEST_FIXTURE"
    && !trustAnchor.key_id.startsWith("SYNTHETIC-EPHEMERAL-ED25519-")) {
    throw new Error("SYNTHETIC_AUTHORITY_KEY_ID_INVALID");
  }
}

function validateConfig(config) {
  if (!exactKeys(config, [
    "correlation_id", "evidence_class", "gate_id", "initialized_at_ms", "quest_id",
    "schema_version", "test_mode", "trust_anchor",
  ]) || config.schema_version !== CONFIG_SCHEMA
    || ![config.quest_id, config.gate_id, config.correlation_id].every(id)
    || !["RUNTIME_AUTHORITY", "SYNTHETIC_TEST_FIXTURE"].includes(config.evidence_class)
    || typeof config.test_mode !== "boolean" || !safeInt(config.initialized_at_ms)) {
    throw new Error("ADAPTER_CONFIG_INVALID");
  }
  if (config.test_mode !== (config.evidence_class === "SYNTHETIC_TEST_FIXTURE")) {
    throw new Error("ADAPTER_CONFIG_EVIDENCE_MODE_MISMATCH");
  }
  validateTrustAnchor(config.trust_anchor, config.evidence_class);
  return config;
}

function validPendingRequest(value) {
  return exactKeys(value, [
    "authority_fingerprint_sha256", "authority_key_id", "capability_sha256", "expected_epoch",
    "expires_at_ms", "issued_at_ms", "request_id", "request_sha256",
  ]) && id(value.request_id) && sha(value.request_sha256) && id(value.authority_key_id)
    && sha(value.authority_fingerprint_sha256) && sha(value.capability_sha256)
    && safeInt(value.expected_epoch, 1) && safeInt(value.issued_at_ms)
    && safeInt(value.expires_at_ms) && value.expires_at_ms > value.issued_at_ms;
}

function validAck(value) {
  return exactKeys(value, [
    "epoch", "observed_effective_hold", "readback_kind", "request_id", "request_sha256",
    "schema_version", "target_state_sha256",
  ]) && value.schema_version === ACK_SCHEMA
    && value.readback_kind === "REFERENCE_TARGET_FILE_REOPEN_POSTCONDITION"
    && id(value.request_id) && sha(value.request_sha256) && safeInt(value.epoch, 1)
    && value.observed_effective_hold === false && sha(value.target_state_sha256);
}

function validateState(state, config) {
  if (!exactKeys(state, [
    "consumed_capability_sha256", "correlation_id", "desired_hold", "effective_hold", "epoch", "gate_id", "last_ack",
    "last_request_id", "last_request_sha256", "pending_request", "phase", "quest_id",
    "recovery_count", "revoked_authority_fingerprints", "schema_version", "transition_seq",
  ]) || state.schema_version !== STATE_SCHEMA
    || state.quest_id !== config.quest_id || state.gate_id !== config.gate_id
    || state.correlation_id !== config.correlation_id
    || typeof state.desired_hold !== "boolean" || typeof state.effective_hold !== "boolean"
    || !safeInt(state.epoch, 1) || !safeInt(state.transition_seq)
    || !safeInt(state.recovery_count)
    || !["HELD", "RELEASE_REQUEST_PENDING", "RELEASE_APPLYING", "RELEASED_ACKED"].includes(state.phase)
    || !Array.isArray(state.revoked_authority_fingerprints)
    || !state.revoked_authority_fingerprints.every(sha)
    || new Set(state.revoked_authority_fingerprints).size !== state.revoked_authority_fingerprints.length
    || !Array.isArray(state.consumed_capability_sha256)
    || !state.consumed_capability_sha256.every(sha)
    || new Set(state.consumed_capability_sha256).size !== state.consumed_capability_sha256.length
    || JSON.stringify(state.consumed_capability_sha256)
      !== JSON.stringify([...state.consumed_capability_sha256].sort())
    || JSON.stringify(state.revoked_authority_fingerprints)
      !== JSON.stringify([...state.revoked_authority_fingerprints].sort())
    || (state.pending_request !== null && !validPendingRequest(state.pending_request))
    || (state.last_ack !== null && !validAck(state.last_ack))) {
    throw new Error("ADAPTER_STATE_INVALID");
  }
  if (state.phase === "HELD") {
    if (!state.desired_hold || !state.effective_hold || state.pending_request !== null) {
      throw new Error("HELD_STATE_INVARIANT_VIOLATION");
    }
  } else if (state.phase === "RELEASED_ACKED") {
    if (state.desired_hold || state.effective_hold || state.pending_request !== null
      || state.last_ack === null) throw new Error("RELEASED_STATE_INVARIANT_VIOLATION");
  } else if (state.desired_hold || !state.effective_hold || state.pending_request === null) {
    throw new Error("PENDING_STATE_INVARIANT_VIOLATION");
  }
  if ((state.last_request_id === null) !== (state.last_request_sha256 === null)
    || (state.last_request_id !== null && (!id(state.last_request_id) || !sha(state.last_request_sha256)))) {
    throw new Error("LAST_REQUEST_BINDING_INVALID");
  }
  if (state.pending_request !== null
    && (state.pending_request.request_id !== state.last_request_id
      || state.pending_request.request_sha256 !== state.last_request_sha256
      || state.pending_request.expected_epoch !== state.epoch)) {
    throw new Error("PENDING_REQUEST_BINDING_INVALID");
  }
  if (state.last_ack !== null
    && (state.last_ack.request_id !== state.last_request_id
      || state.last_ack.request_sha256 !== state.last_request_sha256
      || state.last_ack.epoch !== state.epoch)) throw new Error("ACK_BINDING_INVALID");
  return state;
}

function validateTarget(target, config) {
  if (!exactKeys(target, [
    "correlation_id", "effective_hold", "epoch", "gate_id", "mutation_seq", "quest_id",
    "release_request_id", "schema_version",
  ]) || target.schema_version !== TARGET_SCHEMA
    || target.quest_id !== config.quest_id || target.gate_id !== config.gate_id
    || target.correlation_id !== config.correlation_id
    || typeof target.effective_hold !== "boolean" || !safeInt(target.epoch, 1)
    || !safeInt(target.mutation_seq)
    || (target.release_request_id !== null && !id(target.release_request_id))) {
    throw new Error("REFERENCE_TARGET_STATE_INVALID");
  }
  if (target.effective_hold !== (target.release_request_id === null)) {
    throw new Error("REFERENCE_TARGET_HOLD_BINDING_INVALID");
  }
  return target;
}

function loadConfig(p) { return validateConfig(readEnvelope(p.config).payload); }
function loadState(p, config) { return validateState(readEnvelope(p.state).payload, config); }
function loadTarget(p, config) { return validateTarget(readEnvelope(p.target).payload, config); }

function requestPreimage(request) {
  const { authority_signature_base64: ignored, ...preimage } = request;
  return preimage;
}

function requestHash(request) {
  return sha256(Buffer.from(stableJson(requestPreimage(request)), "utf8"));
}

function validateCoreTransition(request, config) {
  const before = request.core_state_before;
  const after = request.core_state_after;
  if (!validateDefectProjectionStateV4(before) || !validateDefectProjectionStateV4(after)) {
    throw new Error("CORE_STATE_TRANSITION_INVALID");
  }
  for (const field of ["quest_id", "gate_id", "correlation_id"]) {
    if (before[field] !== config[field] || after[field] !== config[field]) {
      throw new Error("CORE_STATE_SCOPE_MISMATCH");
    }
  }
  if (before.quest_hold !== true || after.quest_hold !== false
    || after.defects.some((entry) => entry.scope === "GLOBAL" && entry.status !== "RESOLVED")) {
    throw new Error("CORE_HELD_TO_UNHELD_TRANSITION_REQUIRED");
  }
}

function validateReleaseRequest(request, config, nowMs) {
  const observedNowMs = resolveObservedNow(nowMs);
  if (!exactKeys(request, [
    "authority_key_id", "authority_signature_base64", "capability_sha256", "core_state_after",
    "core_state_before", "correlation_id", "event_type", "expected_epoch", "expires_at_ms",
    "gate_id", "issued_at_ms", "quest_id", "request_id", "schema_version",
  ]) || request.schema_version !== REQUEST_SCHEMA || request.event_type !== "RELEASE_REQUEST"
    || ![request.quest_id, request.gate_id, request.correlation_id, request.request_id,
      request.authority_key_id].every(id)
    || request.quest_id !== config.quest_id || request.gate_id !== config.gate_id
    || request.correlation_id !== config.correlation_id
    || request.authority_key_id !== config.trust_anchor.key_id
    || !sha(request.capability_sha256) || !safeInt(request.expected_epoch, 1)
    || !safeInt(request.issued_at_ms) || !safeInt(request.expires_at_ms)
    || request.expires_at_ms <= request.issued_at_ms
    || request.expires_at_ms - request.issued_at_ms > MAX_AUTHORITY_WINDOW_MS
    || request.issued_at_ms > observedNowMs + MAX_CLOCK_SKEW_MS
    || request.expires_at_ms <= observedNowMs
    || typeof request.authority_signature_base64 !== "string") {
    throw new Error("RELEASE_REQUEST_INVALID");
  }
  validateCoreTransition(request, config);
  const signature = Buffer.from(request.authority_signature_base64, "base64");
  if (signature.length !== 64 || signature.toString("base64") !== request.authority_signature_base64) {
    throw new Error("RELEASE_AUTHORITY_SIGNATURE_ENCODING_INVALID");
  }
  const preimageBytes = Buffer.from(stableJson(requestPreimage(request)), "utf8");
  if (!verify(null, preimageBytes, createPublicKey(config.trust_anchor.public_key_pem), signature)) {
    throw new Error("RELEASE_AUTHORITY_SIGNATURE_INVALID");
  }
  return { request_sha256: requestHash(request), observed_now_ms: observedNowMs };
}

function baseHeldState(
  config, epoch = 1, transitionSeq = 0, recoveryCount = 0, revoked = [], consumed = [],
) {
  return {
    schema_version: STATE_SCHEMA,
    quest_id: config.quest_id,
    gate_id: config.gate_id,
    correlation_id: config.correlation_id,
    epoch,
    phase: "HELD",
    desired_hold: true,
    effective_hold: true,
    pending_request: null,
    last_request_id: null,
    last_request_sha256: null,
    last_ack: null,
    revoked_authority_fingerprints: [...new Set(revoked)].sort(),
    consumed_capability_sha256: [...new Set(consumed)].sort(),
    transition_seq: transitionSeq,
    recovery_count: recoveryCount,
  };
}

function heldTarget(config, epoch = 1, mutationSeq = 0) {
  return {
    schema_version: TARGET_SCHEMA,
    quest_id: config.quest_id,
    gate_id: config.gate_id,
    correlation_id: config.correlation_id,
    epoch,
    effective_hold: true,
    release_request_id: null,
    mutation_seq: mutationSeq,
  };
}

export function initializeAdapter(root, input) {
  return withLock(root, (p) => {
    if ([p.config, p.state, p.target].some(existsSync)) throw new Error("ADAPTER_ALREADY_INITIALIZED");
    const config = validateConfig({ ...input, schema_version: CONFIG_SCHEMA });
    atomicWriteEnvelope(p.config, config);
    atomicWriteEnvelope(p.target, heldTarget(config));
    atomicWriteEnvelope(p.state, baseHeldState(config));
    return { status: "PASS", decision: "INITIALIZED_HELD", config_sha256: readEnvelope(p.config).payload_sha256 };
  });
}

export function submitReleaseRequest(root, request, nowMs) {
  return withLock(root, (p) => {
    const config = loadConfig(p);
    const state = loadState(p, config);
    const target = loadTarget(p, config);
    const { request_sha256: hash } = validateReleaseRequest(request, config, nowMs);
    if (state.last_request_id === request.request_id) {
      if (state.last_request_sha256 !== hash) throw new Error("RELEASE_REQUEST_ID_CONTENT_CONFLICT");
    }
    if (request.expected_epoch !== state.epoch) throw new Error("RELEASE_REQUEST_EPOCH_STALE");
    if (state.revoked_authority_fingerprints.includes(config.trust_anchor.public_key_spki_sha256)) {
      throw new Error("RELEASE_AUTHORITY_REVOKED");
    }
    if (state.last_request_id === request.request_id) {
      if (state.phase !== "RELEASE_REQUEST_PENDING"
        || state.pending_request?.request_id !== request.request_id
        || state.pending_request?.request_sha256 !== hash
        || !target.effective_hold || target.epoch !== state.epoch) {
        throw new Error("RELEASE_REQUEST_REPLAY_NOT_PENDING");
      }
      return { status: "PASS", decision: "IDEMPOTENT_NO_OP", request_sha256: hash };
    }
    if (state.consumed_capability_sha256.includes(request.capability_sha256)) {
      throw new Error("RELEASE_CAPABILITY_ALREADY_CONSUMED");
    }
    if (state.phase !== "HELD" || !target.effective_hold || target.epoch !== state.epoch) {
      throw new Error("RELEASE_REQUEST_REQUIRES_COHERENT_HELD_STATE");
    }
    const nextTransitionSeq = checkedAdvance(state.transition_seq);
    const pending = {
      request_id: request.request_id,
      request_sha256: hash,
      authority_key_id: request.authority_key_id,
      authority_fingerprint_sha256: config.trust_anchor.public_key_spki_sha256,
      capability_sha256: request.capability_sha256,
      expected_epoch: request.expected_epoch,
      issued_at_ms: request.issued_at_ms,
      expires_at_ms: request.expires_at_ms,
    };
    const next = {
      ...state,
      phase: "RELEASE_REQUEST_PENDING",
      desired_hold: false,
      pending_request: pending,
      last_request_id: request.request_id,
      last_request_sha256: hash,
      transition_seq: nextTransitionSeq,
    };
    atomicWriteEnvelope(p.state, next);
    return { status: "PASS", decision: "RELEASE_REQUEST_PENDING", request_sha256: hash };
  });
}

function maybeCrash(config, faultAt, checkpoint) {
  if (faultAt === checkpoint) {
    if (!config.test_mode) throw new Error("FAULT_INJECTION_REQUIRES_SYNTHETIC_TEST_MODE");
    process.exit(97);
  }
}

export function commitRelease(root, request, capabilityPreimage, nowMs, faultAt = "NONE") {
  if (!TEST_FAULTS.has(faultAt)) throw new Error("FAULT_CHECKPOINT_INVALID");
  if (!Buffer.isBuffer(capabilityPreimage) || capabilityPreimage.length < 16
    || capabilityPreimage.length > 4096) throw new Error("CAPABILITY_PREIMAGE_INVALID");
  return withLock(root, (p) => {
    const config = loadConfig(p);
    let state = loadState(p, config);
    let target = loadTarget(p, config);
    const { request_sha256: hash } = validateReleaseRequest(request, config, nowMs);
    if (sha256(capabilityPreimage) !== request.capability_sha256) {
      throw new Error("RELEASE_CAPABILITY_PREIMAGE_MISMATCH");
    }
    if (state.phase === "RELEASED_ACKED" && state.last_request_id === request.request_id
      && state.last_request_sha256 === hash) {
      const targetEnvelope = readEnvelope(p.target);
      const coherent = state.last_ack !== null
        && state.last_ack.observed_effective_hold === false
        && target.effective_hold === false
        && target.epoch === state.epoch
        && target.release_request_id === state.last_ack.request_id
        && targetEnvelope.payload_sha256 === state.last_ack.target_state_sha256;
      if (!coherent) throw new Error("RELEASE_POSTCONDITION_READBACK_MISMATCH");
      return { status: "PASS", decision: "IDEMPOTENT_ALREADY_RELEASED", ack: state.last_ack };
    }
    if (state.phase !== "RELEASE_REQUEST_PENDING" || state.pending_request?.request_id !== request.request_id
      || state.pending_request?.request_sha256 !== hash) throw new Error("BOUND_PENDING_RELEASE_REQUEST_REQUIRED");
    if (request.expected_epoch !== state.epoch || request.expires_at_ms <= Date.now()) {
      throw new Error("RELEASE_COMMIT_EXPIRED_OR_STALE");
    }
    if (state.revoked_authority_fingerprints.includes(config.trust_anchor.public_key_spki_sha256)) {
      throw new Error("RELEASE_AUTHORITY_REVOKED");
    }
    const applyingTransitionSeq = checkedAdvance(state.transition_seq);
    const releasedTransitionSeq = checkedAdvance(state.transition_seq, 2);
    const nextTargetMutationSeq = checkedAdvance(target.mutation_seq);
    state = {
      ...state,
      phase: "RELEASE_APPLYING",
      consumed_capability_sha256: [...state.consumed_capability_sha256, request.capability_sha256].sort(),
      transition_seq: applyingTransitionSeq,
    };
    atomicWriteEnvelope(p.state, state);
    maybeCrash(config, faultAt, "CRASH_AFTER_INTENT_PERSIST");

    target = {
      ...target,
      effective_hold: false,
      release_request_id: request.request_id,
      mutation_seq: nextTargetMutationSeq,
    };
    atomicWriteEnvelope(p.target, target);
    maybeCrash(config, faultAt, "CRASH_AFTER_TARGET_RELEASE_BEFORE_ACK");

    const readback = loadTarget(p, config);
    if (readback.effective_hold !== false || readback.release_request_id !== request.request_id
      || readback.epoch !== state.epoch) throw new Error("RELEASE_POSTCONDITION_READBACK_MISMATCH");
    const targetEnvelope = readEnvelope(p.target);
    const ack = {
      schema_version: ACK_SCHEMA,
      readback_kind: "REFERENCE_TARGET_FILE_REOPEN_POSTCONDITION",
      request_id: request.request_id,
      request_sha256: hash,
      epoch: state.epoch,
      observed_effective_hold: false,
      target_state_sha256: targetEnvelope.payload_sha256,
    };
    state = {
      ...state,
      phase: "RELEASED_ACKED",
      desired_hold: false,
      effective_hold: false,
      pending_request: null,
      last_ack: ack,
      transition_seq: releasedTransitionSeq,
    };
    atomicWriteEnvelope(p.state, state);
    maybeCrash(config, faultAt, "CRASH_AFTER_ACK_PERSIST");
    return { status: "PASS", decision: "RELEASED_AFTER_BOUND_POSTCONDITION_ACK", ack };
  });
}

function validateReopenEvent(event, config) {
  if (!exactKeys(event, [
    "correlation_id", "event_id", "event_sha256", "event_type", "expected_epoch", "gate_id",
    "occurred_at_ms", "quest_id", "reopen_fingerprint_sha256", "schema_version",
  ]) || event.schema_version !== REOPEN_SCHEMA || event.event_type !== "GLOBAL_REOPEN"
    || ![event.quest_id, event.gate_id, event.correlation_id, event.event_id].every(id)
    || event.quest_id !== config.quest_id || event.gate_id !== config.gate_id
    || event.correlation_id !== config.correlation_id || !safeInt(event.expected_epoch, 1)
    || !safeInt(event.occurred_at_ms) || !sha(event.reopen_fingerprint_sha256)
    || !sha(event.event_sha256)) throw new Error("REOPEN_EVENT_INVALID");
  const { event_sha256: ignored, ...preimage } = event;
  const expectedHash = sha256(Buffer.from(stableJson(preimage), "utf8"));
  if (event.event_sha256 !== expectedHash) throw new Error("REOPEN_EVENT_HASH_MISMATCH");
}

export function applyGlobalReopen(root, event, faultAt = "NONE") {
  if (!TEST_FAULTS.has(faultAt)) throw new Error("FAULT_CHECKPOINT_INVALID");
  return withLock(root, (p) => {
    const config = loadConfig(p);
    const state = loadState(p, config);
    const target = loadTarget(p, config);
    validateReopenEvent(event, config);
    if (event.expected_epoch !== state.epoch) throw new Error("REOPEN_EVENT_EPOCH_STALE");
    const nextEpoch = checkedAdvance(state.epoch);
    const nextTargetMutationSeq = checkedAdvance(target.mutation_seq);
    const nextTransitionSeq = checkedAdvance(state.transition_seq);
    atomicWriteEnvelope(p.target, {
      ...target,
      epoch: nextEpoch,
      effective_hold: true,
      release_request_id: null,
      mutation_seq: nextTargetMutationSeq,
    });
    maybeCrash(config, faultAt, "CRASH_AFTER_TARGET_REHOLD_BEFORE_STATE");
    const next = {
      ...baseHeldState(config, nextEpoch, nextTransitionSeq,
        state.recovery_count, state.revoked_authority_fingerprints, state.consumed_capability_sha256),
      last_request_id: state.last_request_id,
      last_request_sha256: state.last_request_sha256,
    };
    atomicWriteEnvelope(p.state, next);
    return { status: "PASS", decision: "GLOBAL_REOPEN_DOMINATES_RELEASE", epoch: nextEpoch };
  });
}

export function revokeAuthority(root, authorityFingerprintSha256) {
  if (!sha(authorityFingerprintSha256)) throw new Error("AUTHORITY_REVOCATION_FINGERPRINT_INVALID");
  return withLock(root, (p) => {
    const config = loadConfig(p);
    const state = loadState(p, config);
    const target = loadTarget(p, config);
    const nextEpoch = checkedAdvance(state.epoch);
    const nextTargetMutationSeq = checkedAdvance(target.mutation_seq);
    const nextTransitionSeq = checkedAdvance(state.transition_seq);
    const revoked = [...new Set([...state.revoked_authority_fingerprints, authorityFingerprintSha256])].sort();
    atomicWriteEnvelope(p.target, {
      ...target,
      epoch: nextEpoch,
      effective_hold: true,
      release_request_id: null,
      mutation_seq: nextTargetMutationSeq,
    });
    const next = {
      ...baseHeldState(config, nextEpoch, nextTransitionSeq, state.recovery_count, revoked,
        state.consumed_capability_sha256),
      last_request_id: state.last_request_id,
      last_request_sha256: state.last_request_sha256,
    };
    atomicWriteEnvelope(p.state, next);
    return { status: "PASS", decision: "AUTHORITY_REVOKED_AND_HELD", epoch: nextEpoch };
  });
}

function quarantineCorruptState(path) {
  if (!existsSync(path)) return null;
  ensureNoSymlink(path);
  const bytes = readFileSync(path);
  const digest = sha256(bytes);
  const destination = `${path}.corrupt-${digest}`;
  if (!existsSync(destination)) renameSync(path, destination);
  else rmSync(path, { force: true });
  return digest;
}

export function recoverAdapter(root) {
  return withLock(root, (p) => {
    const config = loadConfig(p);
    let state;
    let target;
    let stateCorruptionSha256 = null;
    let targetCorruptionSha256 = null;
    try { state = loadState(p, config); } catch {
      if (existsSync(p.state)) {
        ensureNoSymlink(p.state);
        stateCorruptionSha256 = sha256(readFileSync(p.state));
      }
    }
    try { target = loadTarget(p, config); } catch {
      if (existsSync(p.target)) {
        ensureNoSymlink(p.target);
        targetCorruptionSha256 = sha256(readFileSync(p.target));
      }
    }
    if (state?.phase === "RELEASED_ACKED" && target !== undefined && !target.effective_hold
      && target.epoch === state.epoch && target.release_request_id === state.last_ack?.request_id
      && readEnvelope(p.target).payload_sha256 === state.last_ack?.target_state_sha256) {
      return { status: "PASS", decision: "ACKED_RELEASE_RETAINED", epoch: state.epoch };
    }
    const stateUnavailable = state === undefined;
    const targetUnavailable = target === undefined;
    const targetBase = target ?? heldTarget(config, Math.max(state?.epoch ?? 1, 1), 0);
    const nextEpoch = checkedAdvance(Math.max(state?.epoch ?? 1, targetBase.epoch));
    const nextTargetMutationSeq = checkedAdvance(targetBase.mutation_seq);
    const nextTransitionSeq = checkedAdvance(state?.transition_seq ?? 0);
    const nextRecoveryCount = checkedAdvance(state?.recovery_count ?? 0);
    const revoked = stateUnavailable
      ? [config.trust_anchor.public_key_spki_sha256]
      : state.revoked_authority_fingerprints;
    const consumed = stateUnavailable ? [] : state.consumed_capability_sha256;
    if (stateUnavailable && existsSync(p.state)) quarantineCorruptState(p.state);
    if (targetUnavailable && existsSync(p.target)) quarantineCorruptState(p.target);
    atomicWriteEnvelope(p.target, {
      ...targetBase,
      epoch: nextEpoch,
      effective_hold: true,
      release_request_id: null,
      mutation_seq: nextTargetMutationSeq,
    });
    const next = {
      ...baseHeldState(config, nextEpoch, nextTransitionSeq,
        nextRecoveryCount, revoked, consumed),
      last_request_id: stateUnavailable ? null : state.last_request_id,
      last_request_sha256: stateUnavailable ? null : state.last_request_sha256,
    };
    atomicWriteEnvelope(p.state, next);
    return {
      status: "PASS",
      decision: stateUnavailable
        ? (stateCorruptionSha256 === null
          ? "MISSING_STATE_AUTHORITY_REVOKED_HELD"
          : "CORRUPT_STATE_QUARANTINED_AND_AUTHORITY_REVOKED_HELD")
        : "RECOVERED_TO_HELD",
      corruption_sha256: stateCorruptionSha256,
      target_corruption_sha256: targetCorruptionSha256,
      epoch: nextEpoch,
    };
  });
}

export function readPostcondition(root) {
  try {
    const p = paths(root);
    const config = loadConfig(p);
    const stateEnvelope = readEnvelope(p.state);
    const state = validateState(stateEnvelope.payload, config);
    const targetEnvelope = readEnvelope(p.target);
    const target = validateTarget(targetEnvelope.payload, config);
    const referencePostconditionSatisfied = state.phase === "RELEASED_ACKED"
      && state.desired_hold === false && state.effective_hold === false
      && target.effective_hold === false && target.epoch === state.epoch
      && target.release_request_id === state.last_ack?.request_id
      && targetEnvelope.payload_sha256 === state.last_ack?.target_state_sha256;
    return {
      status: referencePostconditionSatisfied
        ? "REFERENCE_POSTCONDITION_OBSERVED"
        : "FAIL_CLOSED",
      reference_postcondition_satisfied: referencePostconditionSatisfied,
      action_allowed: false,
      fail_closed: true,
      state_phase: state.phase,
      state_sha256: stateEnvelope.payload_sha256,
      target_state_sha256: targetEnvelope.payload_sha256,
      epoch: state.epoch,
      reason: referencePostconditionSatisfied
        ? "PRODUCT_RUNTIME_BINDING_REQUIRED"
        : "REFERENCE_RELEASE_POSTCONDITION_NOT_SATISFIED",
    };
  } catch (error) {
    const rawReason = error?.message ?? String(error);
    const reason = /^[A-Z0-9_]+$/.test(rawReason)
      ? rawReason
      : "ADAPTER_POSTCONDITION_UNREADABLE_OR_INVALID";
    return {
      status: "FAIL_CLOSED",
      reference_postcondition_satisfied: false,
      action_allowed: false,
      fail_closed: true,
      state_phase: "UNREADABLE_OR_INVALID",
      reason,
    };
  }
}

function readInputFile(path) {
  return parseBoundedJsonCarrierV4(readBoundedText(path));
}

function cli() {
  const [command, root, inputPath, auxiliary, nowRaw, faultAt = "NONE"] = process.argv.slice(2);
  try {
    let result;
    if (command === "initialize") result = initializeAdapter(root, readInputFile(inputPath));
    else if (command === "request") result = submitReleaseRequest(root, readInputFile(inputPath), Number(auxiliary));
    else if (command === "commit") {
      const capability = Buffer.from(readBoundedText(auxiliary), "utf8");
      result = commitRelease(root, readInputFile(inputPath), capability, Number(nowRaw), faultAt);
    } else if (command === "reopen") result = applyGlobalReopen(root, readInputFile(inputPath), auxiliary ?? "NONE");
    else if (command === "revoke") result = revokeAuthority(root, inputPath);
    else if (command === "recover") result = recoverAdapter(root);
    else if (command === "probe" || command === "inspect-reference") {
      result = readPostcondition(root);
      if (command === "probe" && result.action_allowed !== true) process.exitCode = 2;
    }
    else throw new Error("ADAPTER_CLI_COMMAND_INVALID");
    process.stdout.write(`${JSON.stringify(result)}\n`);
  } catch (error) {
    process.stdout.write(`${JSON.stringify({ status: "DENY", reason: error?.message ?? String(error) })}\n`);
    process.exitCode = 2;
  }
}

if (process.argv[1] && resolve(process.argv[1]) === resolve(fileURLToPath(import.meta.url))) cli();
