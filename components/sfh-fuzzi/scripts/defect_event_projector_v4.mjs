import { createHash } from "node:crypto";
import { TextDecoder } from "node:util";
import {
  parseBoundedJsonCarrierV4,
  sha256BoundedJsonTextV4,
  validateCanonicalDomainV3,
} from "./canonical_state_v2.mjs";

const SHA256 = /^[0-9a-f]{64}$/;
const IDENTIFIER = /^[A-Za-z0-9][A-Za-z0-9._:/-]{0,127}$/;
const MAX_DEFECTS = 10_000;
const MAX_ACCEPTED_EVENTS = 20_000;
const MAX_CLOSURE_ARTIFACT_BYTES = 65_536;
const EVENT_KINDS = new Set([
  "LOCAL_MODULE_DEFECT",
  "GLOBAL_SIGNATURE_DEFECT",
  "DEFECT_CLOSURE_REVALIDATED",
  "DEFECT_RECURRENCE",
]);
const REQUIRED_ADAPTER_ACTION_KINDS = new Set([
  "NO_OP",
  "BLOCK_BRANCH",
  "UNQUARANTINE_BRANCH",
  "QUEST_HOLD",
]);
const INDEPENDENCE_MARKER = "AUDITOR_DISTINCT_FROM_BUILDER__READ_ONLY";
const ACCEPTANCE_KIND = "INDEPENDENT_READ_ONLY_REAUDIT_ACCEPTANCE";
const utf8Decoder = new TextDecoder("utf-8", { fatal: true });

const compareUtf16 = (a, b) => a < b ? -1 : a > b ? 1 : 0;
const sha = (value) => typeof value === "string" && SHA256.test(value);
const id = (value) => typeof value === "string" && IDENTIFIER.test(value);
const safeInt = (value, minimum = 0, maximum = Number.MAX_SAFE_INTEGER) =>
  Number.isSafeInteger(value) && value >= minimum && value <= maximum;
const exactKeys = (value, expected) => validateCanonicalDomainV3(value)
  && value !== null && typeof value === "object" && !Array.isArray(value)
  && JSON.stringify(Object.keys(value).sort()) === JSON.stringify([...expected].sort());
const trusted = (value) => parseBoundedJsonCarrierV4(JSON.stringify(value));

function action(kind, branchId = null) {
  if (!REQUIRED_ADAPTER_ACTION_KINDS.has(kind)) throw new Error("REQUIRED_ADAPTER_ACTION_KIND_INVALID");
  if ((kind === "BLOCK_BRANCH" || kind === "UNQUARANTINE_BRANCH") !== (branchId !== null)
    || (branchId !== null && !id(branchId))) throw new Error("REQUIRED_ADAPTER_ACTION_SHAPE_INVALID");
  const result = branchId === null ? { kind } : { branch_id: branchId, kind };
  return Object.freeze(result);
}

function decision(decisionValue, reason, statePrime, requiredAdapterAction) {
  return Object.freeze({
    schema_version: "limex-defect-projection-decision-v4.0.0",
    decision: decisionValue,
    reason,
    state_prime: statePrime,
    required_adapter_action: requiredAdapterAction,
    effectful_action_allowed: false,
    diagnostic_authority: "NONE",
    authorized_transition: null,
  });
}

function deny(reason, statePrime = null) {
  return decision("DENY", reason, statePrime, action("NO_OP"));
}

function noOp(reason, statePrime) {
  return decision("PASS", reason, statePrime, action("NO_OP"));
}

function sortedUniqueIds(value, maximum = MAX_ACCEPTED_EVENTS) {
  return Array.isArray(value) && value.length <= maximum && value.every(id)
    && new Set(value).size === value.length
    && JSON.stringify(value) === JSON.stringify([...value].sort(compareUtf16));
}

function validArtifactBinding(value) {
  if (!exactKeys(value, ["sha256", "utf8_base64", "utf8_bytes"])
    || !sha(value.sha256) || typeof value.utf8_base64 !== "string"
    || !safeInt(value.utf8_bytes, 1, MAX_CLOSURE_ARTIFACT_BYTES)) return false;
  const bytes = Buffer.from(value.utf8_base64, "base64");
  try {
    const decoded = utf8Decoder.decode(bytes);
    return bytes.length === value.utf8_bytes
      && bytes.toString("base64") === value.utf8_base64
      && Buffer.from(decoded, "utf8").equals(bytes)
      && createHash("sha256").update(bytes).digest("hex") === value.sha256;
  } catch {
    return false;
  }
}

function validIndependentAcceptanceBinding(value) {
  return exactKeys(value, [
    "acceptance_decision", "artifact", "attestation_kind", "auditor_identity",
    "builder_identity", "independence_marker", "subject_correlation_id", "subject_defect_id",
    "subject_gate_id", "subject_quest_id",
  ]) && value.acceptance_decision === "PASS"
    && value.attestation_kind === ACCEPTANCE_KIND
    && value.independence_marker === INDEPENDENCE_MARKER
    && id(value.auditor_identity) && id(value.builder_identity)
    && value.auditor_identity !== value.builder_identity
    && [value.subject_quest_id, value.subject_gate_id, value.subject_correlation_id,
      value.subject_defect_id].every(id)
    && validArtifactBinding(value.artifact);
}

function validClosureRecord(value) {
  return exactKeys(value, [
    "closure_event_id", "complete_reaudit", "correction", "independent_acceptance",
    "regression_guard", "root_cause",
  ]) && id(value.closure_event_id)
    && validArtifactBinding(value.root_cause)
    && validArtifactBinding(value.regression_guard)
    && validArtifactBinding(value.correction)
    && validArtifactBinding(value.complete_reaudit)
    && validIndependentAcceptanceBinding(value.independent_acceptance);
}

function validDefect(value) {
  if (!exactKeys(value, [
    "affected_branch_id", "closure", "declaration_event_id", "defect_fingerprint_sha256",
    "defect_id", "last_transition_event_id", "recurrence_count", "reopen_fingerprint_sha256",
    "scope", "status",
  ]) || !id(value.defect_id) || !id(value.declaration_event_id)
    || !id(value.last_transition_event_id) || !sha(value.defect_fingerprint_sha256)
    || !sha(value.reopen_fingerprint_sha256) || !safeInt(value.recurrence_count, 0)
    || !["LOCAL", "GLOBAL"].includes(value.scope)
    || !["OPEN", "BLOCKED", "RESOLVED"].includes(value.status)) return false;
  if (value.scope === "LOCAL") {
    if (!id(value.affected_branch_id)) return false;
  } else if (value.affected_branch_id !== null) return false;
  if (value.status === "RESOLVED") return validClosureRecord(value.closure);
  return value.closure === null;
}

function derivedBlockedBranches(defects) {
  return [...new Set(defects
    .filter((entry) => entry.scope === "LOCAL" && entry.status !== "RESOLVED")
    .map((entry) => entry.affected_branch_id))].sort(compareUtf16);
}

function derivedQuestHold(defects) {
  return defects.some((entry) => entry.scope === "GLOBAL" && entry.status !== "RESOLVED");
}

export function validateDefectProjectionStateV4(value) {
  try {
    if (!exactKeys(value, [
      "accepted_events", "blocked_branches", "correlation_id", "defects", "gate_id",
      "quest_hold", "quest_id", "schema_version",
    ]) || value.schema_version !== "limex-defect-projection-state-v4.0.0"
      || !id(value.quest_id) || !id(value.gate_id) || !id(value.correlation_id)
      || typeof value.quest_hold !== "boolean" || !Array.isArray(value.accepted_events)
      || value.accepted_events.length > MAX_ACCEPTED_EVENTS
      || !value.accepted_events.every((entry) => exactKeys(entry, ["event_id", "event_sha256"])
        && id(entry.event_id) && sha(entry.event_sha256))
      || new Set(value.accepted_events.map((entry) => entry.event_id)).size !== value.accepted_events.length
      || JSON.stringify(value.accepted_events.map((entry) => entry.event_id))
        !== JSON.stringify(value.accepted_events.map((entry) => entry.event_id).sort(compareUtf16))
      || !Array.isArray(value.defects) || value.defects.length > MAX_DEFECTS
      || !value.defects.every(validDefect)
      || new Set(value.defects.map((entry) => entry.defect_id)).size !== value.defects.length
      || JSON.stringify(value.defects.map((entry) => entry.defect_id))
        !== JSON.stringify(value.defects.map((entry) => entry.defect_id).sort(compareUtf16))
      || !sortedUniqueIds(value.blocked_branches, MAX_DEFECTS)) return false;
    return JSON.stringify(value.blocked_branches) === JSON.stringify(derivedBlockedBranches(value.defects))
      && value.quest_hold === derivedQuestHold(value.defects);
  } catch {
    return false;
  }
}

export function createDefectProjectionStateV4(questId, gateId, correlationId) {
  if (![questId, gateId, correlationId].every(id)) throw new Error("DEFECT_PROJECTION_SCOPE_INVALID");
  return trusted({
    schema_version: "limex-defect-projection-state-v4.0.0",
    quest_id: questId,
    gate_id: gateId,
    correlation_id: correlationId,
    quest_hold: false,
    blocked_branches: [],
    defects: [],
    accepted_events: [],
  });
}

function validPayload(kind, payload) {
  if (kind === "LOCAL_MODULE_DEFECT") {
    return exactKeys(payload, [
      "affected_branch_id", "defect_fingerprint_sha256", "defect_id", "reopen_fingerprint_sha256",
    ]) && id(payload.affected_branch_id) && id(payload.defect_id)
      && sha(payload.defect_fingerprint_sha256) && sha(payload.reopen_fingerprint_sha256);
  }
  if (kind === "GLOBAL_SIGNATURE_DEFECT") {
    return exactKeys(payload, ["defect_fingerprint_sha256", "defect_id", "reopen_fingerprint_sha256"])
      && id(payload.defect_id) && sha(payload.defect_fingerprint_sha256)
      && sha(payload.reopen_fingerprint_sha256);
  }
  if (kind === "DEFECT_CLOSURE_REVALIDATED") {
    return exactKeys(payload, [
      "complete_reaudit", "correction", "defect_id", "independent_acceptance",
      "regression_guard", "root_cause",
    ])
      && id(payload.defect_id) && validArtifactBinding(payload.root_cause)
      && validArtifactBinding(payload.regression_guard)
      && validArtifactBinding(payload.correction)
      && validArtifactBinding(payload.complete_reaudit)
      && validIndependentAcceptanceBinding(payload.independent_acceptance);
  }
  if (kind === "DEFECT_RECURRENCE") {
    return exactKeys(payload, ["defect_id", "recurrence_fingerprint_sha256"])
      && id(payload.defect_id) && sha(payload.recurrence_fingerprint_sha256);
  }
  return false;
}

function eventPreimage(event) {
  return {
    schema_version: event.schema_version,
    quest_id: event.quest_id,
    gate_id: event.gate_id,
    correlation_id: event.correlation_id,
    event_id: event.event_id,
    kind: event.kind,
    payload: event.payload,
  };
}

function validEventDraft(value) {
  const structurallyValid = exactKeys(value, [
    "correlation_id", "event_id", "gate_id", "kind", "payload", "quest_id", "schema_version",
  ]) && value.schema_version === "limex-defect-projection-event-v4.0.0"
    && [value.quest_id, value.gate_id, value.correlation_id, value.event_id].every(id)
    && EVENT_KINDS.has(value.kind) && validPayload(value.kind, value.payload);
  if (!structurallyValid || value.kind !== "DEFECT_CLOSURE_REVALIDATED") return structurallyValid;
  const acceptance = value.payload.independent_acceptance;
  return acceptance.subject_quest_id === value.quest_id
    && acceptance.subject_gate_id === value.gate_id
    && acceptance.subject_correlation_id === value.correlation_id
    && acceptance.subject_defect_id === value.payload.defect_id;
}

function validBoundEvent(value) {
  if (!exactKeys(value, [
    "correlation_id", "event_id", "event_sha256", "gate_id", "kind", "payload", "quest_id",
    "schema_version",
  ]) || !sha(value.event_sha256)) return false;
  const draft = trusted(eventPreimage(value));
  return validEventDraft(draft);
}

export function bindDefectProjectionEventV4(eventDraft) {
  if (!validEventDraft(eventDraft)) throw new Error("DEFECT_PROJECTION_EVENT_DRAFT_INVALID");
  const preimage = eventPreimage(eventDraft);
  const eventSha256 = sha256BoundedJsonTextV4(JSON.stringify(preimage));
  return trusted({ ...preimage, event_sha256: eventSha256 });
}

function rebuildState(state, defects, acceptedEvents) {
  const sortedDefects = [...defects].sort((a, b) => compareUtf16(a.defect_id, b.defect_id));
  const sortedEvents = [...acceptedEvents].sort((a, b) => compareUtf16(a.event_id, b.event_id));
  const statePrime = trusted({
    schema_version: state.schema_version,
    quest_id: state.quest_id,
    gate_id: state.gate_id,
    correlation_id: state.correlation_id,
    quest_hold: derivedQuestHold(sortedDefects),
    blocked_branches: derivedBlockedBranches(sortedDefects),
    defects: sortedDefects,
    accepted_events: sortedEvents,
  });
  if (!validateDefectProjectionStateV4(statePrime)) throw new Error("PROJECTED_DEFECT_STATE_INVALID");
  return statePrime;
}

function acceptEvent(state, event, defects) {
  if (state.accepted_events.length >= MAX_ACCEPTED_EVENTS) throw new Error("ACCEPTED_EVENT_CAPACITY_EXCEEDED");
  return rebuildState(state, defects, [
    ...state.accepted_events,
    { event_id: event.event_id, event_sha256: event.event_sha256 },
  ]);
}

function currentActionForState(statePrime, preferredAction) {
  if (statePrime.quest_hold) return action("QUEST_HOLD");
  return preferredAction;
}

export function projectDefectEventV4(state, event) {
  if (!validateDefectProjectionStateV4(state)) return deny("DEFECT_PROJECTION_STATE_INVALID");
  try {
    if (!validBoundEvent(event)) return deny("DEFECT_PROJECTION_EVENT_INVALID", state);
    if (event.quest_id !== state.quest_id || event.gate_id !== state.gate_id
      || event.correlation_id !== state.correlation_id) {
      return deny("DEFECT_PROJECTION_SCOPE_BINDING_INVALID", state);
    }
    const expectedEventSha256 = sha256BoundedJsonTextV4(JSON.stringify(eventPreimage(event)));
    if (event.event_sha256 !== expectedEventSha256) return deny("DEFECT_PROJECTION_EVENT_HASH_MISMATCH", state);
    const priorEvent = state.accepted_events.find((entry) => entry.event_id === event.event_id);
    if (priorEvent) {
      if (priorEvent.event_sha256 !== event.event_sha256) return deny("DEFECT_EVENT_ID_CONTENT_CONFLICT", state);
      return noOp("EXACT_EVENT_REPLAY_IDEMPOTENT", state);
    }

    const defects = state.defects.map((entry) => ({ ...entry,
      closure: entry.closure === null ? null : { ...entry.closure } }));
    const defectIndex = defects.findIndex((entry) => entry.defect_id === event.payload.defect_id);
    let preferredAction = action("NO_OP");
    let reason = "DEFECT_EVENT_ACCEPTED";

    if (event.kind === "LOCAL_MODULE_DEFECT" || event.kind === "GLOBAL_SIGNATURE_DEFECT") {
      const scope = event.kind === "LOCAL_MODULE_DEFECT" ? "LOCAL" : "GLOBAL";
      const affectedBranchId = scope === "LOCAL" ? event.payload.affected_branch_id : null;
      if (defectIndex >= 0) {
        const existing = defects[defectIndex];
        if (existing.scope !== scope || existing.affected_branch_id !== affectedBranchId
          || existing.defect_fingerprint_sha256 !== event.payload.defect_fingerprint_sha256
          || existing.reopen_fingerprint_sha256 !== event.payload.reopen_fingerprint_sha256) {
          return deny("DEFECT_ID_BINDING_CONFLICT", state);
        }
        preferredAction = existing.status === "RESOLVED" ? action("NO_OP")
          : scope === "LOCAL" ? action("BLOCK_BRANCH", affectedBranchId) : action("QUEST_HOLD");
        reason = "MATCHING_DEFECT_DECLARATION_ACCEPTED";
      } else {
        if (defects.length >= MAX_DEFECTS) return deny("DEFECT_CAPACITY_EXCEEDED", state);
        defects.push({
          defect_id: event.payload.defect_id,
          scope,
          affected_branch_id: affectedBranchId,
          status: "BLOCKED",
          defect_fingerprint_sha256: event.payload.defect_fingerprint_sha256,
          reopen_fingerprint_sha256: event.payload.reopen_fingerprint_sha256,
          declaration_event_id: event.event_id,
          last_transition_event_id: event.event_id,
          recurrence_count: 0,
          closure: null,
        });
        preferredAction = scope === "LOCAL" ? action("BLOCK_BRANCH", affectedBranchId) : action("QUEST_HOLD");
        reason = scope === "LOCAL" ? "LOCAL_DEFECT_BRANCH_ISOLATED" : "GLOBAL_DEFECT_QUEST_HOLD_REQUIRED";
      }
    } else {
      if (defectIndex < 0) return deny("DEFECT_REFERENCE_NOT_FOUND", state);
      const existing = defects[defectIndex];
      if (event.kind === "DEFECT_CLOSURE_REVALIDATED") {
        if (existing.status === "RESOLVED") return deny("DEFECT_ALREADY_RESOLVED", state);
        const closure = {
          closure_event_id: event.event_id,
          root_cause: event.payload.root_cause,
          regression_guard: event.payload.regression_guard,
          correction: event.payload.correction,
          complete_reaudit: event.payload.complete_reaudit,
          independent_acceptance: event.payload.independent_acceptance,
        };
        defects[defectIndex] = {
          ...existing,
          status: "RESOLVED",
          closure,
          last_transition_event_id: event.event_id,
        };
        const anotherOpenLocal = existing.scope === "LOCAL" && defects.some((entry, index) =>
          index !== defectIndex && entry.scope === "LOCAL"
            && entry.affected_branch_id === existing.affected_branch_id && entry.status !== "RESOLVED");
        preferredAction = existing.scope === "LOCAL" && !anotherOpenLocal
          ? action("UNQUARANTINE_BRANCH", existing.affected_branch_id) : action("NO_OP");
        reason = "DEFECT_CLOSED_WITH_BOUND_REPAIR_REAUDIT_AND_INDEPENDENT_ACCEPTANCE";
      } else {
        if (existing.status !== "RESOLVED") return deny("RECURRENCE_REQUIRES_RESOLVED_DEFECT", state);
        if (event.payload.recurrence_fingerprint_sha256 !== existing.reopen_fingerprint_sha256) {
          return deny("RECURRENCE_FINGERPRINT_MISMATCH", state);
        }
        defects[defectIndex] = {
          ...existing,
          status: "OPEN",
          closure: null,
          last_transition_event_id: event.event_id,
          recurrence_count: existing.recurrence_count + 1,
        };
        preferredAction = existing.scope === "LOCAL"
          ? action("BLOCK_BRANCH", existing.affected_branch_id) : action("QUEST_HOLD");
        reason = "BOUND_FINGERPRINT_RECURRENCE_REOPENED_ATOMICALLY";
      }
    }

    const statePrime = acceptEvent(state, event, defects);
    return decision("PASS", reason, statePrime, currentActionForState(statePrime, preferredAction));
  } catch (error) {
    return deny(`DEFECT_PROJECTION_INTERNAL_REJECTION:${error?.message ?? "UNKNOWN"}`, state);
  }
}

function actionKey(value) {
  return `${value.kind}:${value.branch_id ?? ""}`;
}

function terminalAdapterActions(preState, finalState) {
  if (finalState.quest_hold) {
    return preState.quest_hold ? [action("NO_OP")] : [action("QUEST_HOLD")];
  }
  if (preState.quest_hold) {
    // RequiredAdapterAction has no release-quest-hold member.  A separately
    // admitted runtime adapter must reconcile this transition out of band;
    // emitting a branch action here would falsely imply that the global hold
    // had already been lifted.
    return [action("NO_OP")];
  }

  const before = new Set(preState.blocked_branches);
  const after = new Set(finalState.blocked_branches);
  const projected = [];
  for (const branchId of after) {
    if (!before.has(branchId)) projected.push(action("BLOCK_BRANCH", branchId));
  }
  for (const branchId of before) {
    if (!after.has(branchId)) projected.push(action("UNQUARANTINE_BRANCH", branchId));
  }
  projected.sort((left, right) => compareUtf16(actionKey(left), actionKey(right)));
  return projected.length === 0 ? [action("NO_OP")] : projected;
}

export function projectDefectEventBatchV4(state, events) {
  if (!validateDefectProjectionStateV4(state)) return Object.freeze({
    schema_version: "limex-defect-projection-batch-decision-v4.0.0",
    decision: "DENY",
    reason: "DEFECT_PROJECTION_STATE_INVALID",
    state_prime: null,
    required_adapter_actions: Object.freeze([action("NO_OP")]),
    effectful_action_allowed: false,
    diagnostic_authority: "NONE",
    authorized_transition: null,
  });
  if (!validateCanonicalDomainV3(events) || !Array.isArray(events)
    || events.length < 1 || events.length > 256) return Object.freeze({
    schema_version: "limex-defect-projection-batch-decision-v4.0.0",
    decision: "DENY",
    reason: "DEFECT_PROJECTION_EVENT_BATCH_INVALID",
    state_prime: state,
    required_adapter_actions: Object.freeze([action("NO_OP")]),
    effectful_action_allowed: false,
    diagnostic_authority: "NONE",
    authorized_transition: null,
  });
  let staged = state;
  for (const event of events) {
    const result = projectDefectEventV4(staged, event);
    if (result.decision !== "PASS") return Object.freeze({
      schema_version: "limex-defect-projection-batch-decision-v4.0.0",
      decision: "DENY",
      reason: result.reason,
      state_prime: state,
      required_adapter_actions: Object.freeze([action("NO_OP")]),
      effectful_action_allowed: false,
      diagnostic_authority: "NONE",
      authorized_transition: null,
    });
    staged = result.state_prime;
  }
  const requiredActions = terminalAdapterActions(state, staged);
  return Object.freeze({
    schema_version: "limex-defect-projection-batch-decision-v4.0.0",
    decision: "PASS",
    reason: requiredActions[0].kind === "QUEST_HOLD"
      ? "GLOBAL_DEFECT_ACTION_DOMINATES_TERMINAL_BATCH"
      : state.quest_hold && !staged.quest_hold
        ? "QUEST_HOLD_RELEASE_REQUIRES_SEPARATELY_ADMITTED_RUNTIME_ADAPTER"
        : "DEFECT_EVENT_BATCH_TERMINAL_ACTIONS_PROJECTED",
    state_prime: staged,
    required_adapter_actions: Object.freeze(requiredActions),
    effectful_action_allowed: false,
    diagnostic_authority: "NONE",
    authorized_transition: null,
  });
}

export const defectProjectionEventKindsV4 = Object.freeze([...EVENT_KINDS].sort(compareUtf16));
export const defectProjectionRequiredAdapterActionsV4 = Object.freeze([
  "NO_OP", "BLOCK_BRANCH", "UNQUARANTINE_BRANCH", "QUEST_HOLD",
]);
