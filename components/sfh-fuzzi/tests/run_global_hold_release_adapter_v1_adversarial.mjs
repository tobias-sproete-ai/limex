import assert from "node:assert/strict";
import {
  mkdtempSync,
  mkdirSync,
  readdirSync,
  readFileSync,
  rmSync,
  symlinkSync,
  writeFileSync,
} from "node:fs";
import { tmpdir } from "node:os";
import { join, resolve } from "node:path";
import { fileURLToPath } from "node:url";
import { generateKeyPairSync, sign } from "node:crypto";
import { spawnSync } from "node:child_process";
import process from "node:process";
import {
  applyGlobalReopen,
  commitRelease,
  initializeAdapter,
  readPostcondition,
  recoverAdapter,
  revokeAuthority,
  sha256,
  stableJson,
  submitReleaseRequest,
} from "../scripts/global_hold_release_adapter_v1.mjs";
import {
  bindDefectProjectionEventV4,
  createDefectProjectionStateV4,
  projectDefectEventV4,
} from "../scripts/defect_event_projector_v4.mjs";
import { parseBoundedJsonCarrierV4 } from "../scripts/canonical_state_v2.mjs";

const scriptPath = resolve(fileURLToPath(new URL("../scripts/global_hold_release_adapter_v1.mjs", import.meta.url)));
const projectorPath = resolve(fileURLToPath(new URL("../scripts/defect_event_projector_v4.mjs", import.meta.url)));
const canonicalStatePath = resolve(fileURLToPath(new URL("../scripts/canonical_state_v2.mjs", import.meta.url)));
const strictJsonPath = resolve(fileURLToPath(new URL("../scripts/strict_json.mjs", import.meta.url)));
const testPath = resolve(fileURLToPath(import.meta.url));
const results = [];
let assertions = 0;
const NOW = Date.now();

function check(actual, expected, message) {
  assertions += 1;
  assert.deepEqual(actual, expected, message);
}

async function test(id, execute) {
  const started = process.hrtime.bigint();
  try {
    const evidence = await execute();
    results.push({
      id,
      status: "PASS",
      duration_us: Number((process.hrtime.bigint() - started) / 1000n),
      evidence,
    });
  } catch (error) {
    results.push({
      id,
      status: "FAIL",
      duration_us: Number((process.hrtime.bigint() - started) / 1000n),
      error: error?.stack ?? String(error),
    });
  }
}

function expectReason(execute, reason) {
  assertions += 1;
  assert.throws(execute, (error) => error?.message === reason);
}

const carrier = (value) => parseBoundedJsonCarrierV4(JSON.stringify(value));
const digest = (text) => sha256(Buffer.from(text, "utf8"));

function artifact(text) {
  const bytes = Buffer.from(text, "utf8");
  return { sha256: sha256(bytes), utf8_bytes: bytes.length, utf8_base64: bytes.toString("base64") };
}

function createCoreTransition(scope) {
  const initial = createDefectProjectionStateV4(scope.quest_id, scope.gate_id, scope.correlation_id);
  const globalDraft = carrier({
    schema_version: "limex-defect-projection-event-v4.0.0",
    ...scope,
    event_id: "global-defect-open",
    kind: "GLOBAL_SIGNATURE_DEFECT",
    payload: {
      defect_id: "global-defect",
      defect_fingerprint_sha256: digest("global-defect"),
      reopen_fingerprint_sha256: digest("global-reopen"),
    },
  });
  const before = projectDefectEventV4(initial, bindDefectProjectionEventV4(globalDraft)).state_prime;
  const closureDraft = carrier({
    schema_version: "limex-defect-projection-event-v4.0.0",
    ...scope,
    event_id: "global-defect-close",
    kind: "DEFECT_CLOSURE_REVALIDATED",
    payload: {
      defect_id: "global-defect",
      root_cause: artifact("root-cause"),
      regression_guard: artifact("regression-guard"),
      correction: artifact("correction"),
      complete_reaudit: artifact("complete-reaudit"),
      independent_acceptance: {
        acceptance_decision: "PASS",
        artifact: artifact("independent-acceptance"),
        attestation_kind: "INDEPENDENT_READ_ONLY_REAUDIT_ACCEPTANCE",
        auditor_identity: "synthetic-auditor",
        builder_identity: "synthetic-builder",
        independence_marker: "AUDITOR_DISTINCT_FROM_BUILDER__READ_ONLY",
        subject_quest_id: scope.quest_id,
        subject_gate_id: scope.gate_id,
        subject_correlation_id: scope.correlation_id,
        subject_defect_id: "global-defect",
      },
    },
  });
  const after = projectDefectEventV4(before, bindDefectProjectionEventV4(closureDraft)).state_prime;
  check(before.quest_hold, true);
  check(after.quest_hold, false);
  return { before, after };
}

function newHarness(label = "case") {
  const root = mkdtempSync(join(tmpdir(), `limex-hold-${label}-`));
  const scope = {
    quest_id: `quest-${label}`,
    gate_id: `gate-${label}`,
    correlation_id: `corr-${label}`,
  };
  const { publicKey, privateKey } = generateKeyPairSync("ed25519");
  const publicPem = publicKey.export({ type: "spki", format: "pem" });
  const fingerprint = sha256(publicKey.export({ type: "spki", format: "der" }));
  const keyId = `SYNTHETIC-EPHEMERAL-ED25519-${fingerprint.slice(0, 16).toUpperCase()}`;
  const capability = Buffer.from(`capability-${label}-0123456789abcdef`, "utf8");
  const transition = createCoreTransition(scope);
  initializeAdapter(root, {
    ...scope,
    evidence_class: "SYNTHETIC_TEST_FIXTURE",
    initialized_at_ms: NOW - 1000,
    test_mode: true,
    trust_anchor: {
      key_id: keyId,
      public_key_pem: publicPem,
      public_key_spki_sha256: fingerprint,
    },
  });

  function signedRequest(overrides = {}) {
    const preimage = {
      schema_version: "limex-global-hold-release-request-v1.0.0",
      event_type: "RELEASE_REQUEST",
      ...scope,
      request_id: "release-001",
      expected_epoch: 1,
      issued_at_ms: NOW - 1000,
      expires_at_ms: NOW + 60_000,
      capability_sha256: sha256(capability),
      authority_key_id: keyId,
      core_state_before: transition.before,
      core_state_after: transition.after,
      ...overrides,
    };
    return {
      ...preimage,
      authority_signature_base64: sign(null, Buffer.from(stableJson(preimage), "utf8"), privateKey).toString("base64"),
    };
  }

  function reopenEvent(overrides = {}) {
    const preimage = {
      schema_version: "limex-global-hold-reopen-event-v1.0.0",
      event_type: "GLOBAL_REOPEN",
      ...scope,
      event_id: "reopen-001",
      expected_epoch: 1,
      occurred_at_ms: NOW,
      reopen_fingerprint_sha256: digest("global-reopen"),
      ...overrides,
    };
    return { ...preimage, event_sha256: sha256(Buffer.from(stableJson(preimage), "utf8")) };
  }

  return { root, scope, keyId, fingerprint, capability, signedRequest, reopenEvent };
}

function persistJson(path, value) {
  writeFileSync(path, `${JSON.stringify(value, null, 2)}\n`, { encoding: "utf8", mode: 0o600 });
}

function rewriteEnvelope(path, mutate) {
  const value = JSON.parse(readFileSync(path, "utf8"));
  mutate(value.payload);
  value.payload_sha256 = sha256(Buffer.from(stableJson(value.payload), "utf8"));
  persistJson(path, value);
  return value;
}

function crashCommit(harness, request, fault) {
  const requestPath = join(harness.root, `request-${fault}.json`);
  const capabilityPath = join(harness.root, `capability-${fault}.txt`);
  persistJson(requestPath, request);
  writeFileSync(capabilityPath, harness.capability, { mode: 0o600 });
  return spawnSync(process.execPath, [
    scriptPath, "commit", harness.root, requestPath, capabilityPath, String(NOW), fault,
  ], {
    encoding: "utf8",
  });
}

await test("HRA-001.initial-state-denies-protected-action", () => {
  const h = newHarness("initial");
  const probe = readPostcondition(h.root);
  check(probe.action_allowed, false);
  check(probe.fail_closed, true);
  check(probe.state_phase, "HELD");
  return probe;
});

await test("HRA-002.bound-release-needs-and-records-postcondition-ack", () => {
  const h = newHarness("normal");
  const request = h.signedRequest();
  check(submitReleaseRequest(h.root, request, NOW).decision, "RELEASE_REQUEST_PENDING");
  const released = commitRelease(h.root, request, h.capability, NOW);
  check(released.decision, "RELEASED_AFTER_BOUND_POSTCONDITION_ACK");
  check(released.ack.readback_kind, "REFERENCE_TARGET_FILE_REOPEN_POSTCONDITION");
  const probe = readPostcondition(h.root);
  check(probe.reference_postcondition_satisfied, true);
  check(probe.action_allowed, false);
  check(probe.fail_closed, true);
  check(probe.reason, "PRODUCT_RUNTIME_BINDING_REQUIRED");
  return released.ack;
});

await test("HRA-003.exact-request-replay-is-idempotent", () => {
  const h = newHarness("request-replay");
  const request = h.signedRequest();
  const first = submitReleaseRequest(h.root, request, NOW);
  const replay = submitReleaseRequest(h.root, request, NOW);
  check(replay.decision, "IDEMPOTENT_NO_OP");
  check(replay.request_sha256, first.request_sha256);
  return replay;
});

await test("HRA-004.same-request-id-with-different-content-is-denied", () => {
  const h = newHarness("request-conflict");
  const first = h.signedRequest();
  submitReleaseRequest(h.root, first, NOW);
  const conflict = h.signedRequest({ capability_sha256: digest("different-capability") });
  expectReason(() => submitReleaseRequest(h.root, conflict, NOW), "RELEASE_REQUEST_ID_CONTENT_CONFLICT");
  check(readPostcondition(h.root).action_allowed, false);
  return { conflicting_replay_denied: true };
});

await test("HRA-005.commit-replay-after-ack-is-idempotent", () => {
  const h = newHarness("commit-replay");
  const request = h.signedRequest();
  submitReleaseRequest(h.root, request, NOW);
  commitRelease(h.root, request, h.capability, NOW);
  const replay = commitRelease(h.root, request, h.capability, NOW);
  check(replay.decision, "IDEMPOTENT_ALREADY_RELEASED");
  const probe = readPostcondition(h.root);
  check(probe.reference_postcondition_satisfied, true);
  check(probe.action_allowed, false);
  return replay;
});

await test("HRA-006.stale-epoch-request-is-denied", () => {
  const h = newHarness("stale-epoch");
  const request = h.signedRequest({ expected_epoch: 2 });
  expectReason(() => submitReleaseRequest(h.root, request, NOW), "RELEASE_REQUEST_EPOCH_STALE");
  check(readPostcondition(h.root).action_allowed, false);
  return { stale_epoch_denied: true };
});

await test("HRA-007.expired-authority-window-is-denied", () => {
  const h = newHarness("expired");
  const request = h.signedRequest({ issued_at_ms: NOW - 120_000, expires_at_ms: NOW - 1 });
  expectReason(() => submitReleaseRequest(h.root, request, NOW), "RELEASE_REQUEST_INVALID");
  check(readPostcondition(h.root).action_allowed, false);
  return { expired_request_denied: true };
});

await test("HRA-008.invalid-authority-signature-is-denied", () => {
  const h = newHarness("bad-signature");
  const request = h.signedRequest();
  request.authority_signature_base64 = Buffer.alloc(64, 7).toString("base64");
  expectReason(() => submitReleaseRequest(h.root, request, NOW), "RELEASE_AUTHORITY_SIGNATURE_INVALID");
  check(readPostcondition(h.root).action_allowed, false);
  return { invalid_signature_denied: true };
});

await test("HRA-008B.wrong-capability-preimage-is-denied", () => {
  const h = newHarness("bad-capability");
  const request = h.signedRequest();
  submitReleaseRequest(h.root, request, NOW);
  expectReason(
    () => commitRelease(h.root, request, Buffer.from("wrong-capability-0123456789", "utf8"), NOW),
    "RELEASE_CAPABILITY_PREIMAGE_MISMATCH",
  );
  check(readPostcondition(h.root).action_allowed, false);
  return { wrong_capability_denied: true };
});

await test("HRA-009.crash-after-intent-recovers-held-on-restart", () => {
  const h = newHarness("crash-intent");
  const request = h.signedRequest();
  submitReleaseRequest(h.root, request, NOW);
  const child = crashCommit(h, request, "CRASH_AFTER_INTENT_PERSIST");
  check(child.status, 97);
  check(readPostcondition(h.root).action_allowed, false);
  const recovered = recoverAdapter(h.root);
  check(recovered.decision, "RECOVERED_TO_HELD");
  check(readPostcondition(h.root).state_phase, "HELD");
  return recovered;
});

await test("HRA-009B.consumed-capability-cannot-authorize-a-new-request", () => {
  const h = newHarness("consumed-capability");
  const request = h.signedRequest();
  submitReleaseRequest(h.root, request, NOW);
  const child = crashCommit(h, request, "CRASH_AFTER_INTENT_PERSIST");
  check(child.status, 97);
  recoverAdapter(h.root);
  const replayWithNewIdentity = h.signedRequest({ request_id: "release-002", expected_epoch: 2 });
  expectReason(
    () => submitReleaseRequest(h.root, replayWithNewIdentity, NOW),
    "RELEASE_CAPABILITY_ALREADY_CONSUMED",
  );
  check(readPostcondition(h.root).action_allowed, false);
  return { consumed_capability_reuse_denied: true };
});

await test("HRA-010.crash-after-target-release-never-enables-action-without-ack", () => {
  const h = newHarness("crash-target");
  const request = h.signedRequest();
  submitReleaseRequest(h.root, request, NOW);
  const child = crashCommit(h, request, "CRASH_AFTER_TARGET_RELEASE_BEFORE_ACK");
  check(child.status, 97);
  const beforeRecovery = readPostcondition(h.root);
  check(beforeRecovery.action_allowed, false);
  check(beforeRecovery.state_phase, "RELEASE_APPLYING");
  recoverAdapter(h.root);
  check(readPostcondition(h.root).state_phase, "HELD");
  return { pre_ack_action_allowed: false, recovery: "HELD" };
});

await test("HRA-011.crash-after-durable-ack-retains-bound-release", () => {
  const h = newHarness("crash-acked");
  const request = h.signedRequest();
  submitReleaseRequest(h.root, request, NOW);
  const child = crashCommit(h, request, "CRASH_AFTER_ACK_PERSIST");
  check(child.status, 97);
  const recovered = recoverAdapter(h.root);
  check(recovered.decision, "ACKED_RELEASE_RETAINED");
  const probe = readPostcondition(h.root);
  check(probe.reference_postcondition_satisfied, true);
  check(probe.action_allowed, false);
  return recovered;
});

await test("HRA-012.concurrent-global-reopen-dominates-pending-release", () => {
  const h = newHarness("reopen-dominates");
  const request = h.signedRequest();
  submitReleaseRequest(h.root, request, NOW);
  const reopened = applyGlobalReopen(h.root, h.reopenEvent());
  check(reopened.decision, "GLOBAL_REOPEN_DOMINATES_RELEASE");
  expectReason(() => commitRelease(h.root, request, h.capability, NOW), "BOUND_PENDING_RELEASE_REQUEST_REQUIRED");
  check(readPostcondition(h.root).action_allowed, false);
  return reopened;
});

await test("HRA-013.crash-during-reopen-remains-fail-closed-and-recovers", () => {
  const h = newHarness("crash-reopen");
  const request = h.signedRequest();
  submitReleaseRequest(h.root, request, NOW);
  commitRelease(h.root, request, h.capability, NOW);
  const reopen = h.reopenEvent();
  const path = join(h.root, "reopen.json");
  persistJson(path, reopen);
  const child = spawnSync(process.execPath, [
    scriptPath, "reopen", h.root, path, "CRASH_AFTER_TARGET_REHOLD_BEFORE_STATE",
  ], { encoding: "utf8" });
  check(child.status, 97);
  check(readPostcondition(h.root).action_allowed, false);
  const recovered = recoverAdapter(h.root);
  check(recovered.decision, "RECOVERED_TO_HELD");
  return recovered;
});

await test("HRA-014.authority-revocation-dominates-pending-release", () => {
  const h = newHarness("revoked");
  const request = h.signedRequest();
  submitReleaseRequest(h.root, request, NOW);
  const revoked = revokeAuthority(h.root, h.fingerprint);
  check(revoked.decision, "AUTHORITY_REVOKED_AND_HELD");
  expectReason(() => commitRelease(h.root, request, h.capability, NOW), "BOUND_PENDING_RELEASE_REQUEST_REQUIRED");
  check(readPostcondition(h.root).action_allowed, false);
  return revoked;
});

await test("HRA-015.commit-timeout-after-pending-request-is-denied", () => {
  const h = newHarness("timeout");
  const request = h.signedRequest({ expires_at_ms: Date.now() + 40 });
  submitReleaseRequest(h.root, request, Date.now());
  Atomics.wait(new Int32Array(new SharedArrayBuffer(4)), 0, 0, 60);
  expectReason(
    () => commitRelease(h.root, request, h.capability, Date.now()),
    "RELEASE_REQUEST_INVALID",
  );
  check(readPostcondition(h.root).action_allowed, false);
  recoverAdapter(h.root);
  check(readPostcondition(h.root).state_phase, "HELD");
  return { timeout_denied_and_recovered: true };
});

await test("HRA-016.corrupt-state-is-quarantined-and-recovered-held", () => {
  const h = newHarness("corrupt-state");
  writeFileSync(join(h.root, "adapter_state.json"), "{corrupt", "utf8");
  check(readPostcondition(h.root).action_allowed, false);
  const recovered = recoverAdapter(h.root);
  check(recovered.decision, "CORRUPT_STATE_QUARANTINED_AND_AUTHORITY_REVOKED_HELD");
  check(typeof recovered.corruption_sha256, "string");
  check(readPostcondition(h.root).state_phase, "HELD");
  return recovered;
});

await test("HRA-017.post-ack-target-tamper-revokes-effective-release", () => {
  const h = newHarness("target-tamper");
  const request = h.signedRequest();
  submitReleaseRequest(h.root, request, NOW);
  commitRelease(h.root, request, h.capability, NOW);
  const targetPath = join(h.root, "reference_target_hold.json");
  rewriteEnvelope(targetPath, (payload) => { payload.mutation_seq += 1; });
  check(readPostcondition(h.root).action_allowed, false);
  const recovered = recoverAdapter(h.root);
  check(recovered.decision, "RECOVERED_TO_HELD");
  return recovered;
});

await test("HRA-018.live-lock-owner-prevents-concurrent-transition", () => {
  const h = newHarness("lock-contention");
  const lock = join(h.root, ".adapter-lock");
  mkdirSync(lock, { mode: 0o700 });
  persistJson(join(lock, "owner.json"), { pid: process.pid, owner_token: digest("live-lock") });
  const request = h.signedRequest();
  expectReason(() => submitReleaseRequest(h.root, request, NOW), "ADAPTER_LOCK_HELD");
  rmSync(lock, { recursive: true, force: true });
  check(readPostcondition(h.root).action_allowed, false);
  return { concurrent_transition_denied: true };
});

await test("HRA-019.symlink-root-is-rejected", () => {
  const target = mkdtempSync(join(tmpdir(), "limex-hold-real-"));
  const link = `${target}-link`;
  symlinkSync(target, link, "dir");
  const probe = readPostcondition(link);
  check(probe.action_allowed, false);
  check(probe.reason, "ADAPTER_ROOT_SYMLINK_REJECTED");
  rmSync(link, { force: true });
  return probe;
});

await test("HRA-020.real-cli-request-commit-and-probe-path", () => {
  const h = newHarness("cli-e2e");
  const request = h.signedRequest();
  const requestPath = join(h.root, "request-cli.json");
  const capabilityPath = join(h.root, "capability-cli.txt");
  persistJson(requestPath, request);
  writeFileSync(capabilityPath, h.capability, { mode: 0o600 });
  const requested = spawnSync(process.execPath, [
    scriptPath, "request", h.root, requestPath, String(NOW),
  ], { encoding: "utf8" });
  check(requested.status, 0);
  check(JSON.parse(requested.stdout).decision, "RELEASE_REQUEST_PENDING");
  const committed = spawnSync(process.execPath, [
    scriptPath, "commit", h.root, requestPath, capabilityPath, String(NOW), "NONE",
  ], { encoding: "utf8" });
  check(committed.status, 0);
  check(JSON.parse(committed.stdout).decision, "RELEASED_AFTER_BOUND_POSTCONDITION_ACK");
  const probed = spawnSync(process.execPath, [scriptPath, "probe", h.root], { encoding: "utf8" });
  check(probed.status, 2);
  const probe = JSON.parse(probed.stdout);
  check(probe.reference_postcondition_satisfied, true);
  check(probe.action_allowed, false);
  check(probe.fail_closed, true);
  const inspected = spawnSync(process.execPath, [scriptPath, "inspect-reference", h.root], { encoding: "utf8" });
  check(inspected.status, 0);
  check(JSON.parse(inspected.stdout).reference_postcondition_satisfied, true);
  return { cli_reference_release_observed: true, product_authorization: "DENIED", probe };
});

await test("HRA-021.coherent-root-rewrite-never-grants-product-authority", () => {
  const h = newHarness("coherent-root-rewrite");
  const targetPath = join(h.root, "reference_target_hold.json");
  const statePath = join(h.root, "adapter_state.json");
  const forgedRequestId = "forged-release";
  const forgedRequestSha = digest("forged-release-request");
  const targetEnvelope = rewriteEnvelope(targetPath, (payload) => {
    payload.effective_hold = false;
    payload.release_request_id = forgedRequestId;
    payload.mutation_seq += 1;
  });
  rewriteEnvelope(statePath, (payload) => {
    payload.phase = "RELEASED_ACKED";
    payload.desired_hold = false;
    payload.effective_hold = false;
    payload.pending_request = null;
    payload.last_request_id = forgedRequestId;
    payload.last_request_sha256 = forgedRequestSha;
    payload.last_ack = {
      schema_version: "limex-global-hold-release-postcondition-ack-v1.0.0",
      readback_kind: "REFERENCE_TARGET_FILE_REOPEN_POSTCONDITION",
      request_id: forgedRequestId,
      request_sha256: forgedRequestSha,
      epoch: payload.epoch,
      observed_effective_hold: false,
      target_state_sha256: targetEnvelope.payload_sha256,
    };
    payload.transition_seq += 2;
  });
  const probe = readPostcondition(h.root);
  check(probe.reference_postcondition_satisfied, true);
  check(probe.action_allowed, false);
  check(probe.fail_closed, true);
  check(probe.reason, "PRODUCT_RUNTIME_BINDING_REQUIRED");
  return { coherent_reference_rewrite_observed: true, product_authority_granted: false };
});

await test("HRA-022.commit-replay-revalidates-current-target-postcondition", () => {
  const h = newHarness("replay-rehold");
  const request = h.signedRequest();
  submitReleaseRequest(h.root, request, NOW);
  commitRelease(h.root, request, h.capability, NOW);
  rewriteEnvelope(join(h.root, "reference_target_hold.json"), (payload) => {
    payload.effective_hold = true;
    payload.release_request_id = null;
    payload.mutation_seq += 1;
  });
  expectReason(
    () => commitRelease(h.root, request, h.capability, NOW),
    "RELEASE_POSTCONDITION_READBACK_MISMATCH",
  );
  check(readPostcondition(h.root).reference_postcondition_satisfied, false);
  return { false_idempotent_pass_denied: true };
});

await test("HRA-023.authorization-probe-fails-nonzero-when-root-is-missing", () => {
  const missingRoot = join(tmpdir(), `limex-hold-missing-${process.pid}-${Date.now()}`);
  const probed = spawnSync(process.execPath, [scriptPath, "probe", missingRoot], { encoding: "utf8" });
  check(probed.status, 2);
  const probe = JSON.parse(probed.stdout);
  check(probe.status, "FAIL_CLOSED");
  check(probe.reference_postcondition_satisfied, false);
  check(probe.action_allowed, false);
  check(probe.reason, "ADAPTER_POSTCONDITION_UNREADABLE_OR_INVALID");
  return { missing_root_probe_exit_code: probed.status, reason_code: probe.reason };
});

await test("HRA-024.consumed-request-replay-after-global-reopen-is-denied", () => {
  const h = newHarness("consumed-request-after-reopen");
  const request = h.signedRequest();
  submitReleaseRequest(h.root, request, NOW);
  commitRelease(h.root, request, h.capability, NOW);
  applyGlobalReopen(h.root, h.reopenEvent());
  expectReason(
    () => submitReleaseRequest(h.root, request, NOW),
    "RELEASE_REQUEST_EPOCH_STALE",
  );
  const requestPath = join(h.root, "request-replay-after-reopen.json");
  persistJson(requestPath, request);
  const replay = spawnSync(process.execPath, [
    scriptPath, "request", h.root, requestPath, String(NOW),
  ], { encoding: "utf8" });
  check(replay.status, 2);
  check(JSON.parse(replay.stdout).status, "DENY");
  check(JSON.parse(replay.stdout).reason, "RELEASE_REQUEST_EPOCH_STALE");
  check(readPostcondition(h.root).action_allowed, false);
  return { api_replay_denied: true, cli_replay_exit_code: replay.status };
});

await test("HRA-025.invalid-now-carrier-cannot-bypass-authority-expiry", () => {
  const expired = newHarness("invalid-now-expired-request");
  const expiredRequest = expired.signedRequest({
    issued_at_ms: NOW - 120_000,
    expires_at_ms: NOW - 1,
  });
  expectReason(
    () => submitReleaseRequest(expired.root, expiredRequest, Number.NaN),
    "RELEASE_REQUEST_INVALID",
  );
  const expiredPath = join(expired.root, "expired-request-invalid-now.json");
  persistJson(expiredPath, expiredRequest);
  const cliRequest = spawnSync(process.execPath, [
    scriptPath, "request", expired.root, expiredPath, "not-a-number",
  ], { encoding: "utf8" });
  check(cliRequest.status, 2);
  check(JSON.parse(cliRequest.stdout).reason, "RELEASE_REQUEST_INVALID");

  const pending = newHarness("invalid-now-pending-commit");
  const pendingRequest = pending.signedRequest();
  submitReleaseRequest(pending.root, pendingRequest, NOW);
  expectReason(
    () => commitRelease(pending.root, pendingRequest, pending.capability, Number.NaN),
    "RELEASE_REQUEST_INVALID",
  );
  const pendingPath = join(pending.root, "pending-request-invalid-now.json");
  const capabilityPath = join(pending.root, "pending-capability-invalid-now.txt");
  persistJson(pendingPath, pendingRequest);
  writeFileSync(capabilityPath, pending.capability, { mode: 0o600 });
  const cliCommit = spawnSync(process.execPath, [
    scriptPath, "commit", pending.root, pendingPath, capabilityPath, "not-a-number", "NONE",
  ], { encoding: "utf8" });
  check(cliCommit.status, 2);
  check(JSON.parse(cliCommit.stdout).reason, "RELEASE_REQUEST_INVALID");
  check(readPostcondition(pending.root).action_allowed, false);
  return { invalid_api_now_denied: true, invalid_cli_now_denied: true };
});

await test("HRA-026.backdated-safe-integer-time-cannot-bypass-authority-expiry", () => {
  const expired = newHarness("backdated-now-expired-request");
  const expiredRequest = expired.signedRequest({
    issued_at_ms: NOW - 120_000,
    expires_at_ms: NOW - 1,
  });
  expectReason(
    () => submitReleaseRequest(expired.root, expiredRequest, NOW - 120_000),
    "RELEASE_REQUEST_INVALID",
  );
  const expiredPath = join(expired.root, "expired-request-backdated-now.json");
  persistJson(expiredPath, expiredRequest);
  const cliRequest = spawnSync(process.execPath, [
    scriptPath, "request", expired.root, expiredPath, String(NOW - 120_000),
  ], { encoding: "utf8" });
  check(cliRequest.status, 2);
  check(JSON.parse(cliRequest.stdout).reason, "RELEASE_REQUEST_INVALID");

  const pending = newHarness("backdated-now-pending-commit");
  const pendingRequest = pending.signedRequest({ expires_at_ms: Date.now() + 40 });
  submitReleaseRequest(pending.root, pendingRequest, Date.now());
  Atomics.wait(new Int32Array(new SharedArrayBuffer(4)), 0, 0, 60);
  expectReason(
    () => commitRelease(pending.root, pendingRequest, pending.capability, NOW),
    "RELEASE_REQUEST_INVALID",
  );
  const pendingPath = join(pending.root, "pending-request-backdated-now.json");
  const capabilityPath = join(pending.root, "pending-capability-backdated-now.txt");
  persistJson(pendingPath, pendingRequest);
  writeFileSync(capabilityPath, pending.capability, { mode: 0o600 });
  const cliCommit = spawnSync(process.execPath, [
    scriptPath, "commit", pending.root, pendingPath, capabilityPath, String(NOW), "NONE",
  ], { encoding: "utf8" });
  check(cliCommit.status, 2);
  check(JSON.parse(cliCommit.stdout).reason, "RELEASE_REQUEST_INVALID");
  check(readPostcondition(pending.root).action_allowed, false);

  const incoherent = newHarness("far-backdated-now");
  expectReason(
    () => submitReleaseRequest(incoherent.root, incoherent.signedRequest(), NOW - 86_400_000),
    "RELEASE_TIME_REFERENCE_MISMATCH",
  );
  return {
    expired_api_request_denied: true,
    expired_cli_request_denied: true,
    expired_api_commit_denied: true,
    expired_cli_commit_denied: true,
    incoherent_time_reference_denied: true,
  };
});

await test("HRA-027.corrupt-state-recovery-cannot-resurrect-revoked-or-consumed-authority", () => {
  const revoked = newHarness("corrupt-state-after-revocation");
  revokeAuthority(revoked.root, revoked.fingerprint);
  writeFileSync(join(revoked.root, "adapter_state.json"), "{corrupt", "utf8");
  const revokedRecovery = recoverAdapter(revoked.root);
  check(revokedRecovery.decision, "CORRUPT_STATE_QUARANTINED_AND_AUTHORITY_REVOKED_HELD");
  const revokedRequest = revoked.signedRequest({
    request_id: "release-002",
    expected_epoch: revokedRecovery.epoch,
  });
  expectReason(
    () => submitReleaseRequest(revoked.root, revokedRequest, Date.now()),
    "RELEASE_AUTHORITY_REVOKED",
  );
  check(readPostcondition(revoked.root).action_allowed, false);

  const consumed = newHarness("corrupt-state-after-capability-consumption");
  const consumedRequest = consumed.signedRequest();
  submitReleaseRequest(consumed.root, consumedRequest, Date.now());
  commitRelease(consumed.root, consumedRequest, consumed.capability, Date.now());
  writeFileSync(join(consumed.root, "adapter_state.json"), "{corrupt", "utf8");
  const consumedRecovery = recoverAdapter(consumed.root);
  check(consumedRecovery.decision, "CORRUPT_STATE_QUARANTINED_AND_AUTHORITY_REVOKED_HELD");
  const reuseRequest = consumed.signedRequest({
    request_id: "release-002",
    expected_epoch: consumedRecovery.epoch,
  });
  expectReason(
    () => submitReleaseRequest(consumed.root, reuseRequest, Date.now()),
    "RELEASE_AUTHORITY_REVOKED",
  );
  check(readPostcondition(consumed.root).action_allowed, false);
  return { revoked_authority_not_resurrected: true, consumed_capability_path_not_resurrected: true };
});

await test("HRA-028.safe-integer-counter-exhaustion-is-atomic-and-fail-closed", () => {
  const reopened = newHarness("reopen-counter-exhaustion");
  rewriteEnvelope(join(reopened.root, "adapter_state.json"), (payload) => {
    payload.epoch = Number.MAX_SAFE_INTEGER;
  });
  rewriteEnvelope(join(reopened.root, "reference_target_hold.json"), (payload) => {
    payload.epoch = Number.MAX_SAFE_INTEGER;
  });
  const reopenStateBefore = readFileSync(join(reopened.root, "adapter_state.json"));
  const reopenTargetBefore = readFileSync(join(reopened.root, "reference_target_hold.json"));
  expectReason(
    () => applyGlobalReopen(reopened.root, reopened.reopenEvent({
      expected_epoch: Number.MAX_SAFE_INTEGER,
    })),
    "ADAPTER_COUNTER_EXHAUSTED",
  );
  check(readFileSync(join(reopened.root, "adapter_state.json")).equals(reopenStateBefore), true);
  check(readFileSync(join(reopened.root, "reference_target_hold.json")).equals(reopenTargetBefore), true);
  check(readPostcondition(reopened.root).action_allowed, false);

  const committed = newHarness("commit-counter-exhaustion");
  const commitRequest = committed.signedRequest();
  submitReleaseRequest(committed.root, commitRequest, Date.now());
  rewriteEnvelope(join(committed.root, "adapter_state.json"), (payload) => {
    payload.transition_seq = Number.MAX_SAFE_INTEGER - 1;
  });
  const commitStateBefore = readFileSync(join(committed.root, "adapter_state.json"));
  const commitTargetBefore = readFileSync(join(committed.root, "reference_target_hold.json"));
  expectReason(
    () => commitRelease(committed.root, commitRequest, committed.capability, Date.now()),
    "ADAPTER_COUNTER_EXHAUSTED",
  );
  check(readFileSync(join(committed.root, "adapter_state.json")).equals(commitStateBefore), true);
  check(readFileSync(join(committed.root, "reference_target_hold.json")).equals(commitTargetBefore), true);
  check(readPostcondition(committed.root).action_allowed, false);
  return { reopen_overflow_atomic: true, commit_overflow_atomic: true };
});

await test("HRA-029.corrupt-carrier-plus-counter-exhaustion-has-zero-partial-mutation", () => {
  const corruptTarget = newHarness("corrupt-target-exhausted-epoch");
  rewriteEnvelope(join(corruptTarget.root, "adapter_state.json"), (payload) => {
    payload.epoch = Number.MAX_SAFE_INTEGER;
  });
  writeFileSync(join(corruptTarget.root, "reference_target_hold.json"), "{corrupt-target", "utf8");
  const firstNames = readdirSync(corruptTarget.root).sort();
  const firstState = readFileSync(join(corruptTarget.root, "adapter_state.json"));
  const firstTarget = readFileSync(join(corruptTarget.root, "reference_target_hold.json"));
  expectReason(() => recoverAdapter(corruptTarget.root), "ADAPTER_COUNTER_EXHAUSTED");
  check(readdirSync(corruptTarget.root).sort(), firstNames);
  check(readFileSync(join(corruptTarget.root, "adapter_state.json")).equals(firstState), true);
  check(readFileSync(join(corruptTarget.root, "reference_target_hold.json")).equals(firstTarget), true);

  const corruptState = newHarness("corrupt-state-exhausted-target-counter");
  rewriteEnvelope(join(corruptState.root, "reference_target_hold.json"), (payload) => {
    payload.mutation_seq = Number.MAX_SAFE_INTEGER;
  });
  writeFileSync(join(corruptState.root, "adapter_state.json"), "{corrupt-state", "utf8");
  const secondNames = readdirSync(corruptState.root).sort();
  const secondState = readFileSync(join(corruptState.root, "adapter_state.json"));
  const secondTarget = readFileSync(join(corruptState.root, "reference_target_hold.json"));
  expectReason(() => recoverAdapter(corruptState.root), "ADAPTER_COUNTER_EXHAUSTED");
  check(readdirSync(corruptState.root).sort(), secondNames);
  check(readFileSync(join(corruptState.root, "adapter_state.json")).equals(secondState), true);
  check(readFileSync(join(corruptState.root, "reference_target_hold.json")).equals(secondTarget), true);
  return { corrupt_target_preflight_atomic: true, corrupt_state_preflight_atomic: true };
});

const failed = results.filter((entry) => entry.status !== "PASS");
const report = {
  schema_version: "limex-global-hold-release-adapter-adversarial-report-v1.0.0",
  created_at_utc: new Date().toISOString(),
  status: failed.length === 0 ? "PASS" : "FAIL",
  evidence_class: "SYNTHETIC_TEST_FIXTURE_ON_REAL_FILESYSTEM",
  execution_boundary: "CALLER_CONTROLLED__NOT_ATTESTED_BY_TEST_MODULE",
  runtime: {
    node_version: process.version,
    platform: process.platform,
    arch: process.arch,
  },
  source_bindings: {
    adapter_sha256: sha256(readFileSync(scriptPath)),
    test_sha256: sha256(readFileSync(testPath)),
    projector_sha256: sha256(readFileSync(projectorPath)),
    canonical_state_sha256: sha256(readFileSync(canonicalStatePath)),
    strict_json_sha256: sha256(readFileSync(strictJsonPath)),
  },
  tests_total: results.length,
  tests_passed: results.length - failed.length,
  tests_failed: failed.length,
  assertions,
  scenarios: results,
  non_implications: [
    "NO_PRODUCT_RUNTIME_BINDING_ATTESTED",
    "REFERENCE_POSTCONDITION_NEVER_GRANTS_PRODUCT_ACTION_AUTHORITY",
    "NO_HARDWARE_OR_RTOS_ATTESTATION",
    "NO_PRODUCTION_CEO_AUTHORITY_CONSUMED",
    "NO_INDEPENDENT_AUDITOR_SEPARATION",
    "NO_TSA_SECURE_MONOTONIC_OR_HARDWARE_CLOCK_ATTESTATION",
  ],
};
const serializedReport = `${JSON.stringify(report, null, 2)}\n`;
if (process.argv[2]) writeFileSync(process.argv[2], serializedReport, { encoding: "utf8", flag: "wx" });
process.stdout.write(serializedReport);
if (failed.length > 0) process.exitCode = 1;
