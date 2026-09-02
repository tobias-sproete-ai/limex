export const TARGET_UTC_ISO = "2026-09-15T21:59:00Z";
export const TARGET_UTC_MS = Date.parse(TARGET_UTC_ISO);
export const DEFAULT_RESYNC_INTERVAL_MS = 300_000;

export const COUNTDOWN_STATE = Object.freeze({
  SYNCING: "TIME_SYNC_PENDING",
  SYNC_UNAVAILABLE: "TIME_SYNC_UNAVAILABLE__FAIL_CLOSED",
  SYNC_STALE: "TIME_SYNC_STALE__DISPLAY_ONLY",
  T_MINUS: "COUNTDOWN_ACTIVE",
  TARGET_REACHED_LOCKED: "TARGET_REACHED__RELEASE_LOCKED",
  RELEASE_VERIFIED: "SYSTEM_ONLINE__DISPATCH_READY"
});

const INTEGER = Number.isInteger;

export function assertFiniteTimestamp(value, label) {
  if (!Number.isFinite(value)) {
    throw new TypeError(`${label} must be a finite epoch-millisecond value`);
  }
  return value;
}

export function splitDuration(remainingMs) {
  const safeMs = Math.max(0, Math.floor(assertFiniteTimestamp(remainingMs, "remainingMs")));
  const totalSeconds = Math.floor(safeMs / 1_000);
  return Object.freeze({
    days: Math.floor(totalSeconds / 86_400),
    hours: Math.floor(totalSeconds / 3_600) % 24,
    minutes: Math.floor(totalSeconds / 60) % 60,
    seconds: totalSeconds % 60,
    milliseconds: safeMs % 1_000
  });
}

export function padUnit(value, width = 2) {
  if (!INTEGER(value) || value < 0) {
    throw new TypeError("countdown units must be non-negative integers");
  }
  return String(value).padStart(width, "0");
}

export function formatDuration(parts, includeMilliseconds = false) {
  const base = [
    padUnit(parts.days),
    padUnit(parts.hours),
    padUnit(parts.minutes),
    padUnit(parts.seconds)
  ].join(" : ");
  return includeMilliseconds ? `${base}.${padUnit(parts.milliseconds, 3)}` : base;
}

export async function fetchServerTimeSample({
  url,
  fetchImpl = globalThis.fetch,
  monotonicNow = () => globalThis.performance.now(),
  maxRoundTripMs = 2_500
}) {
  if (!url || typeof url !== "string") {
    throw new TypeError("a server time endpoint is required");
  }
  if (typeof fetchImpl !== "function" || typeof monotonicNow !== "function") {
    throw new TypeError("fetchImpl and monotonicNow must be functions");
  }

  const requestStartedMonoMs = monotonicNow();
  const response = await fetchImpl(url, {
    method: "HEAD",
    cache: "no-store",
    credentials: "same-origin",
    redirect: "error"
  });
  const responseReceivedMonoMs = monotonicNow();
  const roundTripMs = responseReceivedMonoMs - requestStartedMonoMs;

  if (!response?.ok) {
    throw new Error(`server time endpoint returned ${response?.status ?? "no response"}`);
  }
  if (!Number.isFinite(roundTripMs) || roundTripMs < 0 || roundTripMs > maxRoundTripMs) {
    throw new Error(`server time sample exceeded the ${maxRoundTripMs} ms RTT bound`);
  }

  const preciseHeader = response.headers.get("x-limex-server-time");
  const dateHeader = response.headers.get("date");
  const rawServerTime = preciseHeader || dateHeader;
  const serverEpochMs = Date.parse(rawServerTime || "");
  assertFiniteTimestamp(serverEpochMs, "server time");

  return Object.freeze({
    serverEpochMs,
    monotonicAnchorMs: requestStartedMonoMs + roundTripMs / 2,
    roundTripMs,
    source: preciseHeader ? "X_LIMEX_SERVER_TIME" : "HTTP_DATE",
    precisionMs: preciseHeader ? 1 : 1_000
  });
}

export class MonotonicServerClock {
  #monotonicNow;
  #sample = null;

  constructor(monotonicNow = () => globalThis.performance.now()) {
    if (typeof monotonicNow !== "function") {
      throw new TypeError("monotonicNow must be a function");
    }
    this.#monotonicNow = monotonicNow;
  }

  bind(sample) {
    assertFiniteTimestamp(sample?.serverEpochMs, "sample.serverEpochMs");
    assertFiniteTimestamp(sample?.monotonicAnchorMs, "sample.monotonicAnchorMs");
    this.#sample = Object.freeze({ ...sample });
    return this.#sample;
  }

  get ready() {
    return this.#sample !== null;
  }

  get sample() {
    return this.#sample;
  }

  nowMs() {
    if (!this.#sample) {
      throw new Error("server clock is not synchronized");
    }
    return this.#sample.serverEpochMs + (this.#monotonicNow() - this.#sample.monotonicAnchorMs);
  }

  sampleAgeMs() {
    if (!this.#sample) return Number.POSITIVE_INFINITY;
    return Math.max(0, this.#monotonicNow() - this.#sample.monotonicAnchorMs);
  }
}

export class ReleaseReceiptLatch {
  #admission = null;

  get verified() {
    return this.#admission !== null;
  }

  get admission() {
    return this.#admission;
  }

  async admit(receipt, verifier, expectedTargetUtc = TARGET_UTC_ISO) {
    if (typeof verifier !== "function") {
      throw new TypeError("a cryptographic receipt verifier capability is required");
    }
    if (!receipt || receipt.target_utc !== expectedTargetUtc || !receipt.receipt_id) {
      throw new Error("release receipt binding does not match the countdown target");
    }

    const verdict = await verifier(receipt);
    if (verdict !== true) {
      throw new Error("release receipt signature verification failed");
    }

    this.#admission = Object.freeze({
      receiptId: receipt.receipt_id,
      targetUtc: receipt.target_utc,
      evidence: "CRYPTOGRAPHIC_VERIFIER_RETURNED_TRUE"
    });
    return this.#admission;
  }
}

export class CountdownModel {
  constructor({ targetUtcMs = TARGET_UTC_MS } = {}) {
    this.targetUtcMs = assertFiniteTimestamp(targetUtcMs, "targetUtcMs");
  }

  snapshot(serverNowMs, releaseVerified = false, includeMilliseconds = false) {
    assertFiniteTimestamp(serverNowMs, "serverNowMs");
    const remainingMs = Math.max(0, this.targetUtcMs - serverNowMs);
    const parts = splitDuration(remainingMs);
    const targetReached = remainingMs === 0;
    const state = !targetReached
      ? COUNTDOWN_STATE.T_MINUS
      : releaseVerified
        ? COUNTDOWN_STATE.RELEASE_VERIFIED
        : COUNTDOWN_STATE.TARGET_REACHED_LOCKED;

    return Object.freeze({
      state,
      targetReached,
      releaseVerified: Boolean(releaseVerified),
      remainingMs,
      parts,
      display: formatDuration(parts, includeMilliseconds)
    });
  }
}
