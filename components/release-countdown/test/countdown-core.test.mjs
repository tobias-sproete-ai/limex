import assert from "node:assert/strict";
import test from "node:test";

import {
  COUNTDOWN_STATE,
  CountdownModel,
  MonotonicServerClock,
  ReleaseReceiptLatch,
  TARGET_UTC_ISO,
  TARGET_UTC_MS,
  fetchServerTimeSample,
  formatDuration,
  splitDuration
} from "../src/countdown-core.mjs";

test("target timestamp binds Berlin MESZ to the requested UTC instant", () => {
  assert.equal(TARGET_UTC_MS, Date.parse("2026-09-15T23:59:00+02:00"));
});

test("duration formatting is stable and tabular", () => {
  const parts = splitDuration((((2 * 24 + 3) * 60 + 4) * 60 + 5) * 1_000 + 6);
  assert.deepEqual(parts, { days: 2, hours: 3, minutes: 4, seconds: 5, milliseconds: 6 });
  assert.equal(formatDuration(parts), "02 : 03 : 04 : 05");
  assert.equal(formatDuration(parts, true), "02 : 03 : 04 : 05.006");
});

test("T_MINUS never exposes release authority", () => {
  const model = new CountdownModel();
  const snapshot = model.snapshot(TARGET_UTC_MS - 1_001, false);
  assert.equal(snapshot.state, COUNTDOWN_STATE.T_MINUS);
  assert.equal(snapshot.releaseVerified, false);
});

test("T_ZERO clamps negative time and remains locked without a verified receipt", () => {
  const model = new CountdownModel();
  const snapshot = model.snapshot(TARGET_UTC_MS + 60_000, false);
  assert.equal(snapshot.display, "00 : 00 : 00 : 00");
  assert.equal(snapshot.remainingMs, 0);
  assert.equal(snapshot.state, COUNTDOWN_STATE.TARGET_REACHED_LOCKED);
});

test("T_ZERO becomes display-ready only after receipt verification", async () => {
  const latch = new ReleaseReceiptLatch();
  await latch.admit(
    { receipt_id: "receipt-001", target_utc: TARGET_UTC_ISO },
    async () => true
  );
  const snapshot = new CountdownModel().snapshot(TARGET_UTC_MS, latch.verified);
  assert.equal(snapshot.state, COUNTDOWN_STATE.RELEASE_VERIFIED);
});

test("receipt admission fails closed on target mismatch and invalid signature", async () => {
  const latch = new ReleaseReceiptLatch();
  await assert.rejects(
    latch.admit({ receipt_id: "x", target_utc: "2026-09-15T00:00:00Z" }, async () => true),
    /does not match/
  );
  await assert.rejects(
    latch.admit({ receipt_id: "x", target_utc: TARGET_UTC_ISO }, async () => false),
    /verification failed/
  );
  assert.equal(latch.verified, false);
});

test("monotonic server clock ignores subsequent wall-clock changes", () => {
  let monotonicMs = 100;
  const clock = new MonotonicServerClock(() => monotonicMs);
  clock.bind({ serverEpochMs: 1_000_000, monotonicAnchorMs: 100 });
  monotonicMs = 4_100;
  assert.equal(clock.nowMs(), 1_004_000);
});

test("server sample binds the midpoint of a bounded round trip", async () => {
  const monotonicValues = [1_000, 1_080];
  const sample = await fetchServerTimeSample({
    url: "/api/time",
    monotonicNow: () => monotonicValues.shift(),
    fetchImpl: async () => ({
      ok: true,
      status: 200,
      headers: new Headers({ "X-Limex-Server-Time": "2026-09-02T12:00:00.250Z" })
    })
  });
  assert.equal(sample.monotonicAnchorMs, 1_040);
  assert.equal(sample.roundTripMs, 80);
  assert.equal(sample.precisionMs, 1);
});

test("excessive RTT is rejected", async () => {
  const monotonicValues = [0, 3_001];
  await assert.rejects(
    fetchServerTimeSample({
      url: "/api/time",
      maxRoundTripMs: 2_500,
      monotonicNow: () => monotonicValues.shift(),
      fetchImpl: async () => ({
        ok: true,
        status: 200,
        headers: new Headers({ Date: "Wed, 02 Sep 2026 12:00:00 GMT" })
      })
    }),
    /RTT bound/
  );
});
