#!/usr/bin/env node
import {
  CountdownModel,
  MonotonicServerClock,
  TARGET_UTC_ISO,
  fetchServerTimeSample
} from "../src/countdown-core.mjs";

const args = process.argv.slice(2);
const timeUrlIndex = args.indexOf("--time-url");
const json = args.includes("--json");
const timeUrl = timeUrlIndex >= 0 ? args[timeUrlIndex + 1] : null;

if (!timeUrl) {
  process.stderr.write("TIME_SYNC_UNAVAILABLE__FAIL_CLOSED: pass --time-url URL\n");
  process.exitCode = 2;
} else {
  try {
    const clock = new MonotonicServerClock();
    clock.bind(await fetchServerTimeSample({ url: timeUrl }));
    const snapshot = new CountdownModel().snapshot(clock.nowMs(), false);
    const output = {
      target_utc: TARGET_UTC_ISO,
      display: snapshot.display,
      status: snapshot.state,
      release_authority: "NOT_PRESENT__DISPLAY_ONLY"
    };
    if (json) {
      process.stdout.write(`${JSON.stringify(output)}\n`);
    } else {
      process.stdout.write([
        "LIMEX // DEPLOYMENT GATE",
        `TARGET : ${TARGET_UTC_ISO}`,
        `T-MINUS: ${snapshot.display}`,
        `STATUS : ${snapshot.state}`,
        "AUTH   : NOT_PRESENT__DISPLAY_ONLY"
      ].join("\n") + "\n");
    }
  } catch (error) {
    process.stderr.write(`TIME_SYNC_UNAVAILABLE__FAIL_CLOSED: ${error.message}\n`);
    process.exitCode = 3;
  }
}
