# SFH FUZZI — reproducible software stress test

SFH FUZZI stresses the deterministic LIMEX functional core with high logical event density, ordering changes, fragmentation, dropouts, hash tampering, and hard size limits. The capsule also tests a separate global-hold-release reference adapter for crash recovery and postcondition readback.

“Frequency” means logical event density only. This artifact is not a physical Hz, RF, EMI, voltage, sensor, driver, RTOS, or hardware test.

## Reproducible capsule result

- Software stress harness: `18/18` vectors, `81` assertions, `0` failures.
- Hold-release reference adapter: `31/31` cases, `195` assertions, `0` failures.
- The reference adapter attests only `reference_postcondition_satisfied`; it never authorizes a product action (`action_allowed=false`, `fail_closed=true`).
- Reference run: macOS ARM64, Node.js `v24.13.1`.

The complete LIMEX successor precheck (`82/82` commands; `2,216/2,216` native checks) is private upstream evidence and cannot be reproduced from this narrow public capsule. Its evidence hashes are declared in the receipt; it is not presented as a public in-capsule run.

Authority-expiry decisions use the locally observed system clock; a supplied time value is only a coherence signal. This does not attest a TSA, secure monotonic clock, or hardware clock.

If the persisted security state is missing or corrupt, the reference path remains locked: recovery revokes the current trust anchor in the restored held state. Safe-integer counters are checked for exhaustion before mutation; an exhausted counter cannot produce a partial transition.

The recovery preflight completes before any quarantine, rename, or write operation. A combined corrupt-carrier and exhausted-counter case therefore produces no partial mutation.

## Run

The capsule has no external package dependencies. Node.js `v24.13.1` was used for the reference run:

```bash
npm test
```

Individual runs:

```bash
node tests/run_fuzzi_sfh_software_stress_v1.mjs
node tests/run_global_hold_release_adapter_v1_adversarial.mjs
```

`probe` is an authorization-oriented fail-closed command and is expected to exit nonzero without externally bound product enforcement. Use `inspect-reference` for diagnostic reference readback only.

Verify the file hashes separately:

```bash
shasum -a 256 -c SHA256SUMS
```

## Contents

- `scripts/`: functional core, canonical parser, and reference adapter.
- `tests/`: executable stress and fault-injection harnesses.
- `receipts/`: bound reference-run results.
- `schemas/`: local JSON schema for the capsule receipt.
- `GOLDSTANDARD_SFH_FUZZI_v1_0.md`: human-readable gold standard.
- `MARCUS_AND_TOBIAS.md`: free-use statement and the engineering rationale behind the extended FUZZI standard.
- `RECEIPT_SFH_FUZZI_v1_0.json`: machine-readable provenance and claim boundaries.
- `ARTIFACT_MANIFEST.json`: hash binding for every payload file including the receipt, with self-exclusion.
- `REPO_INTEGRATION_CONTRACT.json`: target path and current release/integration status.
- `NOTICE.md`: license and use status.

## Release boundary

The publication target for this component is `components/sfh-fuzzi/` under the dedicated `sfh-fuzzi-v1.0.0` tag. The tag and its externally readable GitHub release establish publication; this file does not claim that those external steps have already occurred. The public grant in `NOTICE.md` covers use, copying, modification, and distribution of the version identified by that tag without a license fee or separate agreement. The test and authority limits stated above remain unchanged.
