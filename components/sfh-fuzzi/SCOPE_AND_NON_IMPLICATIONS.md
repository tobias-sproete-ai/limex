# Scope and non-implications

## What is tested

1. Deterministic projection of bounded defect-event batches.
2. Atomic denial without state mutation for malformed, oversized, missing-reference, or hash-corrupted inputs.
3. Terminal state/action coherence under event reordering and fragmentation.
4. A filesystem reference adapter for a held-to-unheld reference transition: signature and one-use capability validation, postcondition readback, crash recovery, reopen dominance, revocation, lock contention, and replay revalidation.
5. A negative regression showing that even a coherent rewrite of all adapter-root files can only satisfy the reference postcondition and cannot authorize a product action.
6. Authority-expiry enforcement against invalid and backdated caller-supplied time values, with the local system clock as the decision source.
7. Security-state corruption recovery that preserves denial by revoking the active trust anchor instead of reconstructing unknown one-use history.
8. Atomic fail-closed rejection when an epoch, transition, recovery, or target-mutation counter cannot be advanced within JavaScript's safe-integer range.
9. Cross-condition recovery preflight proving that corrupt state/target carriers are not quarantined or rewritten when a required safe-integer counter cannot advance.

## Trust boundary

The SHA-256 envelopes detect accidental or partial corruption; a writer of the complete adapter root can recompute them. Therefore the reference adapter always returns `action_allowed=false` and `fail_closed=true`. Product authorization requires a separate enforcement gate with a trust anchor and signed enforcement receipt outside the adapter root and outside that root writer's authority. That product gate is not implemented or claimed here.

## What is not established

- no proof of universal defect absence;
- no product-runtime integration or active LIMEX installation;
- no authorization derived from adapter-root files alone;
- no physical frequency, RF, EMI, voltage, thermal, sensor, bus, driver, kernel, RTOS, or hardware test;
- no hard real-time guarantee or certified recovery interval;
- no TSA, secure monotonic clock, hardware clock, or resistance to privileged host-clock manipulation;
- no packet-capture or syscall-trace completeness;
- no production CEO authority consumption;
- no proof of public-release completion from this file alone; publication requires external tag and release readback;
- no safety certification, conformity assessment, or legal conclusion.

## Five residual assurance dimensions

Any concrete deployment must independently address:

1. model adequacy and specification boundaries;
2. refinement, toolchain, and supply-chain integrity;
3. resource exhaustion and asynchronous behavior;
4. lifecycle, key, and state management;
5. end-to-end composition and system integration.

Carrier-specific voltage, timing, safe-state, watchdog, and environmental limits belong to a separately bound target and hazard contract. Synthetic limits are intentionally excluded from this capsule.
