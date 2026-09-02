# LIMEX deterministic countdown engine v0.1.1

Status: `PUBLIC_SOURCE__DISPLAY_ONLY__NOT_RELEASE_AUTHORITY`

This zero-dependency candidate renders the deployment countdown for the fixed
target `2026-09-15T21:59:00Z` (`2026-09-15 23:59:00 MESZ`). It obtains an
initial server-time sample, binds that sample to the browsing context's
monotonic `performance.now()` clock and resynchronizes every 300 seconds.

The client never derives release authority from the countdown. At T-zero it
enters `TARGET_REACHED__RELEASE_LOCKED`. The visual
`SYSTEM_ONLINE__DISPATCH_READY` state is reachable only after a separately
provided receipt verifier returns `true` for a target-bound receipt. Protected
resources must still enforce the receipt server-side; the client state is a
display only and is never an authentication boundary.

## Components

- `src/countdown-core.mjs`: pure time, state and receipt-latch contracts.
- `src/countdown-widget.mjs`: semantic Web Component with Bauhaus grid.
- `server/dev-server.mjs`: local same-origin time endpoint and demo server.
- `cli/countdown-status.mjs`: terminal readout; fails closed without `--time-url`.
- `test/countdown-core.test.mjs`: deterministic acceptance tests.

## Local validation

```sh
npm test
npm run demo
node cli/countdown-status.mjs --time-url http://127.0.0.1:4177/api/time
```

## Explicit limits

- `performance.now()` is monotonic within the active execution context; it is
  not a physical clock guarantee across reloads, process restarts or every
  suspend/resume implementation. Visibility resume triggers a new time sample.
- The HTTP `Date` fallback has second-level precision. The preferred
  `X-Limex-Server-Time` header carries an ISO-8601 millisecond timestamp.
- Network asymmetry remains inside the measured RTT/precision uncertainty.
- No client-side code can prove or enforce authorization for a protected
  server resource.

## Provenance

This public successor preserves the executable source of the independently
validated local candidate. Its predecessor is bound by:

- candidate manifest SHA-256:
  `15a326f50dab6a6c2212decaf6fa73d593ecae8929a5270378ddf35d2c97fe65`
- candidate tree SHA-256:
  `d3c209533d8816afe4bf3b71a9c1840ed5c801776e53bbbe7777ab23ab4ac013`

Publication changes status and public-facing documentation only. It does not
create release authority, production-key attestation or a proof beyond the
bounded checks recorded in `ACCEPTANCE_RECEIPT.json`.
