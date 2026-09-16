# A Note from Marcus & Tobias

## Free public use

SFH FUZZI v1.0.0 is offered for free public use under the permission notice in `NOTICE.md`. No license fee, commercial agreement, or separate permission request is required.

Anyone may use, study, copy, modify, and redistribute this version of the software and documentation, with or without modification. The permission notice in `NOTICE.md` defines this grant in full. SFH FUZZI is provided as-is, without warranty, certification, or fitness assurance for a particular purpose.

## Why we developed FUZZI further

Conventional fuzzing is excellent at exposing unexpected behaviour through large volumes of malformed or unusual inputs. We wanted to carry that principle further for deterministic, fail-closed state-transition systems.

We therefore developed SFH FUZZI as a deliberately uncompromising, reproducible stress standard. It does not stop when a happy-path test succeeds. It applies pressure at the points where robust systems tend to fail:

- event density at the declared limit and at the first invalid boundary;
- deterministic ordering and phase reversal;
- fragmentation, dropouts, and missing references;
- hash corruption and exact payload-size boundaries;
- crash recovery, replay, expiry, revocation, and lock contention;
- corrupt state, exhausted counters, and combined failure conditions; and
- postcondition readback with fail-closed denial whenever product authority is absent.

The aim is not to produce impressive test counts. The aim is to make weak assumptions visible, preserve negative evidence, and force every accepted transition to remain coherent under adverse conditions.

This version contains a reproducible software stress harness and a separate hold-release reference-adapter harness. The bound reference results are:

- `18/18` software-stress vectors, `81` assertions, `0` failures; and
- `31/31` hold-release cases, `195` assertions, `0` failures.

These results apply only to the released software scope. SFH FUZZI does not claim universal defect absence, production deployment authority, hard real-time behaviour, or physical RF, EMI, voltage, sensor, driver, RTOS, or hardware validation.

We are making SFH FUZZI freely available because stronger testing should be reproducible, inspectable, and open to further improvement.

**Marcus & Tobias**  
*SFH Core Architecture*
