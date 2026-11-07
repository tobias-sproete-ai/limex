<!-- hello, world. -->

# LIMEX

> **Stochastic intelligence. Deterministically gated.**

$$\mathfrak{A}(\Delta) = \bigwedge_{g\in\mathcal{G}} g(\Delta) \qquad \neg\mathfrak{A}(\Delta) \Rightarrow \Delta \not\mapsto \Sigma$$

<!-- ρₙ = MerkleRoot(a₁, …, aₙ) // every branch remembers its root. -->

---

## Invariant

Only complete admission may change state.

Generative models propose transitions ($\Delta$). The admission boundary evaluates a declared invariant set ($\mathcal{G}$). Within that declared boundary, any failed required gate prevents the proposed transition from changing state ($\Sigma$).

If one required term is missing, stale, substituted or contradictory:

> **FAIL_CLOSED**

---

## Status

```text
STATE           PRE-RELEASE
PUBLIC SURFACE  ANNOUNCEMENT + COUNTDOWN + GOLDBACH LEAN AUDIT CAPSULE
CODE            COUNTDOWN + MATHEMATICAL LEAN SOURCES; LIMEX CORE NOT RELEASED
AUDIT           GOLDBACH CAPSULE BUILT; LIMEX CORE RELEASE GATES PENDING
AUTHORITY       NO RUNTIME OR DEPLOYMENT GRANT
```

This repository currently establishes the public announcement boundary and
publishes a narrowly scoped release-gate countdown utility plus a reproducible
mathematical Lean audit capsule.

Specifications, formula collections and reference implementations will be released only after their respective security, disclosure, licensing and publication gates have passed.

---

## Deployment gate countdown

Target: **2026-09-15 23:59:00 MESZ** (`2026-09-15T21:59:00Z`)

**[Open the live countdown](https://tobias-sproete-ai.github.io/limex/)**

The [zero-dependency countdown utility](components/release-countdown/) uses an
initial server-time sample and a monotonic in-page clock. It is display-only:
reaching zero never grants release, runtime or deployment authority.

---

## Goldbach Lean audit capsule

The [Goldbach v1.8.795 audit capsule](science/goldbach/) contains the exact
custom source closure, pinned Lean/Mathlib revisions, a public axiom-audit entry
point and reproducible build instructions.

Its final q=3 theorem is kernel-checked **conditionally**. Two substantive
analytic inputs remain explicit hypotheses; other denominator channels and the
minor arcs remain open. Therefore:

```text
GLOBAL_GOLDBACH_STATUS = NO_PROOF
```

## Goldbach public review route

The Goldbach capsule is presented as a bounded, reproducible review target —
not as a request for trust or a claim of independent validation. The exact
target is tag [`goldbach-v1.8.795`](https://github.com/tobias-sproete-ai/limex/tree/goldbach-v1.8.795/science/goldbach)
at commit `0f919d1785fb25dad8719fc8a6cb420037f5139e`.

- Start with the [scientific review path](science/goldbach/scientific-review/V1_0_0_SCIENTIFIC_REVIEW_PATH.md).
- Reproduce only the pinned capsule via the [reproduction guide](science/goldbach/scientific-review/V1_0_0_REPRODUCTION_AND_CHALLENGE_GUIDE.md).
- Report one falsifiable, bounded observation using the [finding template](science/goldbach/scientific-review/V1_0_0_REVIEW_FINDING_TEMPLATE.md).

A successful local build is evidence about the exact checked artifact. It is
not independent review and does not establish the binary Goldbach conjecture.
The number of public GitHub issues is not evidence of mathematical correctness
or review completeness.

---

## Evidence Boundary

This README describes the intended LIMEX architecture.

It is not a claim of universal safety, semantic truth, legal compliance, certification, patent grant or immunity against an arbitrarily compromised host or trust root.

---

## License

No public software-license grant is included at this pre-release stage. The
published countdown source remains all rights reserved unless and until a
separate license is added.

---

## Stay close

If you would like to follow the work as it unfolds:

- X: [@CngMkr](https://x.com/CngMkr)
- LinkedIn: [Tobias Spröte](https://www.linkedin.com/in/tobias-sproete/)
