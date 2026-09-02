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
PUBLIC SURFACE  ANNOUNCEMENT + COUNTDOWN UTILITY
CODE            COUNTDOWN UTILITY PUBLIC; LIMEX CORE NOT RELEASED
AUDIT           RELEASE GATES PENDING
AUTHORITY       NO RUNTIME OR DEPLOYMENT GRANT
```

This repository currently establishes the public announcement boundary and
publishes one narrowly scoped release-gate countdown utility.

Specifications, formula collections and reference implementations will be released only after their respective security, disclosure, licensing and publication gates have passed.

---

## Deployment gate countdown

Target: **2026-09-15 23:59:00 MESZ** (`2026-09-15T21:59:00Z`)

**[Open the live countdown](https://tobias-sproete-ai.github.io/limex/)**

The [zero-dependency countdown utility](components/release-countdown/) uses an
initial server-time sample and a monotonic in-page clock. It is display-only:
reaching zero never grants release, runtime or deployment authority.

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
