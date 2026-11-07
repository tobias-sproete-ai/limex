# LIMEX Goldbach Scientific Review Path v1.0.0

## Purpose

This is a bounded route for evaluating one published formal-research capsule.
It lets a mathematician, formal-methods researcher, or critical reader identify
the exact claim, reproduce the relevant Lean build, challenge the weakest
dependency, and report a bounded finding.

It is **not** a request to trust LIMEX, a claim of peer review, or a claim that
the binary Goldbach conjecture has been proved.

## Fixed review target

| Field | Value |
| --- | --- |
| Capsule tag | [`goldbach-v1.8.795`](https://github.com/tobias-sproete-ai/limex/tree/goldbach-v1.8.795/science/goldbach) |
| Exact commit | `0f919d1785fb25dad8719fc8a6cb420037f5139e` |
| Formal entry point | [`lean/Audit.lean`](../lean/Audit.lean) |
| Source inventory | [`SOURCE_CLOSURE.json`](../SOURCE_CLOSURE.json) |
| Source hashes | [`SHA256SUMS`](../SHA256SUMS) |
| Formal status | [`STATUS.md`](../STATUS.md) |

The tagged capsule records the following global boundary:

```text
GLOBAL_GOLDBACH_STATUS = NO_PROOF
RUN_STATUS             = FAIL_CLOSED
```

The review target is a kernel-checked q=3 reduction chain and a
method-specific obstruction. It does not establish or falsify the binary
Goldbach conjecture.

## The standard review route

### 1. Orient — read one bounded claim

Start with the [q=3 method-witness claim card](V1_0_0_Q3_METHOD_WITNESS_CLAIM_CARD.md).
It separates the propositions that the Lean kernel checks from the analytic
obligations that remain open.

**Exit condition:** You can state what the capsule claims and what it
explicitly does not claim.

### 2. Reproduce — pin the public source state

Follow the [reproduction and challenge guide](V1_0_0_REPRODUCTION_AND_CHALLENGE_GUIDE.md)
to check out the exact tag, confirm the commit, inspect the source closure, and
run the published Lean build.

**Exit condition:** Either the exact tagged build is reproduced, or a bounded
reproduction discrepancy is recorded.

### 3. Challenge — inspect the decisive boundary

The recommended first review target is the distinction between:

- the formal propositions compiled through `lean/Audit.lean`; and
- the open sign-sensitive and minor-arc obligations required for any global
  Goldbach conclusion.

The method witness excludes one literal absolute-majorant composition. It does
not exclude all possible sign-sensitive arguments.

**Exit condition:** Your finding concerns one named theorem, assumption,
definition, source mapping, build result, or stated boundary.

### 4. Report — make the finding actionable

Use the [review finding template](V1_0_0_REVIEW_FINDING_TEMPLATE.md). A useful
finding identifies the exact artifact and line or symbol, states what was
observed, and distinguishes a build observation from a mathematical objection.

**Exit condition:** The finding can be independently reproduced or assessed
without relying on private context.

## Valid review outcomes

| Outcome | Meaning | Does not mean |
| --- | --- | --- |
| `BUILD_REPRODUCED` | The reviewer reproduced the pinned Lean build. | The binary Goldbach conjecture is proved. |
| `FORMAL_SCOPE_CONFIRMED` | The reviewer confirmed that a stated proposition is what Lean checked. | Every informal interpretation or external premise is correct. |
| `OPEN_OBLIGATION_CONFIRMED` | The reviewer confirmed that a stated gap remains open. | The surrounding research has no value. |
| `CLAIM_MISMATCH` | A document, theorem signature, or public description does not match. | The entire project is automatically invalid. |
| `BUILD_FAILURE` | The pinned build did not reproduce in the stated environment. | The cause has been identified. |

## What is deliberately out of scope

- A request for a blanket endorsement of the project.
- A claim of independent validation or peer review.
- A claim that a successful build proves the binary Goldbach conjecture.
- A request to evaluate every source file before reviewing any bounded result.
- Any new software license grant. The repository-root terms remain controlling.

## Citation and provenance convention

When referring to a review result, identify:

1. the capsule tag and exact commit above;
2. the reviewed file and theorem or symbol where applicable;
3. the local Lean and Mathlib versions reported by the capsule; and
4. whether the result is a reproduction observation, a formal-scope finding,
   an analytic objection, or an open obligation.

This convention preserves a simple scientific rule: a successful local check
is evidence about the exact checked artifact, not a substitute for independent
mathematical review.
