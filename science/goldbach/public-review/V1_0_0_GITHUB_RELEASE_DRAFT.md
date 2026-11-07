# Draft GitHub release: `goldbach-public-review-v1.0.0`

**Publication status:** `DRAFT_ONLY — NOT_PUBLISHED`

## Title

`Goldbach public review surface v1.0.0 — target: goldbach-v1.8.795`

## Release body

This release publishes a documentation-only review surface for one reproducible
Lean 4 audit capsule. It does not alter or retag the underlying mathematical
capsule.

**Review-surface tag:** `goldbach-public-review-v1.0.0`  
**Review-surface commit:** `PENDING — set only when this exact documentation package is committed and tagged`

**Exact target**

- Tag: `goldbach-v1.8.795`
- Commit: `0f919d1785fb25dad8719fc8a6cb420037f5139e`
- Formal entry point: `science/goldbach/lean/Audit.lean`

**Status boundary**

```text
GLOBAL_GOLDBACH_STATUS = NO_PROOF
RUN_STATUS             = FAIL_CLOSED
```

The capsule contains a kernel-checked q=3 reduction chain and a
method-specific obstruction. It does not prove or falsify the binary Goldbach
conjecture, and this release does not claim independent validation or peer
review.

### Review route

1. Read `science/goldbach/scientific-review/V1_0_0_SCIENTIFIC_REVIEW_PATH.md`.
2. Reproduce the pinned source state using `V1_0_0_REPRODUCTION_AND_CHALLENGE_GUIDE.md`.
3. Submit one bounded observation through `V1_0_0_REVIEW_FINDING_TEMPLATE.md` or the corresponding GitHub issue form.

Before interpreting a build, check `SOURCE_CLOSURE.json`, `SHA256SUMS`, and
the exact source commit. A successful build is evidence about the checked
artifact only; it is not a global mathematical conclusion.

The repository-root licensing terms remain controlling. This draft grants no
new license. It must not be published until the review-surface commit is
independently fixed and a separate release decision is made.
