# Reproduction and challenge guide v1.0.0

## Preconditions

You need Git and an Elan-managed Lean environment. The first cache retrieval
may require network access. No LIMEX account, API key, model, or private
dataset is required for the published capsule.

## Reproduce the exact public capsule

```bash
git clone https://github.com/tobias-sproete-ai/limex.git
cd limex
git checkout --detach goldbach-v1.8.795
git rev-parse HEAD
# Expected: 0f919d1785fb25dad8719fc8a6cb420037f5139e
cd science/goldbach
lake exe cache get
lake build
```

The target environment is declared in the tagged capsule:

```text
Lean:    leanprover/lean4:v4.33.1
Mathlib: 0df444a360eaa60ab8c11dca51a86af692955474
```

## Check integrity before interpretation

Before drawing a mathematical conclusion, inspect:

1. `SOURCE_CLOSURE.json` for the declared root modules and source closure;
2. `SHA256SUMS` for the published file-hash inventory; and
3. `lean/Audit.lean` for the exact public audit entry point.

Use a SHA-256 verifier appropriate to your platform to compare the listed
hashes with the corresponding files. If any source differs, report the
discrepancy before interpreting a build outcome.

## What to inspect after a successful build

The public audit entry point contains `#print axioms` commands for the named
Lean propositions. The intended audit condition is that the output identifies
neither `sorryAx` nor a project-specific axiom for those printed signatures.

A successful build establishes that the pinned Lean toolchain accepted the
published formal artifacts. It does **not** by itself validate an external
analytic premise, resolve an open q=3 gate, or prove the binary Goldbach
conjecture.

## Suggested review sequence

1. Read the [claim card](V1_0_0_Q3_METHOD_WITNESS_CLAIM_CARD.md).
2. Confirm the checked-out tag and commit.
3. Inspect the source closure and hashes.
4. Build the capsule.
5. Read the theorem signatures named in `lean/Audit.lean`.
6. Compare their scope with the public status and claim card.
7. Record one bounded finding using the
   [review finding template](V1_0_0_REVIEW_FINDING_TEMPLATE.md).

## Preferred challenge categories

| Category | A useful report identifies |
| --- | --- |
| Reproduction mismatch | platform, tool versions, command, output, and exact failing artifact |
| Hash/source mismatch | expected hash, observed hash, and exact file path |
| Formal-scope mismatch | theorem symbol, observed signature, and alleged discrepancy |
| Assumption-boundary issue | external input, its representation, and why the boundary is unclear |
| Mathematical objection | precise statement, derivation or counterexample, and affected claim |
| Documentation mismatch | exact wording and the artifact that contradicts it |

## Stop conditions

Stop and report rather than infer a broader conclusion when:

- the checked-out commit differs from the pinned commit;
- an included hash does not match;
- the build environment differs materially from the declared toolchain;
- an audit signature exposes an undeclared axiom or `sorryAx`; or
- the claim being discussed extends beyond the stated q=3 method witness.
