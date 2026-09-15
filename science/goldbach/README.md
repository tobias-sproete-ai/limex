# LIMEX Goldbach Lean audit capsule v1.8.767

This directory is a self-contained, reproducible Lean 4 capsule for the
kernel-checked **conditional** q=3 project-branch closure developed in the
LIMEX Goldbach research run.

It is not a proof of the binary Goldbach conjecture.

```text
V1_8_767_THEOREM_STATUS       = KERNEL_PROVED
CONDITIONAL_COMPOSITION       = PROVED
SCALE_ESTIMATE_INHABITATION   = OPEN
SIGNED_RESERVE_INHABITATION   = OPEN
GLOBAL_GOLDBACH_STATUS        = NO_PROOF
```

## Reproduce

Install Git and Elan, then run:

```bash
git clone https://github.com/tobias-sproete-ai/limex.git
cd limex/science/goldbach
lake exe cache get
lake build
```

`lake build` compiles the exact custom import closure and the `Audit.lean`
entry point with warnings treated as errors. The printed assumption report is
expected to contain only Mathlib's standard logical principles used by these
theorems (`propext`, `Classical.choice`, and `Quot.sound`) and no `sorryAx`.

## What is proved

The final theorem
`GoldbachCircleMethodActualQ3FullConditionalClosureV18767.eventually_actualQ3_projectBranch_positive`
composes:

1. elementary eventual scale prerequisites;
2. a source-shaped fixed-modulus distribution estimate supplied as an explicit
   hypothesis;
3. a signed local-density reserve floor supplied as an explicit hypothesis;
4. an audited absorption step for the literal q=3 project branch.

Both substantive inputs remain visible in the theorem signature. The capsule
does not construct inhabitants for them, does not close the other denominator
channels or the minor arcs, and does not state a top-level Goldbach theorem.

## Reproducibility and provenance

- Lean: `leanprover/lean4:v4.33.1`
- Mathlib: `0df444a360eaa60ab8c11dca51a86af692955474`
- Root module: `GoldbachCircleMethodActualQ3FullConditionalClosureV18767`
- Exact source closure: `SOURCE_CLOSURE.json`
- File hashes: `SHA256SUMS`
- Audit entry: `lean/Audit.lean`

The sources are published for inspection under the licensing terms stated at
the repository root. No separate permission is implied by this audit capsule.

## External mathematical reference

The open fixed-modulus estimate is shaped for comparison with explicit bounds
for primes in arithmetic progressions. The corresponding primary reference is:

Ethan S. Lee, Greg Martin, Andrew V. Sutherland, and John D. Thompson,
"Explicit bounds for primes in arithmetic progressions," arXiv:1802.00085.

The paper is a reference for the external analytic input. Its results are not
silently imported as axioms or claimed as locally proved facts in this capsule.
