# LIMEX Goldbach Lean audit capsule v1.8.795

This directory is a self-contained, reproducible Lean 4 capsule for the
kernel-checked q=3 reduction chain developed after the public V1.8.767
baseline.

It is **not** a proof or falsification of the binary Goldbach conjecture.

```text
V1_8_793_REDUCED_GATE          = KERNEL_PROVED_CONDITIONAL
V1_8_794_FULL_PSI_TRANSFER     = KERNEL_PROVED
V1_8_795_METHOD_WITNESS        = KERNEL_PROVED
Q3_SIGN_SENSITIVE_GATE         = OPEN
GLOBAL_MINOR_ARC_CLOSURE       = OPEN
GLOBAL_GOLDBACH_STATUS         = NO_PROOF
```

## Reproduce

Install Git and Elan, then run:

```bash
git clone https://github.com/tobias-sproete-ai/limex.git
cd limex
git checkout goldbach-v1.8.795
cd science/goldbach
lake exe cache get
lake build
```

`lake build` compiles the exact custom source set and the `Audit.lean` entry
point with warnings treated as errors. The printed assumption report must
contain no `sorryAx` and no project-specific axiom.

## Final reduced q=3 gate

V1.8.793 proves that the following inequality is sufficient for positivity of
the actual q=3 composite reserve:

\[
\frac{3}{2}D_3(M,q)
+R_{\mathrm{PNT}}(M,q,n)
+\frac{1}{2}D_2(M,q)
< B_3(M,R,n,P,q),
\]

where

\[
R_{\mathrm{PNT}}(M,q,n)
=C_{\mathrm{linear}}(M,q,n)
-\frac12 C_{\psi-x}(M,q,n).
\]

Here `D₂` and `D₃` are explicit powers-of-two and powers-of-three debits,
`B₃` is the positive base reserve, and `R_PNT` is the remaining sign-sensitive
q=3 residual.

## Exact source transfer

V1.8.794 proves the exact decomposition

\[
\psi(x)-x=E_1(x)+E_2(x)+\lfloor\log_3x\rfloor\log 3.
\]

Thus a two-class source estimate of size `C*x/log(x)` yields the full absolute
envelope

\[
|\psi(x)-x|
<2C\frac{x}{\log x}+\lfloor\log_3x\rfloor\log 3.
\]

## Method-specific negative witness

V1.8.795 proves that inserting this literal `x/log(x)` absolute envelope into
the present `log(M)^21` project normalization produces

\[
2C\frac{\log(M)^{21}}{\log(M)}
=2C\log(M)^{20}\longrightarrow\infty
\quad(C>0).
\]

This excludes only that absolute-majorant composition. It is not a lower bound
for the actual signed correlation, not a counterexample to Goldbach, and not a
global no-go theorem. A stronger source estimate or a genuinely sign-sensitive
argument may still close the local gate.

## What remains open

1. an unconditional sign-sensitive bound for
   `actualQ3PNTResidualSignedCorrelation`;
2. a source estimate whose exact decay survives the actual project
   normalization, if the absolute route is retained;
3. uniform closure of all non-diagonal and minor-arc channels outside this
   local q=3 branch.

## Reproducibility and provenance

- Lean: `leanprover/lean4:v4.33.1`
- Mathlib: `0df444a360eaa60ab8c11dca51a86af692955474`
- Root modules: V1.8.778, V1.8.782, V1.8.793 and V1.8.795
- Exact source inventory: `SOURCE_CLOSURE.json`
- File hashes: `SHA256SUMS`
- Audit entry: `lean/Audit.lean`
- Human-readable decision record: `goldstandard/GOLDSTANDARD_HUMAN.md`
- Machine-readable decision record: `goldstandard/GOLDSTANDARD_AGENTIC.json`

The sources are published for inspection under the licensing terms stated at
the repository root. No separate permission is implied by this audit capsule.

## External mathematical reference

The explicit arithmetic-progression estimate examined by the final method
witness is documented in:

M. A. Bennett, G. Martin, K. O'Bryant and A. Rechnitzer,
“Explicit bounds for primes in arithmetic progressions,” arXiv:1802.00085.

The paper is an external analytic source. Its results are not silently imported
as axioms and are not claimed to prove the project gate.
