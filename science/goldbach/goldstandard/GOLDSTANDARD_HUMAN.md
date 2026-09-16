# Goldbach Quest — Q3 Source-Strength Decision V1.8.795

**Attestation time (UTC):** `2026-09-16T21:42:22Z`  
**Run status:** `FAIL_CLOSED`  
**Global proof status:** `NO_PROOF`  
**Goldbach proved:** `FALSE`  
**Goldbach falsified:** `FALSE`  
**Successful terminal outcome:** `NONE`

## Executive result

The autonomous run has not produced either of the two exclusive terminal
outcomes of the Goldbach Quest: neither an unconditional universal proof nor
a concrete verified counterexample.

It has, however, closed the current q=3 source-matching branch to a precise
method-level decision:

1. V1.8.794 kernel-verifies the exact transfer from the two reduced residue
   classes modulo three to the full Chebyshev fluctuation. The omitted zero
   class is exactly the powers-of-three correction.
2. V1.8.795 kernel-verifies that the literal absolute-value insertion of the
   cited BMOR source envelope into the current project normalization is too
   weak. After the project factor of `log(M)^21` and division by the linear
   reserve, the normalized majorant becomes

   \[
   2C\,\frac{\log(M)^{21}}{\log(M)}
   = 2C\log(M)^{20},
   \]

   and tends to infinity for every `C > 0`, including the conservative
   published constant `C = 1/840`.

This is a structural negative witness for this specific absolute-majorant
composition. It is not a lower bound for the actual signed correlation, not a
counterexample to Goldbach, and not a theorem excluding stronger source
estimates or a sign-sensitive argument.

## Kernel-attested results

### V1.8.794 — exact full-psi transfer

The following facts are kernel-checked:

- the full q=3 zero-residue von-Mangoldt mass equals the odd zero-residue mass;
- this mass is exactly `(Nat.log 3 x) • log(3)`;
- `psi(x)` is exactly partitioned into the three residue classes modulo three;
- the full fluctuation is exactly

  \[
  \psi(x)-x = E_1(x)+E_2(x)+\lfloor\log_3 x\rfloor\log 3;
  \]

- a two-class source bound therefore yields the full envelope

  \[
  |\psi(x)-x|
  < 2C\frac{x}{\log x}+\lfloor\log_3x\rfloor\log 3.
  \]

### V1.8.795 — BMOR project-scale obstruction

The following method-specific facts are kernel-checked:

- away from `log(M)=0`, the normalized absolute majorant equals
  `2*C*log(M)^20`;
- for every `C>0`, this quantity tends to infinity;
- the same conclusion holds for `C=1/840`.

## Axiom readback

Every audited theorem in V1.8.794 and V1.8.795 depends only on:

```text
propext
Classical.choice
Quot.sound
```

`sorryAx = 0`. No custom axiom was introduced.

## Exact remaining proof obligations

The following obligations remain open and may not be promoted to facts:

1. **A source-strength-compatible estimate.** A theorem whose decay survives
   the actual project normalization must be matched with all hypotheses and
   constants. The BMOR `x/log x` estimate does not do so through the tested
   absolute-value route.
2. **The sign-sensitive q=3 residual gate.** The project still lacks an
   unconditional inhabitant for `actualQ3PNTResidualSignedCorrelation`, which
   combines the linear cutoff/mean profile with the genuine `psi(U)-U`
   fluctuation.
3. **Global minor-arc closure.** Closing one q=3 branch does not establish the
   required uniform control of every non-diagonal/minor-arc channel in the
   global Goldbach argument.

The exact reduced implication in V1.8.793 remains conditional: positivity of
the composite reserve follows only if the two explicit prime-power debits and
the signed PNT residual remain strictly below the base reserve.

## Source boundary

The external source checked for the explicit arithmetic-progression envelope
is Bennett, Martin, O'Bryant and Rechnitzer, *Explicit bounds for primes in
arithmetic progressions*, arXiv:1802.00085:

<https://arxiv.org/abs/1802.00085>

The source supplies an estimate of the relevant `x/log x` shape. The project
itself owns — and V1.8.795 rejects — the attempted composition with its
`log(M)^21` absolute normalization. No claim is made that the source proves the
project gate.

## Provenance

| Artifact | SHA-256 |
|---|---|
| `GoldbachCircleMethodActualQ3FullPsiSourceTransferV18794.lean` | `331f968c016b6a25a279e50122be909adba9c6396f498199409901461b7ee4a8` |
| V1.8.794 audit source | `96a071381a1792ca3292112574dfe056a359d508ba40d87a8d1bdc0be7185697` |
| V1.8.794 `.olean` | `713640d8676afdc83965059c633bc9a82a268ee520c0788c473374d1ab19b5f7` |
| V1.8.794 raw axiom log | `14c141be2d5b712b464ef0c6988d697ed1744400987b5e523e10e46ee334a7ea` |
| `GoldbachCircleMethodActualQ3BMORProjectScaleObstructionV18795.lean` | `d21252023be6ef9bfd449938f5dc4b120c20377f671231b0414b9d967b2320aa` |
| V1.8.795 audit source | `c909513b9475edb9f711c32aa34839d0846b5c528cb80db0e42d92bf0c3ad7f6` |
| V1.8.795 `.olean` | `05badf70a2cddfbe4ac74d0fc330d54077ca7a45c2724ed22fdca589f9c35ff2` |
| V1.8.795 raw axiom log | `6f8f1527df50dcdfa13970636d797f27a7587f95b61049495a77122ce0dc4cb7` |

## Final classification

```ini
V1_8_794_KERNEL_STATUS              = PASS
V1_8_795_KERNEL_STATUS              = PASS
BMOR_ABSOLUTE_COMPOSITION           = STRUCTURAL_NEGATIVE_WITNESS
Q3_SIGN_SENSITIVE_RESIDUAL_GATE     = OPEN
GLOBAL_MINOR_ARC_CLOSURE            = OPEN
CLASS_I_A_UNIVERSAL_PROOF           = NOT_ACHIEVED
CLASS_I_B_CONCRETE_COUNTEREXAMPLE   = NOT_ACHIEVED
GOLDBACH_DECISION_STATUS            = UNRESOLVED
GLOBAL_PROOF_STATUS                 = NO_PROOF
RUN_STATUS                          = FAIL_CLOSED
```

The run therefore ends honestly at a bounded method barrier. Any stronger
claim would exceed the proved artifacts.
