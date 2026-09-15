import GoldbachCircleMethodCaseSelectedExactSourceDecompositionV18261
import GoldbachCircleMethodNonGoldbachBlockSourceDefectBridgeV18237

/-!
# Goldbach V1.8.262: case-selected pointwise Goldbach transfer

This module closes the finite logical transfer from one case-selected model
reserve plus explicit residual, correction, and prime-power budgets to the
already kernel-checked pointwise Goldbach predicate.  Every analytic estimate
remains an explicit premise.
-/

open scoped Classical BigOperators

set_option autoImplicit false

namespace GoldbachCircleMethodCaseSelectedPointwiseGoldbachTransferV18262

open GoldbachPurePrimeAdequacyV15
open GoldbachVonMangoldtDecompositionV16
open GoldbachPrimePowerDefectBoundV161
open GoldbachCircleMethodActualResidualExactDecompositionV18225
open GoldbachCircleMethodStructurallyAdmissibleActiveSlotV18258
open GoldbachCircleMethodExceptionalZeroAttestationContractV18260
open GoldbachCircleMethodCaseSelectedExactSourceDecompositionV18261
open GoldbachCircleMethodNonGoldbachBlockSourceDefectBridgeV18237

/-- A pointwise Goldbach witness follows once the selected finite model keeps
`M/1024`, the two exact accounting errors each consume less than `M/4096`,
and the prime-power defect consumes at most `M/2048`. -/
theorem goldbachAt_of_caseSelected_reserve_and_error_budgets
    (M B N : ℕ) (rho : ℝ) (hBN : B ≤ N)
    (hR2 : 2 ≤ (B : ℝ)^rho)
    (ExceptionalZeroAt :
      StructurallyAdmissibleActiveSlot ⌊((B : ℝ)^rho)^2⌋₊ → ℝ → Prop)
    (c : ExceptionalZeroCase ⌊((B : ℝ)^rho)^2⌋₊ ExceptionalZeroAt)
    (hModel :
      (M : ℝ) / 1024 <
        (caseSelectedModelAt B rho ExceptionalZeroAt c (N : ℤ)).re)
    (hResidual :
      ‖caseSelectedResidualAt B rho hR2 ExceptionalZeroAt c (N : ℤ)‖ <
        (M : ℝ) / 4096)
    (hCorrection :
      ‖caseSelectedCenteredCorrectionAt B rho ExceptionalZeroAt c (N : ℤ)‖ <
        (M : ℝ) / 4096)
    (hDefect : primePowerDefect N ≤ (M : ℝ) / 2048) :
    GoldbachAt N := by
  have hResidualRe :
      -((M : ℝ) / 4096) <
        (caseSelectedResidualAt B rho hR2 ExceptionalZeroAt c (N : ℤ)).re := by
    have hAbs := Complex.abs_re_le_norm
      (caseSelectedResidualAt B rho hR2 ExceptionalZeroAt c (N : ℤ))
    have hNeg := neg_abs_le
      (caseSelectedResidualAt B rho hR2 ExceptionalZeroAt c (N : ℤ)).re
    linarith
  have hCorrectionRe :
      -((M : ℝ) / 4096) <
        (caseSelectedCenteredCorrectionAt B rho ExceptionalZeroAt c (N : ℤ)).re := by
    have hAbs := Complex.abs_re_le_norm
      (caseSelectedCenteredCorrectionAt B rho ExceptionalZeroAt c (N : ℤ))
    have hNeg := neg_abs_le
      (caseSelectedCenteredCorrectionAt B rho ExceptionalZeroAt c (N : ℤ)).re
    linarith
  have hDecomp := canonicalBlockSourceAt_eq_caseSelected_decomposition
    B rho hR2 ExceptionalZeroAt c (N : ℤ)
  have hDecompRe := congrArg Complex.re hDecomp
  simp only [Complex.add_re] at hDecompRe
  have hSource :
      (M : ℝ) / 2048 < (canonicalBlockSourceAt B (N : ℤ)).re := by
    linarith
  by_contra hNot
  have hSourceUpper :=
    canonicalBlockSourceAt_re_le_primePowerDefect_of_not_goldbachAt
      B N hBN hNot
  linarith

end GoldbachCircleMethodCaseSelectedPointwiseGoldbachTransferV18262
