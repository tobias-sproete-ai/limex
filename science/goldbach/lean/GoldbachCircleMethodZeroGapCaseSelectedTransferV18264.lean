import GoldbachCircleMethodExceptionalZeroGapAttestationRepairV18263

/-!
# Goldbach V1.8.264: zero-gap case-selected source and Goldbach transfer

This module rebuilds the V1.8.261--262 case-selected chain with the corrected
active exponent `zeroGap = 1 - beta`.  It supersedes the active semantics of
those modules while retaining their audit history.
-/

open scoped Classical BigOperators

set_option autoImplicit false

namespace GoldbachCircleMethodZeroGapCaseSelectedTransferV18264

open GoldbachPurePrimeAdequacyV15
open GoldbachVonMangoldtDecompositionV16
open GoldbachCircleMethodActualResidualLargeValueTransferV18224
open GoldbachCircleMethodActualResidualExactDecompositionV18225
open GoldbachCircleMethodActiveResidualExactDecompositionV18251
open GoldbachCircleMethodStructurallyAdmissibleActiveSlotV18258
open GoldbachCircleMethodNonGoldbachBlockSourceDefectBridgeV18237
open GoldbachCircleMethodExceptionalZeroGapAttestationRepairV18263

noncomputable def zeroGapCaseSelectedModelAt
    (B : ℕ) (rho : ℝ)
    (ExceptionalZeroAt :
      StructurallyAdmissibleActiveSlot ⌊((B : ℝ)^rho)^2⌋₊ → ℝ → Prop)
    (c : ExceptionalZeroGapCase ⌊((B : ℝ)^rho)^2⌋₊ ExceptionalZeroAt)
    (k : ℤ) : ℂ :=
  match c with
  | .absent _ => canonicalPrincipalModelAt B rho k
  | .active d => canonicalAdjustedModelAt B rho d.zeroGap d.slot.val k

noncomputable def zeroGapCaseSelectedResidualAt
    (B : ℕ) (rho : ℝ) (hR2 : 2 ≤ (B : ℝ)^rho)
    (ExceptionalZeroAt :
      StructurallyAdmissibleActiveSlot ⌊((B : ℝ)^rho)^2⌋₊ → ℝ → Prop)
    (c : ExceptionalZeroGapCase ⌊((B : ℝ)^rho)^2⌋₊ ExceptionalZeroAt)
    (k : ℤ) : ℂ :=
  match c with
  | .absent _ => canonicalPrincipalResidualAt B rho hR2 k
  | .active d =>
      canonicalActiveResidualAt B rho hR2 d.zeroGap d.slot.val k

noncomputable def zeroGapCaseSelectedCenteredCorrectionAt
    (B : ℕ) (rho : ℝ)
    (ExceptionalZeroAt :
      StructurallyAdmissibleActiveSlot ⌊((B : ℝ)^rho)^2⌋₊ → ℝ → Prop)
    (c : ExceptionalZeroGapCase ⌊((B : ℝ)^rho)^2⌋₊ ExceptionalZeroAt)
    (k : ℤ) : ℂ :=
  match c with
  | .absent _ => canonicalCenteredErrorCorrectionAt B rho k
  | .active d => canonicalAdjustedCenteredErrorCorrectionAt
      B rho d.zeroGap d.slot.val k

theorem canonicalBlockSourceAt_eq_zeroGapCaseSelected_decomposition
    (B : ℕ) (rho : ℝ) (hR2 : 2 ≤ (B : ℝ)^rho)
    (ExceptionalZeroAt :
      StructurallyAdmissibleActiveSlot ⌊((B : ℝ)^rho)^2⌋₊ → ℝ → Prop)
    (c : ExceptionalZeroGapCase ⌊((B : ℝ)^rho)^2⌋₊ ExceptionalZeroAt)
    (k : ℤ) :
    canonicalBlockSourceAt B k =
      zeroGapCaseSelectedModelAt B rho ExceptionalZeroAt c k +
        zeroGapCaseSelectedResidualAt B rho hR2 ExceptionalZeroAt c k +
        zeroGapCaseSelectedCenteredCorrectionAt B rho ExceptionalZeroAt c k := by
  cases c with
  | absent hAbsent =>
      simpa [zeroGapCaseSelectedModelAt, zeroGapCaseSelectedResidualAt,
        zeroGapCaseSelectedCenteredCorrectionAt] using
        canonicalBlockSourceAt_eq_model_add_residual_add_centeredError
          B rho hR2 k
  | active d =>
      simpa [zeroGapCaseSelectedModelAt, zeroGapCaseSelectedResidualAt,
        zeroGapCaseSelectedCenteredCorrectionAt] using
        canonicalBlockSourceAt_eq_adjustedModel_add_activeResidual_add_adjustedError
          B rho hR2 d.zeroGap d.slot.val k

/-- Corrected conditional transfer to the real prime-pair predicate. -/
theorem goldbachAt_of_zeroGapCaseSelected_reserve_and_error_budgets
    (M B N : ℕ) (rho : ℝ) (hBN : B ≤ N)
    (hR2 : 2 ≤ (B : ℝ)^rho)
    (ExceptionalZeroAt :
      StructurallyAdmissibleActiveSlot ⌊((B : ℝ)^rho)^2⌋₊ → ℝ → Prop)
    (c : ExceptionalZeroGapCase ⌊((B : ℝ)^rho)^2⌋₊ ExceptionalZeroAt)
    (hModel :
      (M : ℝ) / 1024 <
        (zeroGapCaseSelectedModelAt B rho ExceptionalZeroAt c (N : ℤ)).re)
    (hResidual :
      ‖zeroGapCaseSelectedResidualAt B rho hR2 ExceptionalZeroAt c (N : ℤ)‖ <
        (M : ℝ) / 4096)
    (hCorrection :
      ‖zeroGapCaseSelectedCenteredCorrectionAt B rho ExceptionalZeroAt c (N : ℤ)‖ <
        (M : ℝ) / 4096)
    (hDefect : primePowerDefect N ≤ (M : ℝ) / 2048) :
    GoldbachAt N := by
  have hResidualRe :
      -((M : ℝ) / 4096) <
        (zeroGapCaseSelectedResidualAt B rho hR2 ExceptionalZeroAt c (N : ℤ)).re := by
    have hAbs := Complex.abs_re_le_norm
      (zeroGapCaseSelectedResidualAt B rho hR2 ExceptionalZeroAt c (N : ℤ))
    have hNeg := neg_abs_le
      (zeroGapCaseSelectedResidualAt B rho hR2 ExceptionalZeroAt c (N : ℤ)).re
    linarith
  have hCorrectionRe :
      -((M : ℝ) / 4096) <
        (zeroGapCaseSelectedCenteredCorrectionAt B rho ExceptionalZeroAt c (N : ℤ)).re := by
    have hAbs := Complex.abs_re_le_norm
      (zeroGapCaseSelectedCenteredCorrectionAt B rho ExceptionalZeroAt c (N : ℤ))
    have hNeg := neg_abs_le
      (zeroGapCaseSelectedCenteredCorrectionAt B rho ExceptionalZeroAt c (N : ℤ)).re
    linarith
  have hDecomp := canonicalBlockSourceAt_eq_zeroGapCaseSelected_decomposition
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

end GoldbachCircleMethodZeroGapCaseSelectedTransferV18264

