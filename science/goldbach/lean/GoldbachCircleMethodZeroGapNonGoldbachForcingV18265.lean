import GoldbachCircleMethodZeroGapCaseSelectedTransferV18264

/-!
# Goldbach V1.8.265: zero-gap non-Goldbach forcing alternatives

The corrected pointwise transfer is contraposed without hiding any analytic
failure channel.  A hypothetical non-Goldbach target forces a failed model
reserve, a large selected residual, a large selected centered correction, or
an excessive prime-power defect.
-/

open scoped Classical BigOperators

set_option autoImplicit false

namespace GoldbachCircleMethodZeroGapNonGoldbachForcingV18265

open GoldbachPurePrimeAdequacyV15
open GoldbachVonMangoldtDecompositionV16
open GoldbachCircleMethodStructurallyAdmissibleActiveSlotV18258
open GoldbachCircleMethodExceptionalZeroGapAttestationRepairV18263
open GoldbachCircleMethodZeroGapCaseSelectedTransferV18264

theorem not_goldbachAt_forces_zeroGapCaseSelected_failure_channel
    (M B N : ℕ) (rho : ℝ) (hBN : B ≤ N)
    (hR2 : 2 ≤ (B : ℝ)^rho)
    (ExceptionalZeroAt :
      StructurallyAdmissibleActiveSlot ⌊((B : ℝ)^rho)^2⌋₊ → ℝ → Prop)
    (c : ExceptionalZeroGapCase ⌊((B : ℝ)^rho)^2⌋₊ ExceptionalZeroAt)
    (hNot : ¬ GoldbachAt N) :
    (zeroGapCaseSelectedModelAt B rho ExceptionalZeroAt c (N : ℤ)).re ≤
        (M : ℝ) / 1024 ∨
      (M : ℝ) / 4096 ≤
        ‖zeroGapCaseSelectedResidualAt B rho hR2 ExceptionalZeroAt c (N : ℤ)‖ ∨
      (M : ℝ) / 4096 ≤
        ‖zeroGapCaseSelectedCenteredCorrectionAt
          B rho ExceptionalZeroAt c (N : ℤ)‖ ∨
      (M : ℝ) / 2048 < primePowerDefect N := by
  by_cases hModel :
      (M : ℝ) / 1024 <
        (zeroGapCaseSelectedModelAt B rho ExceptionalZeroAt c (N : ℤ)).re
  · by_cases hResidual :
        ‖zeroGapCaseSelectedResidualAt B rho hR2 ExceptionalZeroAt c (N : ℤ)‖ <
          (M : ℝ) / 4096
    · by_cases hCorrection :
          ‖zeroGapCaseSelectedCenteredCorrectionAt
            B rho ExceptionalZeroAt c (N : ℤ)‖ < (M : ℝ) / 4096
      · by_cases hDefect : primePowerDefect N ≤ (M : ℝ) / 2048
        · exact False.elim (hNot
            (goldbachAt_of_zeroGapCaseSelected_reserve_and_error_budgets
              M B N rho hBN hR2 ExceptionalZeroAt c hModel hResidual
                hCorrection hDefect))
        · exact Or.inr (Or.inr (Or.inr (lt_of_not_ge hDefect)))
      · exact Or.inr (Or.inr (Or.inl (le_of_not_gt hCorrection)))
    · exact Or.inr (Or.inl (le_of_not_gt hResidual))
  · exact Or.inl (le_of_not_gt hModel)

/-- Once model reserve and defect absorption are separately established, a
hypothetical exception must enter one of the two exact accounting-error
channels. -/
theorem not_goldbachAt_forces_selected_residual_or_correction
    (M B N : ℕ) (rho : ℝ) (hBN : B ≤ N)
    (hR2 : 2 ≤ (B : ℝ)^rho)
    (ExceptionalZeroAt :
      StructurallyAdmissibleActiveSlot ⌊((B : ℝ)^rho)^2⌋₊ → ℝ → Prop)
    (c : ExceptionalZeroGapCase ⌊((B : ℝ)^rho)^2⌋₊ ExceptionalZeroAt)
    (hModel :
      (M : ℝ) / 1024 <
        (zeroGapCaseSelectedModelAt B rho ExceptionalZeroAt c (N : ℤ)).re)
    (hDefect : primePowerDefect N ≤ (M : ℝ) / 2048)
    (hNot : ¬ GoldbachAt N) :
    (M : ℝ) / 4096 ≤
        ‖zeroGapCaseSelectedResidualAt B rho hR2 ExceptionalZeroAt c (N : ℤ)‖ ∨
      (M : ℝ) / 4096 ≤
        ‖zeroGapCaseSelectedCenteredCorrectionAt
          B rho ExceptionalZeroAt c (N : ℤ)‖ := by
  rcases not_goldbachAt_forces_zeroGapCaseSelected_failure_channel
      M B N rho hBN hR2 ExceptionalZeroAt c hNot with
      hModelFail | hResidual | hCorrection | hDefectFail
  · linarith
  · exact Or.inl hResidual
  · exact Or.inr hCorrection
  · linarith

end GoldbachCircleMethodZeroGapNonGoldbachForcingV18265

