import GoldbachCircleMethodSupportSeparatedSourceBudgetV18484

/-!
# Goldbach V1.8.485: support-separated central moment

The support-separated source budget is propagated through the literal
convolution and central target sweep. This yields a strictly sharper finite
moment interface than the former full-family adjusted-source product.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodSupportSeparatedCentralMomentV18485

open GoldbachCircleMethodActiveExceptionalCenteringV18129
open GoldbachCircleMethodActiveResidualExactDecompositionV18251
open GoldbachCircleMethodAdjustedCenteredCorrectionLiteralAdapterV18252
open GoldbachCircleMethodAdjustedCorrectionL2CompositionV18451
open GoldbachCircleMethodCanonicalCentralAdjustedPositiveV18403
open GoldbachCircleMethodCanonicalCentralSourceTransferV18404
open GoldbachCircleMethodCentralAdjustedCorrectionL2MomentV18452
open GoldbachCircleMethodLogCutoffPresieveBindingV18120
open GoldbachCircleMethodStructurallyAdmissibleActiveSlotV18258
open GoldbachCircleMethodSupportSeparatedSourceBudgetV18484

/-- Before replacing the source energy by any analytic majorant, one target's
literal correction is controlled by the exact supported error energy. -/
theorem canonical_adjusted_centered_correction_sq_le_supported_energy
    (B N : ℕ) (rho b : ℝ)
    (e : CharacterSlot ⌊((B : ℝ) ^ rho) ^ 2⌋₊) (hBN : B ≤ N) :
    ‖canonicalAdjustedCenteredErrorCorrectionAt B rho b e (N : ℤ)‖ ^ 2 ≤
      supportedAdjustedErrorEnergy B rho b e *
        adjustedCorrectionPartnerEnergy B N rho b e := by
  have hmajor := norm_canonicalAdjustedCenteredErrorCorrectionAt_le_majorant
    B N rho b e hBN
  have hmajorNonneg : 0 ≤ adjustedCenteredCorrectionMajorant B N rho b e := by
    unfold adjustedCenteredCorrectionMajorant
    exact Finset.sum_nonneg (fun n _hn =>
      mul_nonneg (norm_nonneg _)
        (add_nonneg (norm_nonneg _) (norm_nonneg _)))
  have hsq :
      ‖canonicalAdjustedCenteredErrorCorrectionAt B rho b e (N : ℤ)‖ ^ 2 ≤
        (adjustedCenteredCorrectionMajorant B N rho b e) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) hmajorNonneg).mpr hmajor
  have hcs :
      (adjustedCenteredCorrectionMajorant B N rho b e) ^ 2 ≤
        supportedAdjustedErrorEnergy B rho b e *
          adjustedCorrectionPartnerEnergy B N rho b e := by
    unfold adjustedCenteredCorrectionMajorant supportedAdjustedErrorEnergy
      adjustedCorrectionPartnerEnergy adjustedCorrectionPartnerNorm
    exact Finset.sum_mul_sq_le_sq_mul_sq (blockCarrier B)
      (fun n =>
        ‖GoldbachCircleMethodSupportedModelErrorConvolutionV18182.supportedAdjustedError
          B n ((B : ℝ) ^ rho) b
          GoldbachCircleMethodCanonicalBumpPrincipalFloorV18220.canonicalLogBump e‖)
      (fun n =>
        ‖blockInput B (N - n)‖ +
          ‖GoldbachCircleMethodSupportedModelErrorConvolutionV18182.supportedAdjustedModel
            B (N - n) ((B : ℝ) ^ rho) b
            GoldbachCircleMethodCanonicalBumpPrincipalFloorV18220.canonicalLogBump e‖)
  exact hsq.trans hcs

theorem centralAdjustedCorrectionEnergy_le_supportSeparated
    (m : ℕ) (rho b : ℝ)
    (e : StructurallyAdmissibleActiveSlot
      ⌊(((8 * m : ℕ) : ℝ) ^ rho) ^ 2⌋₊)
    (hH : 1 ≤ ((8 * m : ℕ) : ℝ) /
      (((8 * m : ℕ) : ℝ) ^ rho) ^ 4)
    (hb : 0 ≤ b) :
    centralAdjustedCorrectionEnergy m rho b e ≤
      3 * supportSeparatedSourceBudget (8 * m) rho b e.val *
        centralAdjustedPartnerEnergy m rho b e := by
  have hsource :=
    supportedAdjustedErrorEnergy_le_three_supportSeparatedSourceBudget
      (8 * m) rho b e.val hH hb
  have hpartnerPointNonneg (i : ℕ) :
      0 ≤ adjustedCorrectionPartnerEnergy
        (8 * m) (centralTargetNat m i) rho b e.val := by
    unfold adjustedCorrectionPartnerEnergy
    positivity
  unfold centralAdjustedCorrectionEnergy centralAdjustedPartnerEnergy
  calc
    (∑ i ∈ Finset.range (2 * m + 1),
        ‖canonicalAdjustedCenteredErrorCorrectionAt
          (8 * m) rho b e.val (centralTargetNat m i : ℤ)‖ ^ 2) ≤
      ∑ i ∈ Finset.range (2 * m + 1),
        supportedAdjustedErrorEnergy (8 * m) rho b e.val *
          adjustedCorrectionPartnerEnergy
            (8 * m) (centralTargetNat m i) rho b e.val := by
      apply Finset.sum_le_sum
      intro i _hi
      apply canonical_adjusted_centered_correction_sq_le_supported_energy
      simp only [centralTargetNat]
      omega
    _ ≤ ∑ i ∈ Finset.range (2 * m + 1),
        (3 * supportSeparatedSourceBudget (8 * m) rho b e.val) *
          adjustedCorrectionPartnerEnergy
            (8 * m) (centralTargetNat m i) rho b e.val := by
      apply Finset.sum_le_sum
      intro i _hi
      exact mul_le_mul_of_nonneg_right hsource (hpartnerPointNonneg i)
    _ = 3 * supportSeparatedSourceBudget (8 * m) rho b e.val *
        (∑ i ∈ Finset.range (2 * m + 1),
          adjustedCorrectionPartnerEnergy
            (8 * m) (centralTargetNat m i) rho b e.val) := by
      rw [Finset.mul_sum]

/-- Central signed aggregate bound with the sparse supports preserved all the
way to the target moment. -/
theorem central_adjusted_error_target_sum_abs_sq_le_supportSeparated
    (m : ℕ) (rho b : ℝ)
    (e : StructurallyAdmissibleActiveSlot
      ⌊(((8 * m : ℕ) : ℝ) ^ rho) ^ 2⌋₊)
    (hH : 1 ≤ ((8 * m : ℕ) : ℝ) /
      (((8 * m : ℕ) : ℝ) ^ rho) ^ 4)
    (hb : 0 ≤ b) :
    |centralAdjustedCenteredErrorTargetSum m rho b e| ^ 2 ≤
      (2 * m + 1 : ℕ) *
        (3 * supportSeparatedSourceBudget (8 * m) rho b e.val *
          centralAdjustedPartnerEnergy m rho b e) := by
  have hcs := sq_sum_le_card_mul_sum_sq
    (s := Finset.range (2 * m + 1))
    (f := fun i =>
      (canonicalAdjustedCenteredErrorCorrectionAt
        (8 * m) rho b e.val (centralTargetNat m i : ℤ)).re)
  have hpoint (i : ℕ) :
      ((canonicalAdjustedCenteredErrorCorrectionAt
        (8 * m) rho b e.val (centralTargetNat m i : ℤ)).re) ^ 2 ≤
      ‖canonicalAdjustedCenteredErrorCorrectionAt
        (8 * m) rho b e.val (centralTargetNat m i : ℤ)‖ ^ 2 := by
    rw [← sq_abs]
    exact (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).mpr
      (Complex.abs_re_le_norm _)
  unfold centralAdjustedCenteredErrorTargetSum
  rw [sq_abs]
  calc
    (∑ i ∈ Finset.range (2 * m + 1),
        (canonicalAdjustedCenteredErrorCorrectionAt
          (8 * m) rho b e.val (centralTargetNat m i : ℤ)).re) ^ 2 ≤
      ((Finset.range (2 * m + 1)).card : ℝ) *
        ∑ i ∈ Finset.range (2 * m + 1),
          ((canonicalAdjustedCenteredErrorCorrectionAt
            (8 * m) rho b e.val (centralTargetNat m i : ℤ)).re) ^ 2 := hcs
    _ ≤ (2 * m + 1 : ℕ) * centralAdjustedCorrectionEnergy m rho b e := by
      simp only [Finset.card_range]
      exact mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum fun i _hi => hpoint i) (by positivity)
    _ ≤ (2 * m + 1 : ℕ) *
        (3 * supportSeparatedSourceBudget (8 * m) rho b e.val *
          centralAdjustedPartnerEnergy m rho b e) := by
      exact mul_le_mul_of_nonneg_left
        (centralAdjustedCorrectionEnergy_le_supportSeparated
          m rho b e hH hb) (by positivity)

end GoldbachCircleMethodSupportSeparatedCentralMomentV18485
