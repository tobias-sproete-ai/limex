import GoldbachCircleMethodExceptionalCorrelationBlockDecayV18524
import GoldbachCircleMethodHybridCenteredCentralMomentV18505

/-!
# Goldbach V1.8.525: hybrid-centered decaying source budget

The V1.8.524 pointwise sharpening is propagated through the actual dyadic
source block and central-target moment.  The exceptional slot now carries its
literal `((B : ℝ) / 2)^(-2*b)` factor.  The principal and nonprincipal
primitive channels are unchanged and remain separate open analytic targets.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

open scoped BigOperators Classical

namespace GoldbachCircleMethodHybridCenteredDecayingSourceBudgetV18525

open GoldbachCircleMethodActiveExceptionalCenteringV18129
open GoldbachCircleMethodActiveResidualExactDecompositionV18251
open GoldbachCircleMethodAdjustedCenteredCorrectionLiteralAdapterV18252
open GoldbachCircleMethodAdjustedCorrectionL2CompositionV18451
open GoldbachCircleMethodCanonicalBumpPrincipalFloorV18220
open GoldbachCircleMethodCanonicalCentralAdjustedPositiveV18403
open GoldbachCircleMethodCanonicalCentralSourceTransferV18404
open GoldbachCircleMethodCentralAdjustedCorrectionL2MomentV18452
open GoldbachCircleMethodExceptionalCorrelationBlockDecayV18524
open GoldbachCircleMethodHybridCenteredCentralMomentV18505
open GoldbachCircleMethodHybridCenteredCorrelationEnergyV18501
open GoldbachCircleMethodLogCutoffPresieveBindingV18120
open GoldbachCircleMethodPrincipalWindowBoundaryV18121
open GoldbachCircleMethodStructurallyAdmissibleActiveSlotV18258
open GoldbachCircleMethodSupportSeparatedCentralMomentV18485
open GoldbachCircleMethodSupportedModelErrorConvolutionV18182

/-- The corrected source-side budget with the actual exceptional exponent. -/
noncomputable def hybridCenteredDecayingSourceBudget
    (B : ℕ) (rho b : ℝ)
    (e : CharacterSlot ⌊((B : ℝ) ^ rho) ^ 2⌋₊) : ℝ :=
  let Q := ⌊((B : ℝ) ^ rho) ^ 2⌋₊
  let H := (B : ℝ) / ((B : ℝ) ^ rho) ^ 4
  let w := logWeight ((B : ℝ) ^ rho) canonicalLogBump
  ∑ n ∈ blockCarrier B,
    (centeredPrincipalCoefficientEnergy Q n w *
        centeredPrincipalSourceEnergy Q B n H +
      nonprincipalCoefficientEnergy Q n w *
        nonprincipalPrimitiveSourceEnergy Q B n H +
      ((9 / 4 : ℝ) * ((B : ℝ) / 2) ^ (-2 * b)) *
        ‖windowCoefficient e.1 n w e.2‖ ^ 2)

theorem hybridCenteredDecayingSourceBudget_nonneg
    (B : ℕ) (rho b : ℝ)
    (e : CharacterSlot ⌊((B : ℝ) ^ rho) ^ 2⌋₊) :
    0 ≤ hybridCenteredDecayingSourceBudget B rho b e := by
  unfold hybridCenteredDecayingSourceBudget
  apply Finset.sum_nonneg
  intro n _hn
  unfold centeredPrincipalCoefficientEnergy centeredPrincipalSourceEnergy
    nonprincipalCoefficientEnergy nonprincipalPrimitiveSourceEnergy
  positivity

/-- Literal supported error energy bounded by the decay-preserving budget. -/
theorem supportedAdjustedErrorEnergy_le_three_decayingSourceBudget
    (B : ℕ) (rho b : ℝ)
    (e : CharacterSlot ⌊((B : ℝ) ^ rho) ^ 2⌋₊)
    (hB : 2 ≤ B)
    (hH : 1 ≤ (B : ℝ) / ((B : ℝ) ^ rho) ^ 4)
    (hb : 0 ≤ b) :
    supportedAdjustedErrorEnergy B rho b e ≤
      3 * hybridCenteredDecayingSourceBudget B rho b e := by
  unfold supportedAdjustedErrorEnergy hybridCenteredDecayingSourceBudget
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n hn
  have hnIoc : n ∈ Finset.Ioc (B / 2) B := by
    simpa only [blockCarrier] using hn
  rw [supportedAdjustedError, if_pos hnIoc]
  exact adjustedCenteredError_sq_le_hybrid_block_decay
    ⌊((B : ℝ) ^ rho) ^ 2⌋₊ B n
    ((B : ℝ) / ((B : ℝ) ^ rho) ^ 4) b
    (logWeight ((B : ℝ) ^ rho) canonicalLogBump) hB hH hb e

/-- Propagation through the actual convolution and complete central target
sweep, with the exceptional source decay retained. -/
theorem centralAdjustedCorrectionEnergy_le_decayingSourceBudget
    (m : ℕ) (hm : 1 ≤ m) (rho b : ℝ)
    (e : StructurallyAdmissibleActiveSlot
      ⌊(((8 * m : ℕ) : ℝ) ^ rho) ^ 2⌋₊)
    (hH : 1 ≤ ((8 * m : ℕ) : ℝ) /
      (((8 * m : ℕ) : ℝ) ^ rho) ^ 4)
    (hb : 0 ≤ b) :
    centralAdjustedCorrectionEnergy m rho b e ≤
      3 * hybridCenteredDecayingSourceBudget (8 * m) rho b e.val *
        centralAdjustedPartnerEnergy m rho b e := by
  have hB : 2 ≤ 8 * m := by omega
  have hsource :=
    supportedAdjustedErrorEnergy_le_three_decayingSourceBudget
      (8 * m) rho b e.val hB hH hb
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
        (3 * hybridCenteredDecayingSourceBudget (8 * m) rho b e.val) *
          adjustedCorrectionPartnerEnergy
            (8 * m) (centralTargetNat m i) rho b e.val := by
      apply Finset.sum_le_sum
      intro i _hi
      exact mul_le_mul_of_nonneg_right hsource (hpartnerPointNonneg i)
    _ = 3 * hybridCenteredDecayingSourceBudget (8 * m) rho b e.val *
        (∑ i ∈ Finset.range (2 * m + 1),
          adjustedCorrectionPartnerEnergy
            (8 * m) (centralTargetNat m i) rho b e.val) := by
      rw [Finset.mul_sum]

/-- Central signed error aggregate with the sharper source budget. -/
theorem central_adjusted_error_target_sum_abs_sq_le_decayingSourceBudget
    (m : ℕ) (hm : 1 ≤ m) (rho b : ℝ)
    (e : StructurallyAdmissibleActiveSlot
      ⌊(((8 * m : ℕ) : ℝ) ^ rho) ^ 2⌋₊)
    (hH : 1 ≤ ((8 * m : ℕ) : ℝ) /
      (((8 * m : ℕ) : ℝ) ^ rho) ^ 4)
    (hb : 0 ≤ b) :
    |centralAdjustedCenteredErrorTargetSum m rho b e| ^ 2 ≤
      (2 * m + 1 : ℕ) *
        (3 * hybridCenteredDecayingSourceBudget (8 * m) rho b e.val *
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
        (3 * hybridCenteredDecayingSourceBudget (8 * m) rho b e.val *
          centralAdjustedPartnerEnergy m rho b e) := by
      exact mul_le_mul_of_nonneg_left
        (centralAdjustedCorrectionEnergy_le_decayingSourceBudget
          m hm rho b e hH hb) (by positivity)

end GoldbachCircleMethodHybridCenteredDecayingSourceBudgetV18525
