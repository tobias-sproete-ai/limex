import GoldbachCircleMethodCentralAdjustedCorrectionL2MomentV18452
import GoldbachCircleMethodCentralPurePrimeWitnessTransferV18445

/-!
# Goldbach V1.8.453: central L2 correction-to-witness transfer

The central L2 correction moment is converted into the aggregate correction
budget consumed by the already verified pure-prime witness transfer.  This
replaces the old direct aggregate-error assumption by a literal, finite,
factored energy budget.

The active residual budget and the analytic bound on the new energy product
remain explicit premises.  Hence the conclusion is conditional and the
top-level proof status remains `NO_PROOF`.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodCentralL2CorrectionWitnessTransferV18453

open GoldbachCircleMethodActiveResidualExactDecompositionV18251
open GoldbachCircleMethodAdjustedCorrectionL2CompositionV18451
open GoldbachCircleMethodCanonicalCentralAdjustedPositiveV18403
open GoldbachCircleMethodCanonicalCentralSourceTransferV18404
open GoldbachCircleMethodCentralAdjustedCorrectionL2MomentV18452
open GoldbachCircleMethodCentralPurePrimeWitnessTransferV18445
open GoldbachCircleMethodStructurallyAdmissibleActiveSlotV18258

/-- Cauchy--Schwarz over the central target sweep, followed by the exact
two-level correction-energy bound. -/
theorem central_adjusted_error_target_sum_abs_sq_le_factored_energy
    (m : ℕ) (rho b : ℝ)
    (e : StructurallyAdmissibleActiveSlot
      ⌊(((8 * m : ℕ) : ℝ)^rho)^2⌋₊) :
    |centralAdjustedCenteredErrorTargetSum m rho b e| ^ 2 ≤
      (2 * m + 1 : ℕ) *
        (adjustedSlotEnergyProductSourceSum (8 * m) rho b e.val *
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
    _ ≤ (2 * m + 1 : ℕ) *
        centralAdjustedCorrectionEnergy m rho b e := by
      simp only [Finset.card_range]
      exact mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum (fun i _hi => hpoint i)) (by positivity)
    _ ≤ (2 * m + 1 : ℕ) *
        (adjustedSlotEnergyProductSourceSum (8 * m) rho b e.val *
          centralAdjustedPartnerEnergy m rho b e) := by
      exact mul_le_mul_of_nonneg_left
        (central_adjusted_correction_energy_le_factored_energy m rho b e)
        (by positivity)

/-- An explicit factored L2 budget yields the old linear aggregate reserve. -/
theorem central_adjusted_error_target_sum_abs_lt_of_l2_budget
    (m : ℕ) (hm : 1 ≤ m) (rho b : ℝ)
    (e : StructurallyAdmissibleActiveSlot
      ⌊(((8 * m : ℕ) : ℝ)^rho)^2⌋₊)
    (henergy :
      (2 * m + 1 : ℕ) *
          (adjustedSlotEnergyProductSourceSum (8 * m) rho b e.val *
            centralAdjustedPartnerEnergy m rho b e) <
        (((8 * m : ℕ) : ℝ) ^ 2 / 2048) ^ 2) :
    |centralAdjustedCenteredErrorTargetSum m rho b e| <
      ((8 * m : ℕ) : ℝ) ^ 2 / 2048 := by
  have hsq :=
    (central_adjusted_error_target_sum_abs_sq_le_factored_energy
      m rho b e).trans_lt henergy
  have htarget : 0 < ((8 * m : ℕ) : ℝ) ^ 2 / 2048 := by
    have hmR : 0 < (m : ℝ) := by exact_mod_cast Nat.zero_lt_of_lt hm
    positivity
  nlinarith [sq_nonneg |centralAdjustedCenteredErrorTargetSum m rho b e|]

/-- Pure-prime witness transfer with the centered correction supplied by the
new factored L2 interface.  The theorem still assumes the active-residual
aggregate budget and the external analytic energy estimate. -/
theorem eventual_exists_goldbach_central_target_of_l2_centered_budget :
    ∃ m₀ : ℕ, ∀ {K : ℕ} [NeZero K],
      ∀ (m : ℕ), m₀ ≤ m →
      ∀ (rho b : ℝ),
      ∀ (hR2 : 2 ≤ ((8 * m : ℕ) : ℝ) ^ rho),
      ∀ (e : StructurallyAdmissibleActiveSlot
        ⌊(((8 * m : ℕ) : ℝ) ^ rho) ^ 2⌋₊),
      (∀ q : GoldbachCircleMethodBoundedConductorReindexV18117.PositiveLevel
        ⌊(((8 * m : ℕ) : ℝ) ^ rho) ^ 2⌋₊, q.val ∣ K) →
      0 < rho → rho ≤ (1 : ℝ) / 10000 →
      GoldbachCircleMethodResidualScaleAdmissionV18196.blockThreshold rho ≤ 8 * m →
      0 ≤ b → b ≤ 1 →
      1 < ((8 * m : ℕ) : ℝ) ^ rho →
      |centralActiveResidualTargetSum m rho hR2 b e| <
        ((8 * m : ℕ) : ℝ) ^ 2 / 256 →
      (2 * m + 1 : ℕ) *
          (adjustedSlotEnergyProductSourceSum (8 * m) rho b e.val *
            centralAdjustedPartnerEnergy m rho b e) <
        (((8 * m : ℕ) : ℝ) ^ 2 / 2048) ^ 2 →
      ∃ i ∈ Finset.range (2 * m + 1),
        GoldbachPurePrimeAdequacyV15.GoldbachAt (centralTargetNat m i) := by
  obtain ⟨m₀, hbase⟩ :=
    eventual_exists_goldbach_central_target_of_separate_budgets
  refine ⟨max m₀ 1, ?_⟩
  intro K hKinst m hm rho b hR2 e hK hrho hrhoUpper hScale hb hb1 hR
    hResidual hEnergy
  have hm₀ : m₀ ≤ m := (le_max_left m₀ 1).trans hm
  have hmOne : 1 ≤ m := (le_max_right m₀ 1).trans hm
  have hCentered := central_adjusted_error_target_sum_abs_lt_of_l2_budget
    m hmOne rho b e hEnergy
  exact hbase m hm₀ rho b hR2 e hK hrho hrhoUpper hScale hb hb1 hR
    hResidual hCentered

end GoldbachCircleMethodCentralL2CorrectionWitnessTransferV18453
