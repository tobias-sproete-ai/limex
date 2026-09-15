import GoldbachCircleMethodHybridCenteredCentralMomentV18505
import GoldbachCircleMethodCentralPurePrimeWitnessTransferV18445
import GoldbachCircleMethodCentralLiteralSourceScaleClosedV18415

/-!
# Goldbach V1.8.506: hybrid-centered witness transfer

The corrected hybrid source energy reaches the already kernel-checked
pure-prime witness gate.  The principal `Lambda - 1` discrepancy remains
intact.  The residual estimate and the hybrid energy inequality are explicit
analytic premises, so this module remains a conditional reduction and does
not prove Goldbach.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodHybridCenteredWitnessTransferV18506

open GoldbachCircleMethodActiveResidualExactDecompositionV18251
open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodCanonicalCentralAdjustedPositiveV18403
open GoldbachCircleMethodCanonicalCentralSourceTransferV18404
open GoldbachCircleMethodCentralLiteralSourceScaleClosedV18415
open GoldbachCircleMethodCentralPurePrimeWitnessTransferV18445
open GoldbachCircleMethodHybridCenteredCentralMomentV18505
open GoldbachCircleMethodLogCutoffPresieveBindingV18120
open GoldbachCircleMethodResidualScaleAdmissionV18196
open GoldbachCircleMethodStructurallyAdmissibleActiveSlotV18258

/-- The hybrid squared-energy budget implies the linear centered-error
reserve consumed by the pure-prime witness transfer. -/
theorem central_adjusted_error_target_sum_abs_lt_of_hybridCentered_budget
    (m : ℕ) (hm : 1 ≤ m) (rho b : ℝ)
    (e : StructurallyAdmissibleActiveSlot
      ⌊(((8 * m : ℕ) : ℝ) ^ rho) ^ 2⌋₊)
    (hH : 1 ≤ ((8 * m : ℕ) : ℝ) /
      (((8 * m : ℕ) : ℝ) ^ rho) ^ 4)
    (hb : 0 ≤ b)
    (henergy :
      (2 * m + 1 : ℕ) *
          (3 * hybridCenteredSourceBudget (8 * m) rho b e.val *
            GoldbachCircleMethodCentralAdjustedCorrectionL2MomentV18452.centralAdjustedPartnerEnergy
              m rho b e) <
        (((8 * m : ℕ) : ℝ) ^ 2 / 2048) ^ 2) :
    |centralAdjustedCenteredErrorTargetSum m rho b e| <
      ((8 * m : ℕ) : ℝ) ^ 2 / 2048 := by
  have hsq :=
    (central_adjusted_error_target_sum_abs_sq_le_hybridCentered
      m rho b e hH hb).trans_lt henergy
  have htarget : 0 < ((8 * m : ℕ) : ℝ) ^ 2 / 2048 := by
    have hmR : 0 < (m : ℝ) := by exact_mod_cast Nat.zero_lt_of_lt hm
    positivity
  nlinarith [sq_nonneg |centralAdjustedCenteredErrorTargetSum m rho b e|]

/-- Eventual pure-prime witness transfer through the repaired hybrid source
split.  No analytic premise is inhabited in this theorem. -/
theorem eventual_exists_goldbach_central_target_of_hybridCentered_budget :
    ∃ m₀ : ℕ, ∀ {K : ℕ} [NeZero K],
      ∀ (m : ℕ), m₀ ≤ m →
      ∀ (rho b : ℝ),
      ∀ (hR2 : 2 ≤ ((8 * m : ℕ) : ℝ) ^ rho),
      ∀ (e : StructurallyAdmissibleActiveSlot
        ⌊(((8 * m : ℕ) : ℝ) ^ rho) ^ 2⌋₊),
      (∀ q : PositiveLevel ⌊(((8 * m : ℕ) : ℝ) ^ rho) ^ 2⌋₊,
        q.val ∣ K) →
      0 < rho → rho ≤ (1 : ℝ) / 10000 →
      blockThreshold rho ≤ 8 * m →
      0 ≤ b → b ≤ 1 →
      1 < ((8 * m : ℕ) : ℝ) ^ rho →
      |centralActiveResidualTargetSum m rho hR2 b e| <
        ((8 * m : ℕ) : ℝ) ^ 2 / 256 →
      (2 * m + 1 : ℕ) *
          (3 * hybridCenteredSourceBudget (8 * m) rho b e.val *
            GoldbachCircleMethodCentralAdjustedCorrectionL2MomentV18452.centralAdjustedPartnerEnergy
              m rho b e) <
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
  have hH := admitted_canonical_window_scale_one
    rho hrho hrhoUpper (8 * m) hScale
  have hCentered :=
    central_adjusted_error_target_sum_abs_lt_of_hybridCentered_budget
      m hmOne rho b e hH hb hEnergy
  exact hbase m hm₀ rho b hR2 e hK hrho hrhoUpper hScale hb hb1 hR
    hResidual hCentered

end GoldbachCircleMethodHybridCenteredWitnessTransferV18506
