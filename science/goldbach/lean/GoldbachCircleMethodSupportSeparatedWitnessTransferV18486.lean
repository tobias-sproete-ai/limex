import GoldbachCircleMethodSupportSeparatedCentralMomentV18485
import GoldbachCircleMethodCentralPurePrimeWitnessTransferV18445
import GoldbachCircleMethodCentralLiteralSourceScaleClosedV18415

/-!
# Goldbach V1.8.486: support-separated witness transfer

The support-separated central moment is connected to the already verified
pure-prime witness transfer.  The canonical window condition is discharged
from the admitted block scale, so the only new premise is the explicit
three-channel analytic energy budget.

This is a conditional reduction.  It does not inhabit the analytic budget
and therefore does not prove Goldbach.  `proof_status = NO_PROOF` remains
mandatory.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodSupportSeparatedWitnessTransferV18486

open GoldbachCircleMethodActiveResidualExactDecompositionV18251
open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodCanonicalCentralAdjustedPositiveV18403
open GoldbachCircleMethodCanonicalCentralSourceTransferV18404
open GoldbachCircleMethodCentralAdjustedCorrectionL2MomentV18452
open GoldbachCircleMethodCentralLiteralSourceScaleClosedV18415
open GoldbachCircleMethodCentralPurePrimeWitnessTransferV18445
open GoldbachCircleMethodLogCutoffPresieveBindingV18120
open GoldbachCircleMethodResidualScaleAdmissionV18196
open GoldbachCircleMethodStructurallyAdmissibleActiveSlotV18258
open GoldbachCircleMethodSupportSeparatedCentralMomentV18485
open GoldbachCircleMethodSupportSeparatedSourceBudgetV18484

/-- An explicit support-separated squared-energy budget implies the linear
aggregate centered-correction reserve consumed by the witness transfer. -/
theorem central_adjusted_error_target_sum_abs_lt_of_supportSeparated_budget
    (m : ℕ) (hm : 1 ≤ m) (rho b : ℝ)
    (e : StructurallyAdmissibleActiveSlot
      ⌊(((8 * m : ℕ) : ℝ) ^ rho) ^ 2⌋₊)
    (hH : 1 ≤ ((8 * m : ℕ) : ℝ) /
      (((8 * m : ℕ) : ℝ) ^ rho) ^ 4)
    (hb : 0 ≤ b)
    (henergy :
      (2 * m + 1 : ℕ) *
          (3 * supportSeparatedSourceBudget (8 * m) rho b e.val *
            centralAdjustedPartnerEnergy m rho b e) <
        (((8 * m : ℕ) : ℝ) ^ 2 / 2048) ^ 2) :
    |centralAdjustedCenteredErrorTargetSum m rho b e| <
      ((8 * m : ℕ) : ℝ) ^ 2 / 2048 := by
  have hsq :=
    (central_adjusted_error_target_sum_abs_sq_le_supportSeparated
      m rho b e hH hb).trans_lt henergy
  have htarget : 0 < ((8 * m : ℕ) : ℝ) ^ 2 / 2048 := by
    have hmR : 0 < (m : ℝ) := by exact_mod_cast Nat.zero_lt_of_lt hm
    positivity
  nlinarith [sq_nonneg |centralAdjustedCenteredErrorTargetSum m rho b e|]

/-- Eventual pure-prime witness transfer with sparse correction supports kept
separate.  The active residual and the three-channel energy inequality remain
explicit analytic premises. -/
theorem eventual_exists_goldbach_central_target_of_supportSeparated_budget :
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
          (3 * supportSeparatedSourceBudget (8 * m) rho b e.val *
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
  have hH := admitted_canonical_window_scale_one
    rho hrho hrhoUpper (8 * m) hScale
  have hCentered :=
    central_adjusted_error_target_sum_abs_lt_of_supportSeparated_budget
      m hmOne rho b e hH hb hEnergy
  exact hbase m hm₀ rho b hR2 e hK hrho hrhoUpper hScale hb hb1 hR
    hResidual hCentered

end GoldbachCircleMethodSupportSeparatedWitnessTransferV18486
