import GoldbachCircleMethodCanonicalCentralCenteredErrorAggregateV18405
import GoldbachCircleMethodCanonicalCentralActiveResidualV18406

/-!
# Goldbach V1.8.407: canonical central source recombination

The two separately audited aggregate error budgets are recombined below the
strict `B^2 / 224` central adjusted-source reserve.  This file contains only
the exact triangle-inequality seam and the transfer to one positive literal
von-Mangoldt source target.

No analytic premise is manufactured here.  In particular, the V1.8.405
centered-correction inputs and the V1.8.406 Vaughan/moment power budget remain
upstream obligations.  The terminal witness is not yet a pure-prime witness.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodCanonicalCentralSourceRecombinationV18407

open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodCanonicalCentralAdjustedPositiveV18403
open GoldbachCircleMethodCanonicalCentralSourceTransferV18404
open GoldbachCircleMethodLogCutoffPresieveBindingV18120
open GoldbachCircleMethodStructurallyAdmissibleActiveSlotV18258

/-- The two strict error allocations fit strictly below the central reserve.
The assumption `1 <= m` is essential because the claimed strict comparison is
false at the degenerate zero block. -/
theorem central_combined_errors_lt_one_over_224
    (m : ℕ) (hm : 1 ≤ m) (rho b : ℝ)
    (hR2 : 2 ≤ ((8 * m : ℕ) : ℝ) ^ rho)
    (e : StructurallyAdmissibleActiveSlot
      ⌊(((8 * m : ℕ) : ℝ) ^ rho) ^ 2⌋₊)
    (hResidual :
      |centralActiveResidualTargetSum m rho hR2 b e| <
        ((8 * m : ℕ) : ℝ) ^ 2 / 256)
    (hCentered :
      |centralAdjustedCenteredErrorTargetSum m rho b e| <
        ((8 * m : ℕ) : ℝ) ^ 2 / 2048) :
    |centralActiveResidualTargetSum m rho hR2 b e +
        centralAdjustedCenteredErrorTargetSum m rho b e| <
      ((8 * m : ℕ) : ℝ) ^ 2 / 224 := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hm)
  have hBsq : 0 < ((8 * m : ℕ) : ℝ) ^ 2 := by
    push_cast
    positivity
  calc
    |centralActiveResidualTargetSum m rho hR2 b e +
        centralAdjustedCenteredErrorTargetSum m rho b e| ≤
      |centralActiveResidualTargetSum m rho hR2 b e| +
        |centralAdjustedCenteredErrorTargetSum m rho b e| := abs_add_le _ _
    _ < ((8 * m : ℕ) : ℝ) ^ 2 / 256 +
          ((8 * m : ℕ) : ℝ) ^ 2 / 2048 := add_lt_add hResidual hCentered
    _ < ((8 * m : ℕ) : ℝ) ^ 2 / 224 := by nlinarith

/-- Exact source positivity after separate active-residual and centered-error
budgets have been proved. -/
theorem admitted_central_block_source_target_sum_pos_of_separate_budgets
    {K : ℕ} [NeZero K]
    (m : ℕ) (hm : 1 ≤ m) (rho b : ℝ)
    (hR2 : 2 ≤ ((8 * m : ℕ) : ℝ) ^ rho)
    (e : StructurallyAdmissibleActiveSlot
      ⌊(((8 * m : ℕ) : ℝ) ^ rho) ^ 2⌋₊)
    (hK : ∀ q : PositiveLevel ⌊(((8 * m : ℕ) : ℝ) ^ rho) ^ 2⌋₊,
      q.val ∣ K)
    (hrho : 0 < rho) (hrhoUpper : rho ≤ (1 : ℝ) / 10000)
    (hScale : GoldbachCircleMethodResidualScaleAdmissionV18196.blockThreshold rho ≤ 8 * m)
    (hb : 0 ≤ b) (hb1 : b ≤ 1)
    (hR : 1 < ((8 * m : ℕ) : ℝ) ^ rho)
    (hResidual :
      |centralActiveResidualTargetSum m rho hR2 b e| <
        ((8 * m : ℕ) : ℝ) ^ 2 / 256)
    (hCentered :
      |centralAdjustedCenteredErrorTargetSum m rho b e| <
        ((8 * m : ℕ) : ℝ) ^ 2 / 2048) :
    0 < centralBlockSourceTargetSum m := by
  apply admitted_central_block_source_target_sum_pos_of_error_absorption
    m hm rho b hR2 e hK hrho hrhoUpper hScale hb hb1 hR
  exact central_combined_errors_lt_one_over_224
    m hm rho b hR2 e hResidual hCentered

/-- Under the same explicit premises, the central sweep contains one positive
literal von-Mangoldt block convolution. -/
theorem exists_positive_central_block_source_target_of_separate_budgets
    {K : ℕ} [NeZero K]
    (m : ℕ) (hm : 1 ≤ m) (rho b : ℝ)
    (hR2 : 2 ≤ ((8 * m : ℕ) : ℝ) ^ rho)
    (e : StructurallyAdmissibleActiveSlot
      ⌊(((8 * m : ℕ) : ℝ) ^ rho) ^ 2⌋₊)
    (hK : ∀ q : PositiveLevel ⌊(((8 * m : ℕ) : ℝ) ^ rho) ^ 2⌋₊,
      q.val ∣ K)
    (hrho : 0 < rho) (hrhoUpper : rho ≤ (1 : ℝ) / 10000)
    (hScale : GoldbachCircleMethodResidualScaleAdmissionV18196.blockThreshold rho ≤ 8 * m)
    (hb : 0 ≤ b) (hb1 : b ≤ 1)
    (hR : 1 < ((8 * m : ℕ) : ℝ) ^ rho)
    (hResidual :
      |centralActiveResidualTargetSum m rho hR2 b e| <
        ((8 * m : ℕ) : ℝ) ^ 2 / 256)
    (hCentered :
      |centralAdjustedCenteredErrorTargetSum m rho b e| <
        ((8 * m : ℕ) : ℝ) ^ 2 / 2048) :
    ∃ i ∈ Finset.range (2 * m + 1),
      0 < (GoldbachCircleMethodActualResidualExactDecompositionV18225.canonicalBlockSourceAt
        (8 * m) ((centralTargetNat m i : ℕ) : ℤ)).re := by
  apply exists_positive_central_block_source_target m
  exact admitted_central_block_source_target_sum_pos_of_separate_budgets
    m hm rho b hR2 e hK hrho hrhoUpper hScale hb hb1 hR hResidual hCentered

end GoldbachCircleMethodCanonicalCentralSourceRecombinationV18407
