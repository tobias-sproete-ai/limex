import GoldbachCircleMethodCentralEulerPolynomialSourceV18442

/-!
# Goldbach V1.8.443: quantitative central source reserve

The strict adjusted-source reserve `B^2/224` and the two already certified
error budgets `B^2/256` and `B^2/2048` leave the exact positive margin
`B^2/14336`.  This module retains that margin instead of collapsing it to
mere positivity.

The theorem is a deterministic recombination seam.  It does not supply the
analytic error estimates and does not yet compare the source reserve with the
prime-power defect.  Hence `proof_status = NO_PROOF` remains mandatory.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodCentralQuantitativeSourceReserveV18443

open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodCanonicalCentralAdjustedPositiveV18403
open GoldbachCircleMethodCanonicalCentralSourceTransferV18404
open GoldbachCircleMethodLogCutoffPresieveBindingV18120
open GoldbachCircleMethodStructurallyAdmissibleActiveSlotV18258

/-- The exact unused fraction of the central reserve after the two separate
error allocations is `1/14336 = 1/224 - 1/256 - 1/2048`. -/
theorem central_block_source_target_sum_gt_one_over_14336_of_separate_budgets
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
    ((8 * m : ℕ) : ℝ) ^ 2 / 14336 <
      centralBlockSourceTargetSum m := by
  have hadjusted :=
    admitted_central_adjusted_source_target_sum_gt_one_over_224
      m hm rho b e hK hrho hrhoUpper hScale hb hb1 hR
  have hResidualLower := (abs_lt.mp hResidual).1
  have hCenteredLower := (abs_lt.mp hCentered).1
  rw [central_block_source_target_sum_eq_adjusted_add_errors
    m rho hR2 b e]
  nlinarith

end GoldbachCircleMethodCentralQuantitativeSourceReserveV18443
