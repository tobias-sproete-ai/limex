import GoldbachPrimePowerDefectBoundV161

/-!
# Conditional main-term dominance bridge, V1.6.2 candidate

This module proves only that an explicit lower bound which dominates the
kernel-checked prime-power defect forces a genuine prime-pair witness.
It does not prove that lower bound.
-/

set_option autoImplicit false

open scoped BigOperators ArithmeticFunction.vonMangoldt Chebyshev

namespace GoldbachMainTermDominanceBridgeV162

open GoldbachPurePrimeAdequacyV15
open GoldbachVonMangoldtDecompositionV16
open GoldbachPrimePowerDefectBoundV161

/-- Exact conditional bridge before inserting a quantitative defect bound. -/
theorem vonMangoldtPairSum_gt_defect_implies_goldbachAt
    {N : Nat}
    (hDominance : primePowerDefect N < vonMangoldtPairSum N) :
    GoldbachAt N := by
  have hDecomposition :=
    vonMangoldtPairSum_eq_purePrimeSum_add_primePowerDefect N
  have hPurePositive : 0 < purePrimeSum N := by
    linarith
  exact (purePrimeSum_pos_iff_strictGoldbach N).mp hPurePositive

/-- Concrete conditional bridge using V1.6.1's explicit defect ceiling.
The hypothesis is the remaining open analytic lower-bound obligation. -/
theorem explicit_four_sqrt_log_sq_dominance_implies_goldbachAt
    {N : Nat} (hN : 1 ≤ N)
    (hDominance :
      4 * Real.sqrt (N : Real) * (Real.log (N : Real)) ^ 2 <
        vonMangoldtPairSum N) :
    GoldbachAt N := by
  have hDefect := primePowerDefect_le_four_sqrt_mul_log_sq hN
  exact vonMangoldtPairSum_gt_defect_implies_goldbachAt
    (lt_of_le_of_lt hDefect hDominance)

end GoldbachMainTermDominanceBridgeV162
