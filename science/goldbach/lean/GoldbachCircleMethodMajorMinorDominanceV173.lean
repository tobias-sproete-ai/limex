import GoldbachCircleMethodMajorMinorPartitionV172

/-!
# Concrete major/minor dominance reduction, V1.7.3 candidate

This module consumes the actual V1.7.2 set integrals. It proves that the
pointwise inequality

`explicit defect threshold < re(major integral) - ‖minor integral‖`

forces the V1.6.2 von Mangoldt dominance condition and hence `GoldbachAt N`.
No instance of that analytic inequality is constructed or asserted.
-/

set_option autoImplicit false

namespace GoldbachCircleMethodMajorMinorDominanceV173

open GoldbachCircleMethodMajorMinorPartitionV172
open GoldbachMainTermDominanceBridgeV162
open GoldbachVonMangoldtDecompositionV16

/--
The concrete major/minor lower bound implies the exact von Mangoldt pair sum
exceeds the V1.6.2 defect threshold. The only estimate used internally is the
kernel theorem `-‖z‖ ≤ re z` for the complex minor-arc integral.
-/
theorem major_minor_pointwise_bound_implies_vonMangoldt_dominance
    (p : ArcParameters)
    (hBound :
      4 * Real.sqrt (p.N : Real) * (Real.log (p.N : Real)) ^ 2 <
        (∫ x in majorArcs p,
          pairFourierIntegrand p.N x ∂AddCircle.haarAddCircle).re -
        ‖∫ x in minorArcs p,
          pairFourierIntegrand p.N x ∂AddCircle.haarAddCircle‖) :
    4 * Real.sqrt (p.N : Real) * (Real.log (p.N : Real)) ^ 2 <
      vonMangoldtPairSum p.N := by
  let majorIntegral : Complex :=
    ∫ x in majorArcs p,
      pairFourierIntegrand p.N x ∂AddCircle.haarAddCircle
  let minorIntegral : Complex :=
    ∫ x in minorArcs p,
      pairFourierIntegrand p.N x ∂AddCircle.haarAddCircle
  have hPartition : majorIntegral + minorIntegral =
      (vonMangoldtPairSum p.N : Complex) := by
    exact major_minor_integral_partition p
  have hRealPartition : majorIntegral.re + minorIntegral.re =
      vonMangoldtPairSum p.N := by
    have h := congrArg Complex.re hPartition
    simpa using h
  have hMinorLower : -‖minorIntegral‖ ≤ minorIntegral.re := by
    exact neg_le_of_abs_le (RCLike.abs_re_le_norm minorIntegral)
  change 4 * Real.sqrt (p.N : Real) * (Real.log (p.N : Real)) ^ 2 <
    majorIntegral.re - ‖minorIntegral‖ at hBound
  linarith

/--
The same concrete pointwise bound implies `GoldbachAt p.N` through the
existing V1.6.2 bridge. This is a conditional reduction, not an analytic
estimate or a proof that the hypothesis is inhabited.
-/
theorem major_minor_pointwise_bound_implies_goldbachAt
    (p : ArcParameters)
    (hBound :
      4 * Real.sqrt (p.N : Real) * (Real.log (p.N : Real)) ^ 2 <
        (∫ x in majorArcs p,
          pairFourierIntegrand p.N x ∂AddCircle.haarAddCircle).re -
        ‖∫ x in minorArcs p,
          pairFourierIntegrand p.N x ∂AddCircle.haarAddCircle‖) :
    GoldbachPurePrimeAdequacyV15.GoldbachAt p.N := by
  exact explicit_four_sqrt_log_sq_dominance_implies_goldbachAt
    (Nat.succ_le_iff.mpr p.N_pos)
    (major_minor_pointwise_bound_implies_vonMangoldt_dominance p hBound)

end GoldbachCircleMethodMajorMinorDominanceV173
