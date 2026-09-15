import GoldbachCircleMethodMajorMinorDominanceV173

/-!
# Real-part major/minor dominance reduction, V1.7.4 candidate

This module sharpens the sufficient V1.7.3 condition by replacing the norm of
the minor-arc integral with the absolute value of its real part. The resulting
condition is logically weaker because `|re z| ≤ ‖z‖`, while remaining wholly
conditional: no analytic instance of either bound is constructed.

The two principal results use the concrete V1.7.2 integrals and the exact
V1.7.2 partition. No generic dominance interface is introduced.
-/

set_option autoImplicit false

namespace GoldbachCircleMethodMajorMinorRealPartV174

open GoldbachCircleMethodMajorMinorPartitionV172
open GoldbachCircleMethodMajorMinorDominanceV173
open GoldbachMainTermDominanceBridgeV162
open GoldbachVonMangoldtDecompositionV16

/--
The concrete real-part bound implies that the von Mangoldt pair sum exceeds
the explicit V1.6.2 defect threshold.
-/
theorem major_minor_realpart_bound_implies_vonMangoldt_dominance
    (p : ArcParameters)
    (hBound :
      4 * Real.sqrt (p.N : Real) * (Real.log (p.N : Real)) ^ 2 <
        (∫ x in majorArcs p,
          pairFourierIntegrand p.N x ∂AddCircle.haarAddCircle).re -
        |(∫ x in minorArcs p,
          pairFourierIntegrand p.N x ∂AddCircle.haarAddCircle).re|) :
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
  have hMinorLower : -|minorIntegral.re| ≤ minorIntegral.re := by
    exact neg_abs_le minorIntegral.re
  change 4 * Real.sqrt (p.N : Real) * (Real.log (p.N : Real)) ^ 2 <
    majorIntegral.re - |minorIntegral.re| at hBound
  linarith

/--
The concrete real-part bound implies `GoldbachAt p.N` through the V1.6.2
defect bridge. This theorem does not supply the analytic bound.
-/
theorem major_minor_realpart_bound_implies_goldbachAt
    (p : ArcParameters)
    (hBound :
      4 * Real.sqrt (p.N : Real) * (Real.log (p.N : Real)) ^ 2 <
        (∫ x in majorArcs p,
          pairFourierIntegrand p.N x ∂AddCircle.haarAddCircle).re -
        |(∫ x in minorArcs p,
          pairFourierIntegrand p.N x ∂AddCircle.haarAddCircle).re|) :
    GoldbachPurePrimeAdequacyV15.GoldbachAt p.N := by
  exact explicit_four_sqrt_log_sq_dominance_implies_goldbachAt
    (Nat.succ_le_iff.mpr p.N_pos)
    (major_minor_realpart_bound_implies_vonMangoldt_dominance p hBound)

/--
The V1.7.3 norm condition implies the weaker V1.7.4 real-part condition.
-/
theorem norm_bound_implies_realpart_bound
    (p : ArcParameters)
    (hBound :
      4 * Real.sqrt (p.N : Real) * (Real.log (p.N : Real)) ^ 2 <
        (∫ x in majorArcs p,
          pairFourierIntegrand p.N x ∂AddCircle.haarAddCircle).re -
        ‖∫ x in minorArcs p,
          pairFourierIntegrand p.N x ∂AddCircle.haarAddCircle‖) :
    4 * Real.sqrt (p.N : Real) * (Real.log (p.N : Real)) ^ 2 <
      (∫ x in majorArcs p,
        pairFourierIntegrand p.N x ∂AddCircle.haarAddCircle).re -
      |(∫ x in minorArcs p,
        pairFourierIntegrand p.N x ∂AddCircle.haarAddCircle).re| := by
  let majorIntegral : Complex :=
    ∫ x in majorArcs p,
      pairFourierIntegrand p.N x ∂AddCircle.haarAddCircle
  let minorIntegral : Complex :=
    ∫ x in minorArcs p,
      pairFourierIntegrand p.N x ∂AddCircle.haarAddCircle
  have hAbsLeNorm : |minorIntegral.re| ≤ ‖minorIntegral‖ := by
    exact RCLike.abs_re_le_norm minorIntegral
  change 4 * Real.sqrt (p.N : Real) * (Real.log (p.N : Real)) ^ 2 <
    majorIntegral.re - ‖minorIntegral‖ at hBound
  change 4 * Real.sqrt (p.N : Real) * (Real.log (p.N : Real)) ^ 2 <
    majorIntegral.re - |minorIntegral.re|
  linarith

end GoldbachCircleMethodMajorMinorRealPartV174
