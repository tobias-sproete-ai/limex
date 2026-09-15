import GoldbachCircleMethodMajorOperatorErrorSupportMassV18640
import GoldbachCircleMethodPrefixBudgetAbsorptionV1870

/-!
# V1.8.641: inhabit the cubic-scale local Major approximation from prefix data

The local approximation parameter in V1.8.640 is no longer a free function.
At `R = logRadius K M` and `P = cubicModelScale R`, finite Abel summation turns
the existing full rational-prefix contract into the exact closed-arc estimate
needed by the support-sensitive Major-energy theorem.

`FullPrefixBound` and `RealVaughanEstimate` remain explicit analytic premises.
No inhabitant of either premise, exceptional-set decay, exception-set
emptiness, or Goldbach theorem is supplied.

`proof_status = NO_PROOF`.
-/
set_option autoImplicit false

open scoped BigOperators Classical
open MeasureTheory AddCircle
open GoldbachPurePrimeAdequacyV15
open GoldbachCircleMethodExceptionalTransferV1823
open GoldbachCircleMethodFourierIdentityV171
open GoldbachCircleMethodMajorMinorPartitionV172
open GoldbachCircleMethodTwoScaleMaskAdapterV1829
open GoldbachCircleMethodTwoScaleEvenBlockDefectReserveV1833
open GoldbachCircleMethodDiscreteMainKernelV1852
open GoldbachCircleMethodFiniteAbelAdapterV1863
open GoldbachCircleMethodCeilScaleEnvelopesV1864
open GoldbachCircleMethodUniformMajorPrefixReductionV1865
open GoldbachCircleMethodPrefixBudgetAbsorptionV1870
open GoldbachCircleMethodRealApproximationMinorAdapterV1873
open GoldbachCircleMethodChebyshevEnergyBudgetV1889
open GoldbachCircleMethodMajorOperatorErrorEnergyV18634
open GoldbachCircleMethodUniformModelReserveCubicScaleV18639
open GoldbachCircleMethodMajorOperatorErrorSupportMassV18640

namespace GoldbachCircleMethodCubicScalePrefixInhabitationV18641

/-- Exact finite-Abel envelope at the cubic model scale. -/
noncomputable def cubicPrefixArcEnvelope
    (K M : ℕ) (C c : ℝ) : ℝ :=
  (1 + 2 * Real.pi *
      (cubicModelScale (logRadius K M) : ℝ)) * prefixEnvelope M C c

theorem cubicPrefixArcEnvelope_nonneg
    (K M : ℕ) (C c : ℝ) (hC : 0 ≤ C) :
    0 ≤ cubicPrefixArcEnvelope K M C c := by
  unfold cubicPrefixArcEnvelope prefixEnvelope
  positivity

/-- The full prefix contract inhabits the literal local approximation required
on every original closed arc at the cubic scale. -/
theorem cubic_local_approximation_of_full_prefix
    (K M : ℕ) (C c : ℝ) (hM : 0 < M) (hC : 0 ≤ C)
    (hprefix : FullPrefixBound K M C c) :
    ∀ i : ReducedRationalIndex (logRadius K M),
      ∀ x ∈ Metric.closedBall (majorArcCenter i)
          (twoScaleArcRadius M (cubicModelScale (logRadius K M)) i),
        ‖exponentialSum M.succ x -
          (((ArithmeticFunction.moebius i.val.1 : ℤ) : ℂ) /
            (Nat.totient i.val.1 : ℂ)) *
              discreteMainPolynomial M (x - majorArcCenter i)‖ ≤
          cubicPrefixArcEnvelope K M C c := by
  intro i x hx
  exact original_arc_error_from_prefix
    M (cubicModelScale (logRadius K M)) (logRadius K M) hM i x
    (prefixEnvelope M C c) (by unfold prefixEnvelope; positivity) hx (hprefix i)

/-- The support-sensitive exceptional-set budget with the local approximation
premise replaced by the finite full-prefix contract. -/
theorem exception_card_mul_threshold_sq_le_cubic_prefix_budget
    (K : ℕ) (C c CV : ℝ) (hC : 0 ≤ C) (hCV : 0 ≤ CV)
    (hV : RealVaughanEstimate CV)
    (M : ℕ) (hM : 32 ≤ M) (hR : 1 ≤ logRadius K M)
    (hcubic : 16 * (logRadius K M) ^ 3 < M)
    (hScale : 112 * (Real.log (M : ℝ)) ^ 2 ≤ Real.sqrt (M : ℝ))
    (hprefix : FullPrefixBound K M C c) :
    ((((evenTargetBlock M).filter (fun N => ¬ GoldbachAt N)).card : ℝ) *
        ((M : ℝ) / 28) ^ 2) ≤
      2 * ((majorOperatorErrorEnvelope M
          (cubicPrefixArcEnvelope K M C c)) ^ 2 *
        (2 * (cubicModelScale (logRadius K M) : ℝ) *
          (logRadius K M : ℝ) ^ 2 / (M : ℝ))) +
        2 * chebyshevFourthBudget M
          (cubicModelScale (logRadius K M)) (logRadius K M) CV := by
  exact exception_card_mul_threshold_sq_le_support_budget_cubic_scale
    CV (cubicPrefixArcEnvelope K M C c) hCV hV M (logRadius K M)
    hM hR hcubic (cubicPrefixArcEnvelope_nonneg K M C c hC) hScale
    (cubic_local_approximation_of_full_prefix K M C c (by omega) hC hprefix)

end GoldbachCircleMethodCubicScalePrefixInhabitationV18641
