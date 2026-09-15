import GoldbachCircleMethodUniformModelReserveCubicScaleV18639
import GoldbachCircleMethodOriginalMaskCountermodelBindingV1882

/-!
# V1.8.640: support-sensitive energy bound for the actual Major-operator error

The V1.8.634 envelope was integrated over the whole normalized circle even
though the actual Major-operator error is identically zero off the unchanged
Major mask.  This module retains the support measure and then substitutes the
already kernel-checked coarse measure bound.

The local Major approximation remains an explicit premise.  No inhabitant of
that analytic premise, exceptional-set decay, exception-set emptiness, or
Goldbach theorem is supplied.

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
open GoldbachCircleMethodTwoScaleIntegralPartitionV1831
open GoldbachCircleMethodTwoScaleEvenBlockDefectReserveV1833
open GoldbachCircleMethodDiscreteMainKernelV1852
open GoldbachCircleMethodSignedMagnitudeIdentityV18628
open GoldbachCircleMethodMajorOperatorErrorBesselV18633
open GoldbachCircleMethodMajorOperatorErrorEnergyV18634
open GoldbachCircleMethodOriginalMaskCountermodelBindingV1882
open GoldbachCircleMethodActualOvershootTwoChannelV18631
open GoldbachCircleMethodRealApproximationMinorAdapterV1873
open GoldbachCircleMethodChebyshevEnergyBudgetV1889
open GoldbachCircleMethodActualMinorFullEnergyTransferV18637
open GoldbachCircleMethodActualChannelProjectBudgetV18638
open GoldbachCircleMethodUniformModelReserveCubicScaleV18639

namespace GoldbachCircleMethodMajorOperatorErrorSupportMassV18640

/-- The exact Major-error energy only pays for the measure of the unchanged
Major mask, because the error function vanishes on its complement. -/
theorem majorOperatorErrorEnergy_le_envelope_sq_mul_measure
    (M P R : ℕ) (hscale : 2 * P * R < M) (ε : ℝ) (hε : 0 ≤ ε)
    (happrox : ∀ i : ReducedRationalIndex R,
      ∀ x ∈ Metric.closedBall (majorArcCenter i) (twoScaleArcRadius M P i),
        ‖exponentialSum M.succ x -
          (((ArithmeticFunction.moebius i.val.1 : ℤ) : ℂ) /
            (Nat.totient i.val.1 : ℂ)) *
              discreteMainPolynomial M (x - majorArcCenter i)‖ ≤ ε) :
    majorOperatorErrorEnergy M P R ≤
      (majorOperatorErrorEnvelope M ε) ^ 2 *
        haarAddCircle.real (twoScaleMajorMask M P R) := by
  let E : ℝ := majorOperatorErrorEnvelope M ε
  have hErr : Integrable
      (fun x : UnitAddCircle => ‖majorOperatorErrorFunction M P R x‖ ^ 2)
      haarAddCircle :=
    (majorOperatorErrorFunction_memLp_two M P R).integrable_norm_pow'
  have hConst : Integrable (fun _x : UnitAddCircle => E ^ 2) haarAddCircle :=
    integrable_const (E ^ 2)
  have hE : 0 ≤ E := by
    unfold E majorOperatorErrorEnvelope
    positivity
  unfold majorOperatorErrorEnergy
  calc
    _ = ∫ x in twoScaleMajorMask M P R,
        ‖majorOperatorErrorFunction M P R x‖ ^ 2 ∂haarAddCircle := by
      rw [← integral_indicator (twoScaleMajorMask_measurable M P R)]
      apply integral_congr_ae
      filter_upwards [] with x
      by_cases hx : x ∈ twoScaleMajorMask M P R
      · simp [hx]
      · rw [Set.indicator_of_notMem hx,
          majorOperatorErrorFunction_eq_zero_of_not_mem M P R x hx]
        simp
    _ ≤ ∫ _x in twoScaleMajorMask M P R, E ^ 2 ∂haarAddCircle := by
      apply setIntegral_mono_on hErr.integrableOn hConst.integrableOn
        (twoScaleMajorMask_measurable M P R)
      intro x _hx
      have h := majorOperatorErrorFunction_norm_le_envelope
        M P R hscale ε hε happrox x
      have hnorm := norm_nonneg (majorOperatorErrorFunction M P R x)
      nlinarith
    _ = E ^ 2 * haarAddCircle.real (twoScaleMajorMask M P R) := by
      rw [setIntegral_const]
      simp
      ring
    _ = _ := by rfl

/-- Substitution of the already proved coarse finite-union mass estimate. -/
theorem majorOperatorErrorEnergy_le_support_budget
    (M P R : ℕ) (hR : 1 ≤ R) (hscale : 2 * P * R < M)
    (ε : ℝ) (hε : 0 ≤ ε)
    (happrox : ∀ i : ReducedRationalIndex R,
      ∀ x ∈ Metric.closedBall (majorArcCenter i) (twoScaleArcRadius M P i),
        ‖exponentialSum M.succ x -
          (((ArithmeticFunction.moebius i.val.1 : ℤ) : ℂ) /
            (Nat.totient i.val.1 : ℂ)) *
              discreteMainPolynomial M (x - majorArcCenter i)‖ ≤ ε) :
    majorOperatorErrorEnergy M P R ≤
      (majorOperatorErrorEnvelope M ε) ^ 2 *
        (2 * (P : ℝ) * (R : ℝ) ^ 2 / (M : ℝ)) := by
  have hEnergy := majorOperatorErrorEnergy_le_envelope_sq_mul_measure
    M P R hscale ε hε happrox
  have hMP : 2 * P < M := by
    calc
      2 * P = 2 * P * 1 := by ring
      _ ≤ 2 * P * R := Nat.mul_le_mul_left (2 * P) hR
      _ < M := hscale
  have hMass := original_major_measure_le M P R hMP
  exact hEnergy.trans
    (mul_le_mul_of_nonneg_left hMass (sq_nonneg (majorOperatorErrorEnvelope M ε)))

/-- The exact two-channel budget with the genuine Major-support measure retained.
The local Major approximation and the Vaughan input remain explicit. -/
theorem actualChannelBudget_le_support_sensitive_project_budget
    (C ε : ℝ) (hC : 0 ≤ C) (hV : RealVaughanEstimate C)
    (M P R : ℕ) (s : Finset ℕ) (hM : 3 ≤ M)
    (hP : 0 < P) (hPM : P ≤ M) (hR : 1 ≤ R)
    (hscale : 2 * P * R < M) (hε : 0 ≤ ε)
    (happrox : ∀ i : ReducedRationalIndex R,
      ∀ x ∈ Metric.closedBall (majorArcCenter i) (twoScaleArcRadius M P i),
        ‖exponentialSum M.succ x -
          (((ArithmeticFunction.moebius i.val.1 : ℤ) : ℂ) /
            (Nat.totient i.val.1 : ℂ)) *
              discreteMainPolynomial M (x - majorArcCenter i)‖ ≤ ε) :
    2 * operatorApproximationSquaredMoment M P R s +
        2 * squareEnergy s (twoScaleMinorIntegralReal M P R) ≤
      2 * ((majorOperatorErrorEnvelope M ε) ^ 2 *
        (2 * (P : ℝ) * (R : ℝ) ^ 2 / (M : ℝ))) +
        2 * chebyshevFourthBudget M P R C := by
  have hBase := actualChannelBudget_le_exactBesselEnergies
    M P R s hR hscale
  have hMajor := majorOperatorErrorEnergy_le_support_budget
    M P R hR hscale ε hε happrox
  have hMinor := minorFourthMoment_le_chebyshev_budget
    C hC hV M P R hM hP hPM (by omega)
  linarith

/-- The support-sensitive exception budget at the inhabited cubic model scale.
This removes the spurious whole-circle Major-energy payment but leaves both
analytic source inputs visibly open. -/
theorem exception_card_mul_threshold_sq_le_support_budget_cubic_scale
    (C ε : ℝ) (hC : 0 ≤ C) (hV : RealVaughanEstimate C)
    (M R : ℕ) (hM : 32 ≤ M) (hR : 1 ≤ R)
    (hcubic : 16 * R ^ 3 < M) (hε : 0 ≤ ε)
    (hScale : 112 * (Real.log (M : ℝ)) ^ 2 ≤ Real.sqrt (M : ℝ))
    (happrox : ∀ i : ReducedRationalIndex R,
      ∀ x ∈ Metric.closedBall (majorArcCenter i)
          (twoScaleArcRadius M (cubicModelScale R) i),
        ‖exponentialSum M.succ x -
          (((ArithmeticFunction.moebius i.val.1 : ℤ) : ℂ) /
            (Nat.totient i.val.1 : ℂ)) *
              discreteMainPolynomial M (x - majorArcCenter i)‖ ≤ ε) :
    ((((evenTargetBlock M).filter (fun N => ¬ GoldbachAt N)).card : ℝ) *
        ((M : ℝ) / 28) ^ 2) ≤
      2 * ((majorOperatorErrorEnvelope M ε) ^ 2 *
        (2 * (cubicModelScale R : ℝ) * (R : ℝ) ^ 2 / (M : ℝ))) +
        2 * chebyshevFourthBudget M (cubicModelScale R) R C := by
  have hBase :=
    exception_card_mul_threshold_sq_le_operatorError_add_minorEnergy
      M (cubicModelScale R) R hScale
        (uniform_discrete_model_reserve_cubic_scale M R hM hR hcubic)
  exact hBase.trans
    (actualChannelBudget_le_support_sensitive_project_budget
      C ε hC hV M (cubicModelScale R) R (evenTargetBlock M)
      (by omega) (cubicModelScale_pos R hR)
      (cubicModelScale_le_scale M R hR hcubic) hR
      (cubicModelScale_window M R hcubic) hε happrox)

end GoldbachCircleMethodMajorOperatorErrorSupportMassV18640
