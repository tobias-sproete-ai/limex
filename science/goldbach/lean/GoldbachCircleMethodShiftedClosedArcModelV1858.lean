import GoldbachCircleMethodClosedArcCoordinatesV1857

/-! # V1.8.58: the shifted discrete model integrated on an actual closed arc.
No von-Mangoldt approximation or disjoint-union claim is made here.
-/
open MeasureTheory
open GoldbachCircleMethodDiscreteMainKernelV1852
open GoldbachCircleMethodDiscreteArcTailV1854
open GoldbachCircleMethodClosedArcCoordinatesV1857
open GoldbachCircleMethodComplexArcModelBindingV1856
open GoldbachCircleMethodSignedFullPrefixV1850

namespace GoldbachCircleMethodShiftedClosedArcModelV1858

attribute [local instance] Classical.propDecidable

theorem fourier_argument_add (n : ℤ) (x y : UnitAddCircle) :
    fourier n (x+y) = fourier n x * fourier n y := by
  simp only [fourier_apply, zsmul_add, AddCircle.toCircle_add, Circle.coe_mul]

noncomputable def shiftedArcModelIntegrand (M N : ℕ) (c : UnitAddCircle)
    (z : ℂ) (x : UnitAddCircle) : ℂ :=
  fourier (-(N : ℤ)) x * (z * discreteMainPolynomial M (x-c))^2

theorem shiftedArcModelIntegrand_centered (M N : ℕ) (c β : ℝ) (z : ℂ) :
    shiftedArcModelIntegrand M N (c : UnitAddCircle) z ((c+β : ℝ) : UnitAddCircle) =
      (z^2 * fourier (-(N : ℤ)) (c : UnitAddCircle)) * realMainIntegrand M N β := by
  simp only [shiftedArcModelIntegrand, realMainIntegrand, discreteMainIntegrand,
    QuotientAddGroup.mk_add, add_sub_cancel_left, fourier_argument_add]
  ring

theorem integral_shiftedArcModel_closedBall (M N : ℕ) (c t : ℝ) (z : ℂ)
    (ht0 : 0 ≤ t) (ht : t < 1/2) :
    (∫ x in Metric.closedBall (c : UnitAddCircle) t,
      shiftedArcModelIntegrand M N (c : UnitAddCircle) z x ∂AddCircle.haarAddCircle) =
        (z^2 * fourier (-(N : ℤ)) (c : UnitAddCircle)) * localDiscreteMainIntegral M N t := by
  rw [integral_closedBall_eq_centered_interval _ c t ht0 ht]
  simp_rw [shiftedArcModelIntegrand_centered]
  exact intervalIntegral.integral_const_mul _ _

theorem sum_unit_center_arc_models (M N q : ℕ) [NeZero q] (t : ℝ)
    (ht0 : 0 ≤ t) (ht : t < 1/2) :
    (∑ a : ZMod q, if IsUnit a then
      ∫ x in Metric.closedBall (((a.val : ℝ)/(q : ℝ) : ℝ) : UnitAddCircle) t,
        shiftedArcModelIntegrand M N (((a.val : ℝ)/(q : ℝ) : ℝ) : UnitAddCircle)
          (((ArithmeticFunction.moebius q : ℤ) : ℂ)/(Nat.totient q : ℂ)) x
            ∂AddCircle.haarAddCircle else 0) =
      complexMajorCoefficient N q * localDiscreteMainIntegral M N t := by
  classical
  let z : ℂ := ((ArithmeticFunction.moebius q : ℤ) : ℂ)/(Nat.totient q : ℂ)
  have hterm (a : ZMod q) :
      (if IsUnit a then
        ∫ x in Metric.closedBall (((a.val : ℝ)/(q : ℝ) : ℝ) : UnitAddCircle) t,
          shiftedArcModelIntegrand M N (((a.val : ℝ)/(q : ℝ) : ℝ) : UnitAddCircle)
            z x ∂AddCircle.haarAddCircle else 0) =
      z^2 * (if IsUnit a then fourier (-(N : ℤ))
        (((a.val : ℝ)/(q : ℝ) : ℝ) : UnitAddCircle) else 0) *
          localDiscreteMainIntegral M N t := by
    by_cases ha : IsUnit a
    · simp only [ha, if_true]
      exact integral_shiftedArcModel_closedBall M N _ t z ht0 ht
    · simp [ha]
  change (∑ a : ZMod q, if IsUnit a then
    ∫ x in Metric.closedBall (((a.val : ℝ)/(q : ℝ) : ℝ) : UnitAddCircle) t,
      shiftedArcModelIntegrand M N (((a.val : ℝ)/(q : ℝ) : ℝ) : UnitAddCircle)
        z x ∂AddCircle.haarAddCircle else 0) = _
  simp_rw [hterm]
  rw [← Finset.sum_mul, ← Finset.mul_sum, rational_phase_sum_eq_integerFourierRamanujan]
  congr 1
  simp only [z, complexMajorCoefficient, dif_neg (NeZero.ne q), Int.cast_pow]
  ring

end GoldbachCircleMethodShiftedClosedArcModelV1858
