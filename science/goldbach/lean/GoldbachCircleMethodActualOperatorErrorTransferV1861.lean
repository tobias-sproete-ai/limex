import GoldbachCircleMethodOriginalMaskDisjointnessV1860

/-! # V1.8.61: actual operator error transfer.
The rational approximation is an explicit hypothesis, not a proved SW instance.
-/
open MeasureTheory
open GoldbachCircleMethodDiscreteMainKernelV1852
open GoldbachCircleMethodDiscreteArcTailV1854
open GoldbachCircleMethodShiftedClosedArcModelV1858
open GoldbachCircleMethodOriginalMaskModelBindingV1859
open GoldbachCircleMethodOriginalMaskDisjointnessV1860
open GoldbachCircleMethodMajorMinorPartitionV172
open GoldbachCircleMethodTwoScaleMaskAdapterV1829
open GoldbachCircleMethodTwoScaleIntegralPartitionV1831
open GoldbachCircleMethodFixedScaleTransferV1824
open GoldbachCircleMethodFourierIdentityV171
open GoldbachCircleMethodClosedArcCoordinatesV1857
open GoldbachCircleMethodComplexArcModelBindingV1856
open GoldbachCircleMethodDiscreteArcModelReserveV1855

namespace GoldbachCircleMethodActualOperatorErrorTransferV1861

theorem square_error_bound (s z : ℂ) (B ε : ℝ)
    (hz : ‖z‖ ≤ B) (he : ‖s-z‖ ≤ ε) :
    ‖s^2-z^2‖ ≤ 2*B*ε+ε^2 := by
  have hB : 0 ≤ B := (norm_nonneg z).trans hz
  have hε : 0 ≤ ε := (norm_nonneg (s-z)).trans he
  have hs : ‖s‖ ≤ ε+B := by
    calc
      ‖s‖ = ‖(s-z)+z‖ := by congr 1; ring
      _ ≤ ‖s-z‖+‖z‖ := norm_add_le _ _
      _ ≤ ε+B := add_le_add he hz
  rw [show s^2-z^2 = (s-z)*(s+z) by ring, norm_mul]
  calc
    ‖s-z‖*‖s+z‖ ≤ ε*(ε+2*B) :=
      mul_le_mul he ((norm_add_le s z).trans (by linarith))
        (norm_nonneg _) hε
    _ = 2*B*ε+ε^2 := by ring

theorem discreteMainPolynomial_norm_le_cutoff (M : ℕ) (x : UnitAddCircle) :
    ‖discreteMainPolynomial M x‖ ≤ M := by
  unfold discreteMainPolynomial
  calc
    ‖∑ n ∈ Finset.Icc 1 M, fourier (n : ℤ) x‖ ≤
      ∑ n ∈ Finset.Icc 1 M, ‖fourier (n : ℤ) x‖ := norm_sum_le _ _
    _ = M := by simp [fourier_apply, Circle.norm_coe]

theorem rational_amplitude_norm_le_one (q : ℕ) (hq : 0 < q) :
    ‖((ArithmeticFunction.moebius q : ℤ) : ℂ)/(Nat.totient q : ℂ)‖ ≤ 1 := by
  have ht : (1 : ℝ) ≤ Nat.totient q := by exact_mod_cast Nat.totient_pos.mpr hq
  have hm : |((ArithmeticFunction.moebius q : ℤ) : ℝ)| ≤ 1 := by
    exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := q))
  rw [norm_div, Complex.norm_natCast]
  have hcast : ‖((ArithmeticFunction.moebius q : ℤ) : ℂ)‖ =
      |((ArithmeticFunction.moebius q : ℤ) : ℝ)| := by
    rw [← Complex.ofReal_intCast, Complex.norm_real, Real.norm_eq_abs]
  rw [hcast, div_le_one (by linarith : (0 : ℝ) < Nat.totient q)]
  exact hm.trans ht

theorem local_model_norm_le_cutoff (M q : ℕ) (hq : 0 < q) (x : UnitAddCircle) :
    ‖(((ArithmeticFunction.moebius q : ℤ) : ℂ)/(Nat.totient q : ℂ)) *
      discreteMainPolynomial M x‖ ≤ M := by
  rw [norm_mul]
  calc
    _ ≤ 1*(M : ℝ) := mul_le_mul (rational_amplitude_norm_le_one q hq)
      (discreteMainPolynomial_norm_le_cutoff M x) (norm_nonneg _) (by norm_num)
    _ = M := one_mul _

theorem haar_real_closedBall (c t : ℝ) (ht0 : 0 ≤ t) (ht : t < 1/2) :
    AddCircle.haarAddCircle.real (Metric.closedBall (c : UnitAddCircle) t) = 2*t := by
  have h := integral_closedBall_eq_interval (fun _ => (1 : ℂ)) c t ht0 ht
  have hr := congrArg Complex.re h
  simpa [two_mul] using hr

theorem shiftedArcModelIntegrand_integrable (M N : ℕ) (c : UnitAddCircle) (z : ℂ) :
    Integrable (shiftedArcModelIntegrand M N c z) AddCircle.haarAddCircle := by
  have hc : Continuous (shiftedArcModelIntegrand M N c z) := by
    unfold shiftedArcModelIntegrand
    exact (fourier (-(N : ℤ))).continuous.mul
      ((continuous_const.mul ((discreteMainPolynomial_continuous M).comp
        (continuous_id.sub continuous_const))).pow 2)
  simpa only [IntegrableOn, Measure.restrict_univ] using
    (ContinuousOn.integrableOn_compact (μ := AddCircle.haarAddCircle)
      (K := Set.univ) isCompact_univ hc.continuousOn)

theorem actual_integrand_error_bound (M N q : ℕ) (hq : 0 < q)
    (c x : UnitAddCircle) (ε : ℝ)
    (happrox : ‖exponentialSum M.succ x -
      (((ArithmeticFunction.moebius q : ℤ) : ℂ)/(Nat.totient q : ℂ)) *
        discreteMainPolynomial M (x-c)‖ ≤ ε) :
    ‖fixedScalePairFourierIntegrand M N x - shiftedArcModelIntegrand M N c
      (((ArithmeticFunction.moebius q : ℤ) : ℂ)/(Nat.totient q : ℂ)) x‖ ≤
        2*(M : ℝ)*ε+ε^2 := by
  have h := square_error_bound (exponentialSum M.succ x)
    ((((ArithmeticFunction.moebius q : ℤ) : ℂ)/(Nat.totient q : ℂ)) *
      discreteMainPolynomial M (x-c)) (M : ℝ) ε
        (local_model_norm_le_cutoff M q hq (x-c)) happrox
  unfold fixedScalePairFourierIntegrand shiftedArcModelIntegrand
  rw [← mul_sub, norm_mul]
  simpa only [fourier_apply, Circle.norm_coe, one_mul, pow_two] using h

theorem individual_arc_error_bound (M P R N : ℕ) (hMP : 2*P < M)
    (i : ReducedRationalIndex R) (ε : ℝ)
    (happrox : ∀ x ∈ Metric.closedBall (majorArcCenter i) (twoScaleArcRadius M P i),
      ‖exponentialSum M.succ x -
        (((ArithmeticFunction.moebius i.val.1 : ℤ) : ℂ)/(Nat.totient i.val.1 : ℂ)) *
          discreteMainPolynomial M (x-majorArcCenter i)‖ ≤ ε) :
    ‖(∫ x in Metric.closedBall (majorArcCenter i) (twoScaleArcRadius M P i),
        fixedScalePairFourierIntegrand M N x ∂AddCircle.haarAddCircle) -
      (∫ x in Metric.closedBall (majorArcCenter i) (twoScaleArcRadius M P i),
        shiftedArcModelIntegrand M N (majorArcCenter i)
          (((ArithmeticFunction.moebius i.val.1 : ℤ) : ℂ)/(Nat.totient i.val.1 : ℂ)) x
            ∂AddCircle.haarAddCircle)‖ ≤
      (2*(M : ℝ)*ε+ε^2)*(2*twoScaleArcRadius M P i) := by
  rw [← integral_sub (fixedScalePairFourierIntegrand_integrable M N).integrableOn
    (shiftedArcModelIntegrand_integrable M N (majorArcCenter i) _).integrableOn]
  have hb := norm_setIntegral_le_of_norm_le_const (μ := AddCircle.haarAddCircle)
    (s := Metric.closedBall (majorArcCenter i) (twoScaleArcRadius M P i))
    (measure_lt_top _ _) (fun x hx => actual_integrand_error_bound M N i.val.1
      (index_denominator_pos i) (majorArcCenter i) x ε (happrox x hx))
  rw [show AddCircle.haarAddCircle.real
      (Metric.closedBall (majorArcCenter i) (twoScaleArcRadius M P i)) =
        2*twoScaleArcRadius M P i from
      haar_real_closedBall _ _ (original_index_radius_bounds M P R hMP i).1
        (original_index_radius_bounds M P R hMP i).2] at hb
  exact hb

theorem original_major_operator_error_bound (M P R N : ℕ)
    (hR : 1 ≤ R) (hscale : 2*P*R < M) (ε : ℝ)
    (happrox : ∀ i : ReducedRationalIndex R,
      ∀ x ∈ Metric.closedBall (majorArcCenter i) (twoScaleArcRadius M P i),
        ‖exponentialSum M.succ x -
          (((ArithmeticFunction.moebius i.val.1 : ℤ) : ℂ)/(Nat.totient i.val.1 : ℂ)) *
            discreteMainPolynomial M (x-majorArcCenter i)‖ ≤ ε) :
    ‖(∫ x in twoScaleMajorMask M P R, fixedScalePairFourierIntegrand M N x
        ∂AddCircle.haarAddCircle) - complexDiscreteArcMainModel M N R P‖ ≤
      (2*(M : ℝ)*ε+ε^2) *
        (∑ i : ReducedRationalIndex R, 2*twoScaleArcRadius M P i) := by
  classical
  have hMP : 2*P < M := by nlinarith
  rw [integral_original_mask_eq_sum M P R hscale _
    (fixedScalePairFourierIntegrand_integrable M N),
    ← originalIndexArcModelSum_eq_complex_model M P R N hMP]
  unfold originalIndexArcModelSum
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i : ReducedRationalIndex R,
        ‖(∫ x in Metric.closedBall (majorArcCenter i) (twoScaleArcRadius M P i),
          fixedScalePairFourierIntegrand M N x ∂AddCircle.haarAddCircle) -
        (∫ x in Metric.closedBall (majorArcCenter i) (twoScaleArcRadius M P i),
          shiftedArcModelIntegrand M N (majorArcCenter i)
            (((ArithmeticFunction.moebius i.val.1 : ℤ) : ℂ)/(Nat.totient i.val.1 : ℂ)) x
              ∂AddCircle.haarAddCircle)‖ := norm_sum_le _ _
    _ ≤ ∑ i : ReducedRationalIndex R,
        (2*(M : ℝ)*ε+ε^2)*(2*twoScaleArcRadius M P i) := by
      apply Finset.sum_le_sum
      intro i _
      exact individual_arc_error_bound M P R N hMP i ε (happrox i)
    _ = _ := (Finset.mul_sum _ _ _).symm

theorem original_major_real_error_bound (M P R N : ℕ)
    (hR : 1 ≤ R) (hscale : 2*P*R < M) (ε : ℝ)
    (happrox : ∀ i : ReducedRationalIndex R,
      ∀ x ∈ Metric.closedBall (majorArcCenter i) (twoScaleArcRadius M P i),
        ‖exponentialSum M.succ x -
          (((ArithmeticFunction.moebius i.val.1 : ℤ) : ℂ)/(Nat.totient i.val.1 : ℂ)) *
            discreteMainPolynomial M (x-majorArcCenter i)‖ ≤ ε) :
    |twoScaleMajorIntegralReal M P R N - discreteArcMainModel M N R P| ≤
      (2*(M : ℝ)*ε+ε^2) *
        (∑ i : ReducedRationalIndex R, 2*twoScaleArcRadius M P i) := by
  have h := original_major_operator_error_bound M P R N hR hscale ε happrox
  have hr := (Complex.abs_re_le_norm
    ((∫ x in twoScaleMajorMask M P R, fixedScalePairFourierIntegrand M N x
      ∂AddCircle.haarAddCircle) - complexDiscreteArcMainModel M N R P)).trans h
  simpa only [Complex.sub_re, complexDiscreteArcMainModel_re,
    twoScaleMajorIntegralReal] using hr

end GoldbachCircleMethodActualOperatorErrorTransferV1861
