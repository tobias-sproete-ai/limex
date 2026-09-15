import GoldbachCircleMethodMaskedFrequencyCountermodelV1881

/-! Bind the broad-class countermodel to the unchanged minor mask.
The comparator remains non-arithmetic; no statement about actual prime coefficients. -/
set_option autoImplicit false
open scoped BigOperators Classical
open MeasureTheory AddCircle Filter Topology
open GoldbachCircleMethodMajorMinorPartitionV172
open GoldbachCircleMethodTwoScaleMaskAdapterV1829
open GoldbachCircleMethodTwoScaleIntegralPartitionV1831
open GoldbachCircleMethodClosedArcCoordinatesV1857
open GoldbachCircleMethodOriginalMaskModelBindingV1859
open GoldbachCircleMethodCeilScaleEnvelopesV1864
open GoldbachCircleMethodMaskedFrequencyCountermodelV1881
open GoldbachCircleMethodExceptionalTransferV1823

namespace GoldbachCircleMethodOriginalMaskCountermodelBindingV1882

theorem reduced_index_card_le_square (R : ℕ) :
    Fintype.card (ReducedRationalIndex R) ≤ R^2 := by
  rw [Fintype.card_coe]
  calc
    _ ≤ ((Finset.Icc 1 R).product (Finset.range R)).card :=
      Finset.card_filter_le _ _
    _ = _ := by simp [pow_two]

theorem original_arc_measure (M P R : ℕ) (hMP : 2*P < M)
    (i : ReducedRationalIndex R) :
    haarAddCircle.real (Metric.closedBall (majorArcCenter i) (twoScaleArcRadius M P i)) =
      2*twoScaleArcRadius M P i := by
  have h := integral_closedBall_eq_interval (fun _ => (1 : ℂ))
    ((i.val.2 : ℝ)/(i.val.1 : ℝ)) (twoScaleArcRadius M P i)
    (original_index_radius_bounds M P R hMP i).1
    (original_index_radius_bounds M P R hMP i).2
  have hr := congrArg Complex.re h
  simpa [integral_const, intervalIntegral.integral_const, Complex.real_smul, two_mul,
    majorArcCenter] using hr

/-- Deliberately coarse R^2 bound; enough for the fixed polylogarithmic scales. -/
theorem original_major_measure_le (M P R : ℕ) (hMP : 2*P < M) :
    haarAddCircle.real (twoScaleMajorMask M P R) ≤
      2*(P : ℝ)*(R : ℝ)^2/(M : ℝ) := by
  have hm : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hb (i : ReducedRationalIndex R) :
      haarAddCircle.real (Metric.closedBall (majorArcCenter i) (twoScaleArcRadius M P i)) ≤
        2*(P : ℝ)/(M : ℝ) := by
    rw [original_arc_measure M P R hMP i]
    have hq : (1 : ℝ) ≤ i.val.1 := by exact_mod_cast index_denominator_pos i
    have hd : twoScaleArcRadius M P i ≤ (P : ℝ)/(M : ℝ) := by
      unfold twoScaleArcRadius
      apply div_le_div_of_nonneg_left (Nat.cast_nonneg P) hm
      nlinarith
    simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left hd (by norm_num : (0 : ℝ) ≤ 2)
  calc
    _ ≤ ∑ i : ReducedRationalIndex R,
        haarAddCircle.real (Metric.closedBall (majorArcCenter i) (twoScaleArcRadius M P i)) :=
      measureReal_iUnion_fintype_le _
    _ ≤ ∑ _i : ReducedRationalIndex R, 2*(P : ℝ)/(M : ℝ) :=
      Finset.sum_le_sum (fun i _ => hb i)
    _ = (Fintype.card (ReducedRationalIndex R) : ℝ)*(2*(P : ℝ)/(M : ℝ)) := by simp
    _ ≤ (R : ℝ)^2*(2*(P : ℝ)/(M : ℝ)) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast reduced_index_card_le_square R
    _ = _ := by ring

theorem logarithmic_coarse_mass_tendsto_zero (K : ℕ) :
    Tendsto (fun M : ℕ =>
      2*(logWidth K M : ℝ)*(logRadius K M : ℝ)^2/(M : ℝ)) atTop (𝓝 0) := by
  have hu : Tendsto (fun M : ℕ => 16*(Real.log (M : ℝ))^(5*K)/(M : ℝ))
      atTop (𝓝 0) := by
    simpa only [mul_zero, mul_div_assoc] using
      (log_power_div_scale_tendsto_zero (5*K)).const_mul 16
  apply squeeze_zero' (Eventually.of_forall (fun _ => by positivity)) _ hu
  filter_upwards [(Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1]
    with M hl
  change 1 ≤ Real.log (M : ℝ) at hl
  have hP := (ceil_power_bounds _ hl (3*K)).2
  change (logWidth K M : ℝ) ≤ 2*(Real.log (M : ℝ))^(3*K) at hP
  have hR := (ceil_power_bounds _ hl K).2
  have hs : (logRadius K M : ℝ)^2 ≤ (2*(Real.log (M : ℝ))^K)^2 := by
    change (logRadius K M : ℝ) ≤ 2*(Real.log (M : ℝ))^K at hR
    nlinarith [Nat.cast_nonneg (logRadius K M) (α := ℝ)]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg M)
  calc
    _ ≤ 2*(2*(Real.log (M : ℝ))^(3*K))*(2*(Real.log (M : ℝ))^K)^2 := by
      apply mul_le_mul (by linarith : 2*(logWidth K M : ℝ) ≤
        2*(2*(Real.log (M : ℝ))^(3*K))) hs (by positivity) (by positivity)
    _ = _ := by rw [show 5*K=3*K+K*2 by omega, pow_add, pow_mul]; ring

theorem original_minor_measure_tendsto_one (K : ℕ) :
    Tendsto (fun M : ℕ =>
      haarAddCircle.real (twoScaleMinorMask M (logWidth K M) (logRadius K M)))
        atTop (𝓝 1) := by
  have hmajor : Tendsto (fun M : ℕ =>
      haarAddCircle.real (twoScaleMajorMask M (logWidth K M) (logRadius K M)))
        atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall (fun _ => measureReal_nonneg)) _
      (logarithmic_coarse_mass_tendsto_zero K)
    filter_upwards [log_scales_eventually_disjoint K] with M hM
    apply original_major_measure_le
    have h := hM.2.2
    have hr := hM.1
    nlinarith
  have h := (tendsto_const_nhds (x := (1 : ℝ))).sub hmajor
  simpa [twoScaleMinorMask, measureReal_compl (twoScaleMajorMask_measurable _ _ _)] using h

/-- Uniform in all nonempty target carriers: the comparator is still NOT the actual S^2. -/
theorem eventually_original_mask_rejects_fixed_factor (K : ℕ) (ε : ℝ) (hε : ε < 1) :
    ∀ᶠ M : ℕ in atTop, ∀ (T : Finset ℕ) (n : ℕ), n ∈ T →
      ¬ (negativePartSquaredMoment T
          (fun N => (fourierCoeff (negativeMaskedMode
            (twoScaleMinorMask M (logWidth K M) (logRadius K M)) n) (N : ℤ)).re) ≤
        ε*(∫ x : UnitAddCircle, ‖negativeMaskedMode
          (twoScaleMinorMask M (logWidth K M) (logRadius K M)) n x‖^2 ∂haarAddCircle)) := by
  have hm := original_minor_measure_tendsto_one K
  filter_upwards [hm.eventually_const_lt hε, hm.eventually_const_lt (by norm_num : (0 : ℝ) < 1)]
    with M he hp T n hn
  exact masked_mode_rejects_small_factor _ (twoScaleMinorMask_measurable _ _ _) hp T n hn ε he

end GoldbachCircleMethodOriginalMaskCountermodelBindingV1882
