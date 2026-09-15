import GoldbachCircleMethodActualMaskReflectionV1886

/-! Explicit Fourier kernel of the unchanged disjoint closed-arc mask. -/
set_option autoImplicit false
open scoped BigOperators Classical
open MeasureTheory AddCircle
open GoldbachCircleMethodMajorMinorPartitionV172
open GoldbachCircleMethodTwoScaleMaskAdapterV1829
open GoldbachCircleMethodTwoScaleIntegralPartitionV1831
open GoldbachCircleMethodClosedArcCoordinatesV1857
open GoldbachCircleMethodShiftedClosedArcModelV1858
open GoldbachCircleMethodOriginalMaskModelBindingV1859
open GoldbachCircleMethodOriginalMaskDisjointnessV1860
open GoldbachCircleMethodArithmeticHalfShiftV1883
open GoldbachCircleMethodSignedMaskKernelConvolutionV1884

namespace GoldbachCircleMethodExplicitMaskFourierKernelV1887

noncomputable def centeredCharacterKernel (k : ℤ) (t : ℝ) : ℂ :=
  if k = 0 then (2*t : ℝ)
  else (1/(-2*(Real.pi : ℂ)*Complex.I*(k : ℂ))) *
    (fourier (-k) (t : UnitAddCircle)-fourier (-k) ((-t : ℝ) : UnitAddCircle))

theorem centered_character_integral (k : ℤ) (t : ℝ) :
    (∫ x in -t..t, fourier (-k) (x : UnitAddCircle)) =
      centeredCharacterKernel k t := by
  by_cases hk : k = 0
  · subst k
    simp [centeredCharacterKernel, intervalIntegral.integral_const, Complex.real_smul]
    ring
  · rw [centeredCharacterKernel, if_neg hk]
    have hi : IntervalIntegrable (fun x : ℝ => fourier (-k) (x : UnitAddCircle))
        volume (-t) t :=
      ((fourier (-k)).continuous.comp (AddCircle.continuous_mk' (1 : ℝ))).intervalIntegrable _ _
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x _ => has_antideriv_at_fourier_neg (T := (1 : ℝ)) inferInstance hk x) hi
    simpa only [Complex.ofReal_one, mul_sub] using h

theorem closed_arc_character_integral (k : ℤ) (c t : ℝ)
    (ht0 : 0 ≤ t) (ht : t < 1/2) :
    (∫ x in Metric.closedBall (c : UnitAddCircle) t,
      fourier (-k) x ∂haarAddCircle) =
      fourier (-k) (c : UnitAddCircle)*centeredCharacterKernel k t := by
  rw [integral_closedBall_eq_centered_interval _ c t ht0 ht]
  simp_rw [QuotientAddGroup.mk_add, fourier_argument_add]
  rw [intervalIntegral.integral_const_mul, centered_character_integral]

theorem full_circle_character_integral (k : ℤ) :
    (∫ x : UnitAddCircle, fourier (-k) x ∂haarAddCircle) =
      if k = 0 then 1 else 0 := by
  have h := congrFun (fourierCoeff_fourier (T := (1 : ℝ)) 0) k
  simpa only [fourierCoeff, fourier_zero, ContinuousMap.one_apply, smul_eq_mul,
    mul_one, Pi.single_apply] using h

theorem minorMaskKernel_eq_integral (M P R : ℕ) (k : ℤ) :
    minorMaskKernel M P R k =
      ∫ x in twoScaleMinorMask M P R, fourier (-k) x ∂haarAddCircle := by
  unfold minorMaskKernel fourierCoeff minorWeight
  simp only [smul_eq_mul]
  rw [← integral_indicator (twoScaleMinorMask_measurable M P R)]
  apply integral_congr_ae
  filter_upwards [] with x
  by_cases hx : x ∈ twoScaleMinorMask M P R <;> simp [hx]

theorem explicit_original_mask_kernel (M P R : ℕ) (hscale : 2*P*R < M) (k : ℤ) :
    minorMaskKernel M P R k = (if k = 0 then 1 else 0) -
      ∑ i : ReducedRationalIndex R, fourier (-k) (majorArcCenter i) *
        centeredCharacterKernel k (twoScaleArcRadius M P i) := by
  have hf : Integrable (fourier (-k) : UnitAddCircle → ℂ) haarAddCircle :=
    (fourier (-k)).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hp := integral_add_compl (twoScaleMajorMask_measurable M P R) hf
  change (∫ x in twoScaleMajorMask M P R, fourier (-k) x ∂haarAddCircle) +
    (∫ x in twoScaleMinorMask M P R, fourier (-k) x ∂haarAddCircle) =
    (∫ x : UnitAddCircle, fourier (-k) x ∂haarAddCircle) at hp
  rw [← minorMaskKernel_eq_integral, full_circle_character_integral] at hp
  rw [integral_original_mask_eq_sum M P R hscale _ hf] at hp
  have ht (i : ReducedRationalIndex R) :
      (∫ x in Metric.closedBall (majorArcCenter i) (twoScaleArcRadius M P i),
        fourier (-k) x ∂haarAddCircle) =
      fourier (-k) (majorArcCenter i)*centeredCharacterKernel k (twoScaleArcRadius M P i) := by
    have hR : 1 ≤ R := (Nat.succ_le_of_lt (index_denominator_pos i)).trans
      (Finset.mem_Icc.mp (Finset.mem_product.mp (Finset.mem_filter.mp i.property).1).1).2
    have hMP : 2*P < M := by nlinarith
    exact closed_arc_character_integral k _ _
      (original_index_radius_bounds M P R hMP i).1
      (original_index_radius_bounds M P R hMP i).2
  simp_rw [ht] at hp
  exact (eq_sub_iff_add_eq).mpr (by simpa only [add_comm] using hp)


theorem explicit_denominator_mask_kernel (M P R : ℕ) (hscale : 2*P*R < M) (k : ℤ) :
    minorMaskKernel M P R k = (if k = 0 then 1 else 0) -
      ∑ q : Denominator R,
        GoldbachCircleMethodSignedFullPrefixV1850.integerFourierRamanujan q.val (-k)
          (NeZero.ne q.val) *
        centeredCharacterKernel k ((P : ℝ)/((q.val : ℝ)*(M : ℝ))) := by
  rw [explicit_original_mask_kernel M P R hscale]
  congr 1
  change (∑ i : ReducedRationalIndex R,
    (fun q a : ℕ => fourier (-k) (((a : ℝ)/(q : ℝ) : ℝ) : UnitAddCircle) *
      centeredCharacterKernel k ((P : ℝ)/((q : ℝ)*(M : ℝ)))) i.val.1 i.val.2) = _
  rw [sum_original_indices R (fun q a : ℕ =>
    fourier (-k) (((a : ℝ)/(q : ℝ) : ℝ) : UnitAddCircle) *
      centeredCharacterKernel k ((P : ℝ)/((q : ℝ)*(M : ℝ))))]
  apply Finset.sum_congr rfl
  intro q _
  rw [← GoldbachCircleMethodComplexArcModelBindingV1856.rational_phase_sum_eq_integerFourierRamanujan]
  rw [Finset.sum_mul]
  simp only [ite_mul, zero_mul]


theorem fourier_real_argument_im (k : ℤ) (t : ℝ) :
    (fourier k (t : UnitAddCircle)).im = Real.sin (2*Real.pi*(k : ℝ)*t) := by
  simp [Complex.exp_im, Complex.mul_re, Complex.mul_im]

theorem centeredCharacterKernel_sine (k : ℤ) (hk : k ≠ 0) (t : ℝ) :
    centeredCharacterKernel k t =
      ((Real.sin (2*Real.pi*(k : ℝ)*t)/(Real.pi*(k : ℝ)) : ℝ) : ℂ) := by
  rw [centeredCharacterKernel, if_neg hk]
  have hconj : fourier (-k) ((-t : ℝ) : UnitAddCircle) =
      (starRingEnd ℂ) (fourier (-k) (t : UnitAddCircle)) := by
    simpa only [AddCircle.coe_neg] using
      GoldbachCircleMethodActualMaskReflectionV1886.fourier_neg_argument (-k) (t : UnitAddCircle)
  rw [hconj]
  have hz (z : ℂ) : z-(starRingEnd ℂ) z = (2*(z.im : ℂ))*Complex.I := by
    apply Complex.ext <;> simp
    ring
  rw [hz, fourier_real_argument_im]
  have hs : Real.sin (2*Real.pi*((-k : ℤ) : ℝ)*t) =
      -Real.sin (2*Real.pi*(k : ℝ)*t) := by
    rw [Int.cast_neg, show 2*Real.pi*(-(k : ℝ))*t = -(2*Real.pi*(k : ℝ)*t) by ring,
      Real.sin_neg]
  rw [hs]
  push_cast
  have hkc : (k : ℂ) ≠ 0 := by exact_mod_cast hk
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp

end GoldbachCircleMethodExplicitMaskFourierKernelV1887
