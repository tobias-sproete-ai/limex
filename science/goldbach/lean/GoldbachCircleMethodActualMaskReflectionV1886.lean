import GoldbachCircleMethodSignedMaskKernelConvolutionV1884

/-! Reflection of the ORIGINAL mask; exact realness, not coefficient positivity. -/
set_option autoImplicit false
open scoped BigOperators Classical
open MeasureTheory AddCircle
open GoldbachCircleMethodFourierIdentityV171
open GoldbachCircleMethodMajorMinorPartitionV172
open GoldbachCircleMethodTwoScaleMaskAdapterV1829
open GoldbachCircleMethodTwoScaleIntegralPartitionV1831
open GoldbachCircleMethodTwoScaleBesselBridgeV1834
open GoldbachCircleMethodArithmeticHalfShiftV1883
open GoldbachCircleMethodSignedMaskKernelConvolutionV1884

namespace GoldbachCircleMethodActualMaskReflectionV1886

theorem original_index_has_neg_center {R : ℕ} (i : ReducedRationalIndex R) :
    ∃ j : ReducedRationalIndex R,
      j.val.1 = i.val.1 ∧ majorArcCenter j = -majorArcCenter i := by
  let q := i.val.1
  let _ : NeZero q := ⟨(index_denominator_pos i).ne'⟩
  let a : ZMod q := i.val.2
  have hua : IsUnit a :=
    (ZMod.isUnit_iff_coprime _ _).mpr (Finset.mem_filter.mp i.property).2.2
  have hneg : Nat.Coprime (-a).val q := by
    apply (ZMod.isUnit_iff_coprime _ _).mp
    simpa using hua.neg
  have hq := (Finset.mem_product.mp (Finset.mem_filter.mp i.property).1).1
  have ha := ZMod.val_lt (-a)
  let j : ReducedRationalIndex R := ⟨(q, (-a).val), Finset.mem_filter.mpr
    ⟨Finset.mem_product.mpr ⟨hq, Finset.mem_range.mpr
      (ha.trans_le (Finset.mem_Icc.mp hq).2)⟩, ha, hneg⟩⟩
  refine ⟨j, rfl, ?_⟩
  change ((((-a).val : ℝ)/(q : ℝ) : ℝ) : UnitAddCircle) =
    -(((i.val.2 : ℝ)/(q : ℝ) : ℝ) : UnitAddCircle)
  rw [← ZMod.toAddCircle_apply, map_neg]
  congr 1
  exact ZMod.toAddCircle_natCast i.val.2

theorem original_major_reflection (M P R : ℕ) (x : UnitAddCircle) :
    -x ∈ twoScaleMajorMask M P R ↔ x ∈ twoScaleMajorMask M P R := by
  have h : ∀ y : UnitAddCircle, y ∈ twoScaleMajorMask M P R →
      -y ∈ twoScaleMajorMask M P R := by
    intro y hy
    rcases Set.mem_iUnion.mp hy with ⟨i,hi⟩
    obtain ⟨j,hq,hc⟩ := original_index_has_neg_center i
    apply Set.mem_iUnion.mpr
    refine ⟨j, ?_⟩
    change dist (-y) (majorArcCenter j) ≤ twoScaleArcRadius M P j
    rw [hc, dist_neg_neg]
    simpa only [Metric.mem_closedBall, twoScaleArcRadius, hq] using hi
  exact ⟨fun hx => by simpa using h (-x) hx, h x⟩

theorem original_minor_reflection (M P R : ℕ) (x : UnitAddCircle) :
    -x ∈ twoScaleMinorMask M P R ↔ x ∈ twoScaleMinorMask M P R := by
  simp only [twoScaleMinorMask, Set.mem_compl_iff, original_major_reflection]

theorem minorWeight_reflection (M P R : ℕ) (x : UnitAddCircle) :
    minorWeight M P R (-x) = minorWeight M P R x := by
  simp only [minorWeight, Set.indicator_apply, original_minor_reflection]

theorem minorWeight_conj (M P R : ℕ) (x : UnitAddCircle) :
    (starRingEnd ℂ) (minorWeight M P R x) = minorWeight M P R x := by
  by_cases hx : x ∈ twoScaleMinorMask M P R <;> simp [minorWeight, hx]

theorem fourier_neg_argument (k : ℤ) (x : UnitAddCircle) :
    fourier k (-x) = (starRingEnd ℂ) (fourier k x) := by
  simpa only [fourier_apply, smul_neg] using
    (fourier_neg' (n := k) (x := x))

theorem minorMaskKernel_im_zero (M P R : ℕ) (k : ℤ) :
    (minorMaskKernel M P R k).im = 0 := by
  apply Complex.conj_eq_iff_im.mp
  unfold minorMaskKernel fourierCoeff
  rw [← integral_conj]
  calc
    _ = ∫ x : UnitAddCircle,
        fourier (-k) (-x) * minorWeight M P R (-x) ∂haarAddCircle := by
      apply integral_congr_ae
      filter_upwards [] with x
      simp only [smul_eq_mul, map_mul, ← fourier_neg_argument,
        minorWeight_conj, minorWeight_reflection]
    _ = _ := by
      simpa only [smul_eq_mul] using
        (integral_neg_eq_self (fun x : UnitAddCircle =>
          fourier (-k) x * minorWeight M P R x) haarAddCircle)

theorem actual_masked_coefficient_im_zero (M P R N : ℕ) :
    (fourierCoeff (maskedSquare M P R) (N : ℤ)).im = 0 := by
  rw [maskedSquare_coefficient_exact_finite_convolution]
  simp [Complex.mul_im, minorMaskKernel_im_zero]

theorem actual_real_part_discards_no_energy (M P R N : ℕ) :
    (twoScaleMinorIntegralReal M P R N)^2 =
      ‖fourierCoeff (maskedSquare M P R) (N : ℤ)‖^2 := by
  rw [minorReal_eq_re_fourierCoeff, Complex.sq_norm]
  simp [Complex.normSq_apply, actual_masked_coefficient_im_zero, pow_two]

end GoldbachCircleMethodActualMaskReflectionV1886
