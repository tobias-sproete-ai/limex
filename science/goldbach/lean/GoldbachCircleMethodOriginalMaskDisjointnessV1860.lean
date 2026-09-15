import GoldbachCircleMethodOriginalMaskModelBindingV1859

/-! # V1.8.60: rational separation and actual closed-mask disjointness.
The reduced indices, centres and radii are the unchanged V172/V1829 objects.
-/
open GoldbachCircleMethodMajorMinorPartitionV172
open GoldbachCircleMethodTwoScaleMaskAdapterV1829

namespace GoldbachCircleMethodOriginalMaskDisjointnessV1860

theorem center_addOrderOf {R : ℕ} (i : ReducedRationalIndex R) :
    addOrderOf (majorArcCenter i) = i.val.1 := by
  simpa only [majorArcCenter, mul_one] using
    (AddCircle.addOrderOf_div_of_gcd_eq_one (p := (1 : ℝ))
      (index_denominator_pos i) (Finset.mem_filter.mp i.property).2.2.gcd_eq_one)

theorem center_representative_mem_Ico {R : ℕ} (i : ReducedRationalIndex R) :
    (i.val.2 : ℝ)/(i.val.1 : ℝ) ∈ Set.Ico 0 (0+1 : ℝ) := by
  have hq : (0 : ℝ) < i.val.1 := by exact_mod_cast index_denominator_pos i
  have ha : (i.val.2 : ℝ) < i.val.1 := by
    exact_mod_cast (Finset.mem_filter.mp i.property).2.1
  constructor
  · positivity
  · rw [zero_add, div_lt_one hq]
    exact ha

theorem majorArcCenter_injective (R : ℕ) :
    Function.Injective (majorArcCenter : ReducedRationalIndex R → UnitAddCircle) := by
  intro i j hij
  have hq : i.val.1 = j.val.1 := by
    simpa only [center_addOrderOf] using congrArg addOrderOf hij
  have hab : (i.val.2 : ℝ)/(i.val.1 : ℝ) = (j.val.2 : ℝ)/(j.val.1 : ℝ) :=
    (AddCircle.coe_eq_coe_iff_of_mem_Ico
      (center_representative_mem_Ico i) (center_representative_mem_Ico j)).mp hij
  rw [hq] at hab
  have hqne : (j.val.1 : ℝ) ≠ 0 := by
    exact_mod_cast (index_denominator_pos j).ne'
  have ha : i.val.2 = j.val.2 := by
    have hr := (div_left_inj' hqne).mp hab
    exact_mod_cast hr
  exact Subtype.ext (Prod.ext hq ha)

theorem center_denominator_nsmul {R : ℕ} (i : ReducedRationalIndex R) :
    i.val.1 • majorArcCenter i = 0 := by
  rw [← center_addOrderOf i, addOrderOf_nsmul_eq_zero]

theorem distinct_centers_distance_lower (R : ℕ) (i j : ReducedRationalIndex R)
    (hij : i ≠ j) :
    1/((i.val.1 : ℝ)*(j.val.1 : ℝ)) ≤ dist (majorArcCenter i) (majorArcCenter j) := by
  let u := majorArcCenter i - majorArcCenter j
  have hu0 : u ≠ 0 := by
    intro h
    exact hij (majorArcCenter_injective R (sub_eq_zero.mp h))
  have hn : 0 < i.val.1*j.val.1 :=
    Nat.mul_pos (index_denominator_pos i) (index_denominator_pos j)
  have hkill : (i.val.1*j.val.1) • u = 0 := by
    rw [show u = majorArcCenter i - majorArcCenter j from rfl, nsmul_sub]
    have hi : (i.val.1*j.val.1) • majorArcCenter i = 0 := by
      rw [Nat.mul_comm, mul_smul, center_denominator_nsmul, smul_zero]
    have hj : (i.val.1*j.val.1) • majorArcCenter j = 0 := by
      rw [mul_smul, center_denominator_nsmul, smul_zero]
    rw [hi, hj, sub_self]
  have hfin : IsOfFinAddOrder u := isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨_, hn, hkill⟩
  have horder : addOrderOf u ≤ i.val.1*j.val.1 :=
    addOrderOf_le_of_nsmul_eq_zero hn hkill
  have hnorm : (1 : ℝ) ≤ (addOrderOf u : ℝ)*‖u‖ := by
    simpa only [nsmul_eq_mul] using
      (AddCircle.le_add_order_smul_norm_of_isOfFinAddOrder hfin hu0)
  have hbound : (1 : ℝ) ≤ ((i.val.1*j.val.1 : ℕ) : ℝ)*‖u‖ :=
    hnorm.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast horder) (norm_nonneg u))
  have hprod : (0 : ℝ) < (i.val.1 : ℝ)*(j.val.1 : ℝ) := by exact_mod_cast hn
  rw [div_le_iff₀ hprod, dist_eq_norm]
  simpa only [Nat.cast_mul, u, mul_comm] using hbound

theorem original_closed_arcs_pairwise_disjoint (M P R : ℕ) (hscale : 2*P*R < M) :
    Pairwise (fun i j : ReducedRationalIndex R =>
      Disjoint (Metric.closedBall (majorArcCenter i) (twoScaleArcRadius M P i))
        (Metric.closedBall (majorArcCenter j) (twoScaleArcRadius M P j))) := by
  intro i j hij
  have hq : (0 : ℝ) < i.val.1 := by exact_mod_cast index_denominator_pos i
  have hr : (0 : ℝ) < j.val.1 := by exact_mod_cast index_denominator_pos j
  have hM : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hiR : (i.val.1 : ℝ) ≤ R := by
    exact_mod_cast (Finset.mem_Icc.mp (Finset.mem_product.mp
      (Finset.mem_filter.mp i.property).1).1).2
  have hjR : (j.val.1 : ℝ) ≤ R := by
    exact_mod_cast (Finset.mem_Icc.mp (Finset.mem_product.mp
      (Finset.mem_filter.mp j.property).1).1).2
  have hs : 2*(P : ℝ)*(R : ℝ) < M := by exact_mod_cast hscale
  have hP : (0 : ℝ) ≤ P := Nat.cast_nonneg P
  have hnum : (P : ℝ)*((i.val.1 : ℝ)+(j.val.1 : ℝ)) < M := by nlinarith
  apply Metric.closedBall_disjoint_closedBall
  apply lt_of_lt_of_le _ (distinct_centers_distance_lower R i j hij)
  rw [lt_div_iff₀ (mul_pos hq hr)]
  calc
    (twoScaleArcRadius M P i + twoScaleArcRadius M P j) *
        ((i.val.1 : ℝ)*(j.val.1 : ℝ)) =
        (P : ℝ)*((i.val.1 : ℝ)+(j.val.1 : ℝ))/(M : ℝ) := by
      unfold twoScaleArcRadius
      field_simp
      ring
    _ < 1 := (div_lt_one hM).mpr hnum

theorem integral_original_mask_eq_sum (M P R : ℕ) (hscale : 2*P*R < M)
    (f : UnitAddCircle → ℂ) (hf : MeasureTheory.Integrable f AddCircle.haarAddCircle) :
    (∫ x in twoScaleMajorMask M P R, f x ∂AddCircle.haarAddCircle) =
      ∑ i : ReducedRationalIndex R,
        ∫ x in Metric.closedBall (majorArcCenter i) (twoScaleArcRadius M P i),
          f x ∂AddCircle.haarAddCircle := by
  exact MeasureTheory.integral_iUnion_fintype (fun _ => measurableSet_closedBall)
    (original_closed_arcs_pairwise_disjoint M P R hscale) (fun _ => hf.integrableOn)

end GoldbachCircleMethodOriginalMaskDisjointnessV1860
