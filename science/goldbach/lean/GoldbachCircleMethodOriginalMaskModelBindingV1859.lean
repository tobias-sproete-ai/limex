import GoldbachCircleMethodShiftedClosedArcModelV1858
import GoldbachCircleMethodTwoScaleIntegralPartitionV1831

/-! # V1.8.59: bind the existing rational index, centre and radius.
The V172 index and V1829 mask are imported unchanged. No second mask is defined.
-/
open MeasureTheory
open GoldbachCircleMethodMajorMinorPartitionV172
open GoldbachCircleMethodTwoScaleMaskAdapterV1829
open GoldbachCircleMethodShiftedClosedArcModelV1858
open GoldbachCircleMethodComplexArcModelBindingV1856
open GoldbachCircleMethodDiscreteArcTailV1854

namespace GoldbachCircleMethodOriginalMaskModelBindingV1859

attribute [local instance] Classical.propDecidable

abbrev Denominator (R : ℕ) := {q : ℕ // q ∈ Finset.Icc 1 R}

instance denominatorNeZero {R : ℕ} (q : Denominator R) : NeZero q.val :=
  ⟨by have h := (Finset.mem_Icc.mp q.property).1; omega⟩

abbrev ReducedUnitIndex (R : ℕ) :=
  (q : Denominator R) × {a : ZMod q.val // IsUnit a}

noncomputable def reducedIndexUnitEquiv (R : ℕ) :
    ReducedRationalIndex R ≃ ReducedUnitIndex R where
  toFun i := by
    have hi := Finset.mem_filter.mp i.property
    have hq := (Finset.mem_product.mp hi.1).1
    exact ⟨⟨i.val.1, hq⟩, ⟨(i.val.2 : ZMod i.val.1),
      (ZMod.isUnit_iff_coprime _ _).mpr hi.2.2⟩⟩
  invFun i := by
    have ha : i.2.val.val < i.1.val := ZMod.val_lt _
    have hc : Nat.Coprime i.2.val.val i.1.val := by
      apply (ZMod.isUnit_iff_coprime _ _).mp
      simpa using i.2.property
    exact ⟨(i.1.val, i.2.val.val), Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨i.1.property,
        Finset.mem_range.mpr (ha.trans_le (Finset.mem_Icc.mp i.1.property).2)⟩,
        ha, hc⟩⟩
  left_inv i := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact ZMod.val_natCast_of_lt (Finset.mem_filter.mp i.property).2.1
  right_inv i := by
    rcases i with ⟨⟨q, hq⟩, ⟨a, ha⟩⟩
    let _ : NeZero q := ⟨by have h := (Finset.mem_Icc.mp hq).1; omega⟩
    change (⟨⟨q, hq⟩, ⟨(a.val : ZMod q), by simpa using ha⟩⟩ : ReducedUnitIndex R) =
      ⟨⟨q, hq⟩, ⟨a, ha⟩⟩
    exact congrArg (fun b : {a : ZMod q // IsUnit a} =>
      (⟨⟨q, hq⟩, b⟩ : ReducedUnitIndex R)) (Subtype.ext (ZMod.natCast_zmod_val a))

theorem sum_original_indices (R : ℕ) (f : ℕ → ℕ → ℂ) :
    (∑ i : ReducedRationalIndex R, f i.val.1 i.val.2) =
      ∑ q : Denominator R, ∑ a : ZMod q.val, if IsUnit a then f q.val a.val else 0 := by
  classical
  calc
    _ = ∑ i : ReducedUnitIndex R, f i.1.val i.2.val.val := by
      apply Fintype.sum_equiv (reducedIndexUnitEquiv R)
      intro i
      change f i.val.1 i.val.2 = f i.val.1 (i.val.2 : ZMod i.val.1).val
      rw [ZMod.val_natCast_of_lt (Finset.mem_filter.mp i.property).2.1]
    _ = _ := by
      rw [Fintype.sum_sigma]
      apply Finset.sum_congr rfl
      intro q _
      simpa only [Finset.sum_filter] using
        (Finset.sum_subtype (Finset.univ.filter (fun a : ZMod q.val => IsUnit a))
          (by simp) (fun a : ZMod q.val => f q.val a.val)).symm

theorem original_index_radius_bounds (M P R : ℕ) (hMP : 2*P < M)
    (i : ReducedRationalIndex R) :
    0 ≤ twoScaleArcRadius M P i ∧ twoScaleArcRadius M P i < 1/2 := by
  have hq : (1 : ℝ) ≤ (i.val.1 : ℝ) := by
    exact_mod_cast index_denominator_pos i
  have hM : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hP : (0 : ℝ) ≤ P := Nat.cast_nonneg P
  have hMP' : 2*(P : ℝ) < M := by exact_mod_cast hMP
  unfold twoScaleArcRadius
  constructor
  · positivity
  · rw [div_lt_iff₀ (mul_pos (by linarith : (0 : ℝ) < i.val.1) hM)]
    nlinarith

theorem original_index_arc_model_integral (M P R N : ℕ) (hMP : 2*P < M)
    (i : ReducedRationalIndex R) :
    (∫ x in Metric.closedBall (majorArcCenter i) (twoScaleArcRadius M P i),
      shiftedArcModelIntegrand M N (majorArcCenter i)
        (((ArithmeticFunction.moebius i.val.1 : ℤ) : ℂ)/(Nat.totient i.val.1 : ℂ)) x
          ∂AddCircle.haarAddCircle) =
      ((((ArithmeticFunction.moebius i.val.1 : ℤ) : ℂ)/(Nat.totient i.val.1 : ℂ))^2 *
        fourier (-(N : ℤ)) (majorArcCenter i)) *
          localDiscreteMainIntegral M N (twoScaleArcRadius M P i) := by
  exact integral_shiftedArcModel_closedBall M N _ _ _
    (original_index_radius_bounds M P R hMP i).1
    (original_index_radius_bounds M P R hMP i).2

noncomputable def originalIndexArcModelSum (M P R N : ℕ) : ℂ :=
  ∑ i : ReducedRationalIndex R,
    ∫ x in Metric.closedBall (majorArcCenter i) (twoScaleArcRadius M P i),
      shiftedArcModelIntegrand M N (majorArcCenter i)
        (((ArithmeticFunction.moebius i.val.1 : ℤ) : ℂ)/(Nat.totient i.val.1 : ℂ)) x
          ∂AddCircle.haarAddCircle

theorem originalIndexArcModelSum_eq_complex_model (M P R N : ℕ) (hMP : 2*P < M) :
    originalIndexArcModelSum M P R N = complexDiscreteArcMainModel M N R P := by
  classical
  unfold originalIndexArcModelSum majorArcCenter twoScaleArcRadius
  rw [sum_original_indices R (fun q a =>
    ∫ x in Metric.closedBall (((a : ℝ)/(q : ℝ) : ℝ) : UnitAddCircle)
      ((P : ℝ)/((q : ℝ)*(M : ℝ))),
      shiftedArcModelIntegrand M N (((a : ℝ)/(q : ℝ) : ℝ) : UnitAddCircle)
        (((ArithmeticFunction.moebius q : ℤ) : ℂ)/(Nat.totient q : ℂ)) x
          ∂AddCircle.haarAddCircle)]
  have hq (q : Denominator R) :
      0 ≤ (P : ℝ)/((q.val : ℝ)*(M : ℝ)) ∧
        (P : ℝ)/((q.val : ℝ)*(M : ℝ)) < 1/2 := by
    have hq1 : (1 : ℝ) ≤ q.val := by exact_mod_cast (Finset.mem_Icc.mp q.property).1
    have hM : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
    have hMP' : 2*(P : ℝ) < M := by exact_mod_cast hMP
    constructor
    · positivity
    · rw [div_lt_iff₀ (mul_pos (by linarith : (0 : ℝ) < q.val) hM)]
      nlinarith
  simp_rw [sum_unit_center_arc_models M N _ _ (hq _).1 (hq _).2]
  simpa only [complexDiscreteArcMainModel] using
    (Finset.sum_coe_sort (Finset.Icc 1 R) (fun q : ℕ =>
      complexMajorCoefficient N q * localDiscreteMainIntegral M N
        ((P : ℝ)/((q : ℝ)*(M : ℝ)))))

end GoldbachCircleMethodOriginalMaskModelBindingV1859
