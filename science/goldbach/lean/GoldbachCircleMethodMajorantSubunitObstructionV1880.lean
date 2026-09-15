import GoldbachCircleMethodConditionalGlobalExceptionDecayV1879

/-! # V1.8.80: limitation of the existing explicit upper majorant only.
A lower bound on this majorant is NOT a lower bound on actual exceptions,
and is NOT a no-go theorem for other analytic methods.
-/
set_option autoImplicit false
open Filter Topology
open GoldbachCircleMethodQuantitativeMinorEvenBlockV1874

namespace GoldbachCircleMethodMajorantSubunitObstructionV1880

/-- The literal V1.8.74 count majorant, not the actual exception count. -/
noncomputable def countMajorant (M P R : ℕ) (C : ℝ) : ℝ :=
  784*fourthMomentBudget M P R C/(M : ℝ)^2

theorem countMajorant_cutoff_independent_floor (M P R : ℕ) (C : ℝ) (hM : 0 < M) :
    2352*C^2*(M : ℝ)^((3 : ℝ)/5)*(Real.log (M : ℝ))^10 ≤
      countMajorant M P R C := by
  have hm : (0 : ℝ) < M := by exact_mod_cast hM
  have hprod : (M : ℝ)^((8 : ℝ)/5) = (M : ℝ)^((3 : ℝ)/5)*(M : ℝ) := by
    calc
      _ = (M : ℝ)^(((3 : ℝ)/5)+1) := by norm_num
      _ = (M : ℝ)^((3 : ℝ)/5)*(M : ℝ)^((1 : ℝ)) := Real.rpow_add hm _ _
      _ = _ := by rw [Real.rpow_one]
  have hbr : (M : ℝ)^((8 : ℝ)/5) ≤
      (M : ℝ)^2/(R : ℝ)+(M : ℝ)^((8 : ℝ)/5)+2*(M : ℝ)^2/(P : ℝ) := by
    have h1 : (0 : ℝ) ≤ (M : ℝ)^2/(R : ℝ) := by positivity
    have h2 : (0 : ℝ) ≤ 2*(M : ℝ)^2/(P : ℝ) := by positivity
    linarith
  have hb := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hbr
      (show 0 ≤ 784*(3*C^2*(M : ℝ)*(Real.log (M : ℝ))^10) by positivity))
    (show 0 ≤ (M : ℝ)^2 by positivity)
  change _ ≤ 784*(3*C^2*(M : ℝ)*(Real.log (M : ℝ))^10*
    ((M : ℝ)^2/(R : ℝ)+(M : ℝ)^((8 : ℝ)/5)+2*(M : ℝ)^2/(P : ℝ)))/(M : ℝ)^2
  calc
    _ = 784*(3*C^2*(M : ℝ)*(Real.log (M : ℝ))^10)*(M : ℝ)^((8 : ℝ)/5)/(M : ℝ)^2 := by
      rw [hprod]
      field_simp
      ring
    _ ≤ _ := by simpa only [mul_assoc] using hb

theorem countMajorant_tendsto_atTop (P R : ℕ → ℕ) (C : ℝ) (hC : 0 < C) :
    Tendsto (fun M : ℕ => countMajorant M (P M) (R M) C) atTop atTop := by
  have hc : 0 < 2352*C^2 := by positivity
  have hbase : Tendsto (fun M : ℕ => 2352*C^2*(M : ℝ)^((3 : ℝ)/5)) atTop atTop :=
    Filter.Tendsto.const_mul_atTop hc
      ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 3/5)).comp
        tendsto_natCast_atTop_atTop)
  apply tendsto_atTop_mono' atTop _ hbase
  filter_upwards [eventually_gt_atTop (0 : ℕ),
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1]
      with M hM hl
  change 1 ≤ Real.log (M : ℝ) at hl
  have hp : (1 : ℝ) ≤ (Real.log (M : ℝ))^10 := one_le_pow₀ hl
  calc
    _ ≤ 2352*C^2*(M : ℝ)^((3 : ℝ)/5)*(Real.log (M : ℝ))^10 :=
      le_mul_of_one_le_right (by positivity) hp
    _ ≤ _ := countMajorant_cutoff_independent_floor M (P M) (R M) C hM

theorem eventually_countMajorant_gt_one (P R : ℕ → ℕ) (C : ℝ) (hC : 0 < C) :
    ∀ᶠ M : ℕ in atTop, 1 < countMajorant M (P M) (R M) C :=
  (countMajorant_tendsto_atTop P R C hC).eventually_gt_atTop 1

/-- A logical countermodel for an upper-bound-only inference, not a Goldbach number. -/
theorem upper_bound_allows_nonzero_count (U : ℝ) (hU : 1 ≤ U) :
    ∃ n : ℕ, (n : ℝ) ≤ U ∧ n ≠ 0 :=
  ⟨1, by simpa using hU, by decide⟩

theorem eventually_majorant_allows_nonzero_count (P R : ℕ → ℕ) (C : ℝ) (hC : 0 < C) :
    ∀ᶠ M : ℕ in atTop, ∃ n : ℕ,
      (n : ℝ) ≤ countMajorant M (P M) (R M) C ∧ n ≠ 0 := by
  filter_upwards [eventually_countMajorant_gt_one P R C hC] with M hM
  exact upper_bound_allows_nonzero_count _ hM.le

end GoldbachCircleMethodMajorantSubunitObstructionV1880
