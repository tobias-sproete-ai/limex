import GoldbachCircleMethodCanonicalPairwiseBlockBindingV18326

/-!
# Goldbach V1.8.327: finite Abel control for pairwise-period errors

This module isolates the deterministic summation-by-parts mechanism needed to
replace pointwise spatial freezing by bounded total variation.  It is purely
finite and applies to arbitrary complex sequences whose prefix sums are
uniformly bounded.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodPairwiseAbelVariationV18327

/-- A real scalar weight acting on a complex sequence is controlled by the
uniform prefix bound times its terminal magnitude plus total variation. -/
theorem weighted_complex_sum_norm_le_of_prefix_bound
    (a : ℕ → ℂ) (u : ℕ → ℝ) (T : ℕ) (C V : ℝ)
    (hC : 0 ≤ C) (hT : 1 ≤ T)
    (hprefix : ∀ k : ℕ, k ≤ T → ‖∑ i ∈ Finset.range k, a i‖ ≤ C)
    (hlast : |u (T - 1)| ≤ 1)
    (hvariation :
      ∑ i ∈ Finset.range (T - 1), |u (i + 1) - u i| ≤ V) :
    ‖∑ i ∈ Finset.range T, u i • a i‖ ≤ C * (1 + V) := by
  have habel := Finset.sum_range_by_parts u a T
  rw [habel]
  calc
    _ ≤ ‖u (T - 1) • ∑ i ∈ Finset.range T, a i‖ +
          ‖∑ i ∈ Finset.range (T - 1),
            (u (i + 1) - u i) •
              ∑ j ∈ Finset.range (i + 1), a j‖ := norm_sub_le _ _
    _ ≤ |u (T - 1)| * C +
          ∑ i ∈ Finset.range (T - 1), |u (i + 1) - u i| * C := by
      apply add_le_add
      · simp only [norm_smul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (hprefix T le_rfl) (abs_nonneg _)
      · calc
          _ ≤ ∑ i ∈ Finset.range (T - 1),
              ‖(u (i + 1) - u i) •
                ∑ j ∈ Finset.range (i + 1), a j‖ := norm_sum_le _ _
          _ ≤ ∑ i ∈ Finset.range (T - 1),
              |u (i + 1) - u i| * C := by
            apply Finset.sum_le_sum
            intro i hi
            simp only [norm_smul, Real.norm_eq_abs]
            exact mul_le_mul_of_nonneg_left
              (hprefix (i + 1) (by
                have hi' := Finset.mem_range.mp hi
                omega)) (abs_nonneg _)
    _ = C * (|u (T - 1)| +
          ∑ i ∈ Finset.range (T - 1), |u (i + 1) - u i|) := by
      rw [← Finset.sum_mul]
      ring
    _ ≤ C * (1 + V) := by
      gcongr

/-- Product weights have no more total variation than the sum of the two
factor variations when every factor has magnitude at most one. -/
theorem product_weight_total_variation_le
    (u v : ℕ → ℝ) (T : ℕ) (U V : ℝ)
    (hu : ∀ i : ℕ, i < T → |u i| ≤ 1)
    (hv : ∀ i : ℕ, i < T → |v i| ≤ 1)
    (hU : ∑ i ∈ Finset.range (T - 1), |u (i + 1) - u i| ≤ U)
    (hV : ∑ i ∈ Finset.range (T - 1), |v (i + 1) - v i| ≤ V) :
    ∑ i ∈ Finset.range (T - 1),
        |u (i + 1) * v (i + 1) - u i * v i| ≤ U + V := by
  calc
    _ ≤ ∑ i ∈ Finset.range (T - 1),
        (|u (i + 1) - u i| + |v (i + 1) - v i|) := by
      apply Finset.sum_le_sum
      intro i hi
      have hi' := Finset.mem_range.mp hi
      have hiT : i < T := by omega
      have hisT : i + 1 < T := by omega
      calc
        |u (i + 1) * v (i + 1) - u i * v i| =
            |(u (i + 1) - u i) * v (i + 1) +
              u i * (v (i + 1) - v i)| := by ring_nf
        _ ≤ |u (i + 1) - u i| * |v (i + 1)| +
              |u i| * |v (i + 1) - v i| := by
          rw [← Real.norm_eq_abs]
          calc
            _ ≤ ‖(u (i + 1) - u i) * v (i + 1)‖ +
                ‖u i * (v (i + 1) - v i)‖ := norm_add_le _ _
            _ = _ := by simp only [Real.norm_eq_abs, abs_mul]
        _ ≤ |u (i + 1) - u i| * 1 +
              1 * |v (i + 1) - v i| := by
          gcongr
          · exact hv (i + 1) hisT
          · exact hu i hiT
        _ = _ := by ring
    _ = (∑ i ∈ Finset.range (T - 1), |u (i + 1) - u i|) +
          ∑ i ∈ Finset.range (T - 1), |v (i + 1) - v i| := by
      rw [Finset.sum_add_distrib]
    _ ≤ U + V := add_le_add hU hV

end GoldbachCircleMethodPairwiseAbelVariationV18327
