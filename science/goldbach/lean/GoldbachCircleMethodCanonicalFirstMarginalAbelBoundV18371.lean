import GoldbachCircleMethodCanonicalTargetWeightBranchVariationV18370
import GoldbachCircleMethodEvenTargetWeightedCharacterAverageV18366

/-!
# V1.8.371: canonical first-marginal Abel bound

The free terminal-weight constant in finite Abel summation is generalized and
then instantiated with the source-bound canonical linear target weight from
V1.8.367--V1.8.370.  On either monotone parity-compatible target branch, the
weighted first character marginal is bounded by `4*r*B`.

This uses only the single conductor `r`; no common LCM of all conductors is
introduced.  The cross-turn step, conductor aggregation, and the
target-independent second marginal remain open.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodCanonicalFirstMarginalAbelBoundV18371

open GoldbachCircleMethodCanonicalTargetLinearWeightBindingV18367
open GoldbachCircleMethodCanonicalTargetWeightPiecewiseGeometryV18368
open GoldbachCircleMethodCanonicalTargetWeightBranchVariationV18370
open GoldbachCircleMethodEvenTargetWeightedCharacterAverageV18366

/-- General finite Abel bound with an explicit terminal-weight budget `H`. -/
theorem weighted_complex_sum_norm_le_of_prefix_bound_general
    (a : ℕ → ℂ) (u : ℕ → ℝ) (T : ℕ) (C H V : ℝ)
    (hC : 0 ≤ C) (hT : 1 ≤ T)
    (hprefix : ∀ k : ℕ, k ≤ T → ‖∑ i ∈ Finset.range k, a i‖ ≤ C)
    (hlast : |u (T - 1)| ≤ H)
    (hvariation :
      ∑ i ∈ Finset.range (T - 1), |u (i + 1) - u i| ≤ V) :
    ‖∑ i ∈ Finset.range T, u i • a i‖ ≤ C * (H + V) := by
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
    _ ≤ C * (H + V) := by
      gcongr

/-- The first marginal along consecutive step-two targets has conductor-size
prefix sums. -/
theorem even_target_first_marginal_prefix_norm_le
    (r : ℕ) [NeZero r]
    (chi : DirichletCharacter ℂ r) (hne : chi ≠ 1)
    (A : ℕ) (h2 : Nat.Coprime 2 r) (T : ℕ) :
    ‖∑ i ∈ Finset.range T,
        ((ArithmeticFunction.moebius r : ℤ) : ℂ) *
          chi ((A + 2 * i : ℕ) : ZMod r)‖ ≤ (r : ℝ) := by
  let u : (ZMod r)ˣ := ZMod.unitOfCoprime 2 h2
  have hprefix := affine_first_marginal_prefix_norm_le
    r chi hne (A : ZMod r) u T
  simpa only [Nat.cast_add, Nat.cast_mul, u, ZMod.coe_unitOfCoprime] using hprefix

/-- On a growing canonical target branch, the weighted first character
marginal is at most `4*r*B`. -/
theorem canonical_first_marginal_growing_branch_norm_le
    (r : ℕ) [NeZero r]
    (chi : DirichletCharacter ℂ r) (hne : chi ≠ 1)
    (h2 : Nat.Coprime 2 r)
    (B A T : ℕ) (b : ℝ) (hb : 0 ≤ b)
    (hB : 1 ≤ B) (hBA : B ≤ A)
    (hNonempty : 2 * (B / 2 + 1) ≤ A)
    (hT : 1 ≤ T)
    (hLast : A + 2 * (T - 1) ≤ blockPairTurningTarget B) :
    ‖∑ i ∈ Finset.range T,
        canonicalTargetLinearWeight B (A + 2 * i) b •
          (((ArithmeticFunction.moebius r : ℤ) : ℂ) *
            chi ((A + 2 * i : ℕ) : ZMod r))‖ ≤
      (r : ℝ) * (4 * B) := by
  have hBound := weighted_complex_sum_norm_le_of_prefix_bound_general
    (fun i => ((ArithmeticFunction.moebius r : ℤ) : ℂ) *
      chi ((A + 2 * i : ℕ) : ZMod r))
    (fun i => canonicalTargetLinearWeight B (A + 2 * i) b)
    T (r : ℝ) (2 * B) (2 * B) (Nat.cast_nonneg r) hT
    (fun k _hk => even_target_first_marginal_prefix_norm_le r chi hne A h2 k)
    (by
      have hmem := canonicalTargetLinearWeight_mem_Icc
        B (A + 2 * (T - 1)) b hb (by omega)
      rw [abs_of_nonneg hmem.1]
      exact hmem.2)
    (canonicalTargetLinearWeight_growing_branch_variation_le
      B A T b hb hB hBA hNonempty hT hLast)
  calc
    _ ≤ (r : ℝ) * ((2 : ℝ) * B + 2 * B) := hBound
    _ = (r : ℝ) * (4 * B) := by ring

/-- On a shrinking canonical target branch, the weighted first character
marginal is at most `4*r*B`. -/
theorem canonical_first_marginal_shrinking_branch_norm_le
    (r : ℕ) [NeZero r]
    (chi : DirichletCharacter ℂ r) (hne : chi ≠ 1)
    (h2 : Nat.Coprime 2 r)
    (B A T : ℕ) (b : ℝ) (hb : 0 ≤ b)
    (hB : 1 ≤ B) (hBA : B ≤ A)
    (hTurn : blockPairTurningTarget B ≤ A)
    (hT : 1 ≤ T)
    (hLast : A + 2 * (T - 1) ≤ 2 * B) :
    ‖∑ i ∈ Finset.range T,
        canonicalTargetLinearWeight B (A + 2 * i) b •
          (((ArithmeticFunction.moebius r : ℤ) : ℂ) *
            chi ((A + 2 * i : ℕ) : ZMod r))‖ ≤
      (r : ℝ) * (4 * B) := by
  have hBound := weighted_complex_sum_norm_le_of_prefix_bound_general
    (fun i => ((ArithmeticFunction.moebius r : ℤ) : ℂ) *
      chi ((A + 2 * i : ℕ) : ZMod r))
    (fun i => canonicalTargetLinearWeight B (A + 2 * i) b)
    T (r : ℝ) (2 * B) (2 * B) (Nat.cast_nonneg r) hT
    (fun k _hk => even_target_first_marginal_prefix_norm_le r chi hne A h2 k)
    (by
      have hmem := canonicalTargetLinearWeight_mem_Icc
        B (A + 2 * (T - 1)) b hb (by omega)
      rw [abs_of_nonneg hmem.1]
      exact hmem.2)
    (canonicalTargetLinearWeight_shrinking_branch_variation_le
      B A T b hb hB hBA hTurn hT hLast)
  calc
    _ ≤ (r : ℝ) * ((2 : ℝ) * B + 2 * B) := hBound
    _ = (r : ℝ) * (4 * B) := by ring

end GoldbachCircleMethodCanonicalFirstMarginalAbelBoundV18371
