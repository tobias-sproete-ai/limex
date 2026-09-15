import GoldbachCircleMethodCanonicalTargetWeightEvenStepV18369

/-!
# V1.8.370: branchwise total variation of the canonical target weight

The exact even-target monotonicity from V1.8.369 is converted into a
telescoping total-variation identity on each side of the turning target.  The
canonical weight is also bounded between zero and `2*B`, so either monotone
branch has total variation at most `2*B`.

This is a source-bound replacement for the free branch-variation parameter in
V1.8.366.  The crossing step between the two parity-compatible branches and
the target-independent second marginal remain open.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodCanonicalTargetWeightBranchVariationV18370

open GoldbachCircleMethodBlockPairCarrierV18227
open GoldbachCircleMethodCanonicalTargetLinearWeightBindingV18367
open GoldbachCircleMethodCanonicalTargetWeightPiecewiseGeometryV18368
open GoldbachCircleMethodCanonicalTargetWeightEvenStepV18369
open GoldbachCircleMethodExceptionalWeightBoundaryV18128
open GoldbachCircleMethodLogCutoffPresieveBindingV18120
open GoldbachCircleMethodRemovedConvolutionNormV18123

/-- Total variation of a finite nondecreasing real sequence telescopes. -/
theorem sum_abs_forward_diff_eq_last_sub_first_of_mono
    (u : ℕ → ℝ) (T : ℕ) (hT : 1 ≤ T)
    (hmono : ∀ i : ℕ, i + 1 < T → u i ≤ u (i + 1)) :
    (∑ i ∈ Finset.range (T - 1), |u (i + 1) - u i|) =
      u (T - 1) - u 0 := by
  calc
    (∑ i ∈ Finset.range (T - 1), |u (i + 1) - u i|) =
        ∑ i ∈ Finset.range (T - 1), (u (i + 1) - u i) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [abs_of_nonneg]
      exact sub_nonneg.mpr (hmono i (by
        have hi' := Finset.mem_range.mp hi
        omega))
    _ = u (T - 1) - u 0 := Finset.sum_range_sub u (T - 1)

/-- Total variation of a finite nonincreasing real sequence telescopes. -/
theorem sum_abs_forward_diff_eq_first_sub_last_of_antitone
    (u : ℕ → ℝ) (T : ℕ) (hT : 1 ≤ T)
    (hanti : ∀ i : ℕ, i + 1 < T → u (i + 1) ≤ u i) :
    (∑ i ∈ Finset.range (T - 1), |u (i + 1) - u i|) =
      u 0 - u (T - 1) := by
  calc
    (∑ i ∈ Finset.range (T - 1), |u (i + 1) - u i|) =
        ∑ i ∈ Finset.range (T - 1), (u i - u (i + 1)) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [abs_sub_comm, abs_of_nonneg]
      exact sub_nonneg.mpr (hanti i (by
        have hi' := Finset.mem_range.mp hi
        omega))
    _ = u 0 - u (T - 1) := Finset.sum_range_sub' u (T - 1)

/-- The source-bound canonical linear target weight is nonnegative and at
most twice the source scale. -/
theorem canonicalTargetLinearWeight_mem_Icc
    (B N : ℕ) (b : ℝ) (hb : 0 ≤ b) (hBN : B ≤ N) :
    canonicalTargetLinearWeight B N b ∈ Set.Icc (0 : ℝ) (2 * B) := by
  rw [canonicalTargetLinearWeight_eq_two_mul_sum B N b hBN]
  constructor
  · have hsum : 0 ≤
        ∑ n ∈ pairFirstCarrier (blockCarrier B) N, powerWeight b n := by
      apply Finset.sum_nonneg
      intro n _hn
      exact Real.rpow_nonneg (Nat.cast_nonneg n) _
    positivity
  · calc
      2 * (∑ n ∈ pairFirstCarrier (blockCarrier B) N, powerWeight b n) ≤
          2 * (∑ _n ∈ pairFirstCarrier (blockCarrier B) N, (1 : ℝ)) := by
        gcongr with n hn
        have hnBlock : n ∈ blockCarrier B := (Finset.mem_filter.mp hn).1
        have hw := power_weight_abs_le_one B n b hb hnBlock
        exact (le_abs_self (powerWeight b n)).trans hw
      _ = 2 * (((pairFirstCarrier (blockCarrier B) N).card : ℕ) : ℝ) := by simp
      _ ≤ 2 * (((blockCarrier B).card : ℕ) : ℝ) := by
        exact_mod_cast Nat.mul_le_mul_left 2 (Finset.card_filter_le _ _)
      _ ≤ 2 * B := by
        exact_mod_cast Nat.mul_le_mul_left 2 (block_carrier_card_le B)

/-- Exact total variation on a growing parity-compatible even-target branch. -/
theorem canonicalTargetLinearWeight_growing_branch_variation_eq
    (B A T : ℕ) (b : ℝ)
    (hB : 1 ≤ B) (hBA : B ≤ A)
    (hNonempty : 2 * (B / 2 + 1) ≤ A)
    (hT : 1 ≤ T)
    (hLast : A + 2 * (T - 1) ≤ blockPairTurningTarget B) :
    (∑ i ∈ Finset.range (T - 1),
        |canonicalTargetLinearWeight B (A + 2 * (i + 1)) b -
          canonicalTargetLinearWeight B (A + 2 * i) b|) =
      canonicalTargetLinearWeight B (A + 2 * (T - 1)) b -
        canonicalTargetLinearWeight B A b := by
  let u : ℕ → ℝ := fun i => canonicalTargetLinearWeight B (A + 2 * i) b
  have hmono : ∀ i : ℕ, i + 1 < T → u i ≤ u (i + 1) := by
    intro i hi
    dsimp [u]
    have hiBound : i + 1 ≤ T - 1 := by omega
    have hstepBound : A + 2 * (i + 1) ≤ A + 2 * (T - 1) :=
      Nat.add_le_add_left (Nat.mul_le_mul_left 2 hiBound) A
    have hTurni : A + 2 * i + 2 ≤ blockPairTurningTarget B := by
      have hEq : A + 2 * i + 2 = A + 2 * (i + 1) := by omega
      rw [hEq]
      exact hstepBound.trans hLast
    have hstep := canonicalTargetLinearWeight_mono_growing
      B (A + 2 * i) b hB (by omega) (by omega) hTurni
    have hEq : A + 2 * (i + 1) = A + 2 * i + 2 := by omega
    rw [hEq]
    exact hstep
  simpa only [u, Nat.mul_zero, Nat.add_zero] using
    sum_abs_forward_diff_eq_last_sub_first_of_mono u T hT hmono

/-- The growing-branch variation is bounded by `2*B`, independently of its
number of even targets. -/
theorem canonicalTargetLinearWeight_growing_branch_variation_le
    (B A T : ℕ) (b : ℝ) (hb : 0 ≤ b)
    (hB : 1 ≤ B) (hBA : B ≤ A)
    (hNonempty : 2 * (B / 2 + 1) ≤ A)
    (hT : 1 ≤ T)
    (hLast : A + 2 * (T - 1) ≤ blockPairTurningTarget B) :
    (∑ i ∈ Finset.range (T - 1),
        |canonicalTargetLinearWeight B (A + 2 * (i + 1)) b -
          canonicalTargetLinearWeight B (A + 2 * i) b|) ≤ 2 * B := by
  rw [canonicalTargetLinearWeight_growing_branch_variation_eq
    B A T b hB hBA hNonempty hT hLast]
  have hTop := (canonicalTargetLinearWeight_mem_Icc
    B (A + 2 * (T - 1)) b hb (by omega)).2
  have hBase := (canonicalTargetLinearWeight_mem_Icc B A b hb hBA).1
  linarith

/-- Exact total variation on a shrinking parity-compatible even-target branch. -/
theorem canonicalTargetLinearWeight_shrinking_branch_variation_eq
    (B A T : ℕ) (b : ℝ)
    (hB : 1 ≤ B) (hBA : B ≤ A)
    (hTurn : blockPairTurningTarget B ≤ A)
    (hT : 1 ≤ T)
    (hLast : A + 2 * (T - 1) ≤ 2 * B) :
    (∑ i ∈ Finset.range (T - 1),
        |canonicalTargetLinearWeight B (A + 2 * (i + 1)) b -
          canonicalTargetLinearWeight B (A + 2 * i) b|) =
      canonicalTargetLinearWeight B A b -
        canonicalTargetLinearWeight B (A + 2 * (T - 1)) b := by
  let u : ℕ → ℝ := fun i => canonicalTargetLinearWeight B (A + 2 * i) b
  have hanti : ∀ i : ℕ, i + 1 < T → u (i + 1) ≤ u i := by
    intro i hi
    dsimp [u]
    have hiBound : i + 1 ≤ T - 1 := by omega
    have hstepBound : A + 2 * (i + 1) ≤ A + 2 * (T - 1) :=
      Nat.add_le_add_left (Nat.mul_le_mul_left 2 hiBound) A
    have hUpperi : A + 2 * i + 2 ≤ 2 * B := by
      have hEq : A + 2 * i + 2 = A + 2 * (i + 1) := by omega
      rw [hEq]
      exact hstepBound.trans hLast
    have hstep := canonicalTargetLinearWeight_antitone_shrinking
      B (A + 2 * i) b hB (by omega) (by omega) hUpperi
    have hEq : A + 2 * (i + 1) = A + 2 * i + 2 := by omega
    rw [hEq]
    exact hstep
  simpa only [u, Nat.mul_zero, Nat.add_zero] using
    sum_abs_forward_diff_eq_first_sub_last_of_antitone u T hT hanti

/-- The shrinking-branch variation is bounded by `2*B`, independently of its
number of even targets. -/
theorem canonicalTargetLinearWeight_shrinking_branch_variation_le
    (B A T : ℕ) (b : ℝ) (hb : 0 ≤ b)
    (hB : 1 ≤ B) (hBA : B ≤ A)
    (hTurn : blockPairTurningTarget B ≤ A)
    (hT : 1 ≤ T)
    (hLast : A + 2 * (T - 1) ≤ 2 * B) :
    (∑ i ∈ Finset.range (T - 1),
        |canonicalTargetLinearWeight B (A + 2 * (i + 1)) b -
          canonicalTargetLinearWeight B (A + 2 * i) b|) ≤ 2 * B := by
  rw [canonicalTargetLinearWeight_shrinking_branch_variation_eq
    B A T b hB hBA hTurn hT hLast]
  have hTop := (canonicalTargetLinearWeight_mem_Icc B A b hb hBA).2
  have hLastNonneg := (canonicalTargetLinearWeight_mem_Icc
    B (A + 2 * (T - 1)) b hb (by omega)).1
  linarith

end GoldbachCircleMethodCanonicalTargetWeightBranchVariationV18370
