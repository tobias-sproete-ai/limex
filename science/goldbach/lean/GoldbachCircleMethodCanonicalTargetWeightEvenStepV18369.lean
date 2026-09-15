import GoldbachCircleMethodCanonicalTargetWeightPiecewiseGeometryV18368

/-!
# V1.8.369: exact even-target steps of the canonical linear weight

The two endpoint regimes from V1.8.368 are advanced by one even target step.
On the growing side exactly two terms enter the one-sided carrier sum.  On the
shrinking side exactly two terms leave it.  Since the source-bound linear
coefficient is twice that sum, this gives exact step identities and the
corresponding monotonicity.

No global total-variation budget, character-average absorption,
exceptional-set estimate, or Goldbach conclusion is asserted.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodCanonicalTargetWeightEvenStepV18369

open GoldbachCircleMethodCanonicalTargetLinearWeightBindingV18367
open GoldbachCircleMethodCanonicalTargetWeightPiecewiseGeometryV18368
open GoldbachCircleMethodExceptionalWeightBoundaryV18128

/-- Adding two points at the top of a nonempty natural interval adds exactly
their two values. -/
theorem sum_Icc_add_two_top
    {M : Type*} [AddCommMonoid M]
    (A U : ℕ) (hAU : A ≤ U) (f : ℕ → M) :
    (∑ n ∈ Finset.Icc A (U + 2), f n) =
      (∑ n ∈ Finset.Icc A U, f n) + f (U + 1) + f (U + 2) := by
  rw [show U + 2 = (U + 1) + 1 by omega,
    Finset.sum_Icc_succ_top (by omega) f,
    Finset.sum_Icc_succ_top (by omega) f]

/-- Removing the two bottom points of a natural interval leaves the interval
starting two positions later. -/
theorem sum_Icc_eq_two_bottom_add
    {M : Type*} [AddCommMonoid M]
    (A U : ℕ) (hAU : A + 1 ≤ U) (f : ℕ → M) :
    (∑ n ∈ Finset.Icc A U, f n) =
      f A + f (A + 1) + ∑ n ∈ Finset.Icc (A + 2) U, f n := by
  have hset : Finset.Icc A U =
      insert A (insert (A + 1) (Finset.Icc (A + 2) U)) := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  rw [hset, Finset.sum_insert, Finset.sum_insert]
  · ac_rfl
  · simp only [Finset.mem_Icc]
    omega
  · simp only [Finset.mem_insert, Finset.mem_Icc]
    omega

/-- Before the turning target, advancing by two adds exactly the next two
one-sided power weights, each doubled by complement symmetry. -/
theorem canonicalTargetLinearWeight_add_two_growing
    (B N : ℕ) (b : ℝ)
    (hB : 1 ≤ B) (hBN : B ≤ N)
    (hNonempty : 2 * (B / 2 + 1) ≤ N)
    (hTurn : N + 2 ≤ blockPairTurningTarget B) :
    canonicalTargetLinearWeight B (N + 2) b =
      canonicalTargetLinearWeight B N b +
        2 * (powerWeight b (N - (B / 2 + 1) + 1) +
          powerWeight b (N - (B / 2 + 1) + 2)) := by
  rw [canonicalTargetLinearWeight_eq_growing_sum B N b hB hBN
      (by omega),
    canonicalTargetLinearWeight_eq_growing_sum B (N + 2) b hB
      (by omega) hTurn]
  have hsub : N + 2 - (B / 2 + 1) = N - (B / 2 + 1) + 2 := by omega
  rw [hsub, sum_Icc_add_two_top (B / 2 + 1)
    (N - (B / 2 + 1)) (by omega) (powerWeight b)]
  ring

/-- The source-bound linear target weight is monotone along even steps on the
growing side. -/
theorem canonicalTargetLinearWeight_mono_growing
    (B N : ℕ) (b : ℝ)
    (hB : 1 ≤ B) (hBN : B ≤ N)
    (hNonempty : 2 * (B / 2 + 1) ≤ N)
    (hTurn : N + 2 ≤ blockPairTurningTarget B) :
    canonicalTargetLinearWeight B N b ≤
      canonicalTargetLinearWeight B (N + 2) b := by
  rw [canonicalTargetLinearWeight_add_two_growing B N b hB hBN hNonempty hTurn]
  have h₁ : 0 ≤ powerWeight b (N - (B / 2 + 1) + 1) :=
    Real.rpow_nonneg (Nat.cast_nonneg _) _
  have h₂ : 0 ≤ powerWeight b (N - (B / 2 + 1) + 2) :=
    Real.rpow_nonneg (Nat.cast_nonneg _) _
  nlinarith

/-- After the turning target, advancing by two removes exactly the current
two bottom weights, each doubled by complement symmetry. -/
theorem canonicalTargetLinearWeight_add_two_shrinking
    (B N : ℕ) (b : ℝ)
    (hB : 1 ≤ B) (hBN : B ≤ N)
    (hTurn : blockPairTurningTarget B ≤ N)
    (hUpper : N + 2 ≤ 2 * B) :
    canonicalTargetLinearWeight B N b =
      canonicalTargetLinearWeight B (N + 2) b +
        2 * (powerWeight b (N - B) + powerWeight b (N - B + 1)) := by
  rw [canonicalTargetLinearWeight_eq_shrinking_sum B N b hB hBN hTurn,
    canonicalTargetLinearWeight_eq_shrinking_sum B (N + 2) b hB
      (by omega) (by omega)]
  have hsub : N + 2 - B = N - B + 2 := by omega
  rw [hsub, sum_Icc_eq_two_bottom_add (N - B) B (by omega)
    (powerWeight b)]
  ring

/-- The source-bound linear target weight is monotone decreasing along even
steps on the shrinking side. -/
theorem canonicalTargetLinearWeight_antitone_shrinking
    (B N : ℕ) (b : ℝ)
    (hB : 1 ≤ B) (hBN : B ≤ N)
    (hTurn : blockPairTurningTarget B ≤ N)
    (hUpper : N + 2 ≤ 2 * B) :
    canonicalTargetLinearWeight B (N + 2) b ≤
      canonicalTargetLinearWeight B N b := by
  rw [canonicalTargetLinearWeight_add_two_shrinking B N b hB hBN hTurn hUpper]
  have h₁ : 0 ≤ powerWeight b (N - B) :=
    Real.rpow_nonneg (Nat.cast_nonneg _) _
  have h₂ : 0 ≤ powerWeight b (N - B + 1) :=
    Real.rpow_nonneg (Nat.cast_nonneg _) _
  nlinarith

end GoldbachCircleMethodCanonicalTargetWeightEvenStepV18369
