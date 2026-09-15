import GoldbachCircleMethodCanonicalQuadraticEvenStepV18386

/-!
# Goldbach V1.8.387: branch variation of the canonical quadratic weight

The source-derived one-step estimates from V1.8.386 are summed along each
parity-compatible branch.  No monotonicity is assumed: the total variation is
controlled directly by the number of even steps.  The resulting bound is
`B * (2 + 4*b)` on either side of the canonical turning target.

No character sum, Abel transport, modulus aggregation, reserve absorption, or
Goldbach conclusion is used.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodCanonicalQuadraticBranchVariationV18387

open GoldbachCircleMethodCanonicalQuadraticEvenStepV18386
open GoldbachCircleMethodCanonicalTargetQuadraticWeightBindingV18385
open GoldbachCircleMethodCanonicalTargetWeightPiecewiseGeometryV18368

/-- The growing parity branch has total quadratic-weight variation at most
`B * (2 + 4*b)`. -/
theorem canonicalTargetQuadraticWeight_growing_branch_variation_le
    (B A T : ℕ) (b : ℝ)
    (hB : 2 ≤ B) (hBA : B ≤ A) (hb : 0 ≤ b)
    (hNonempty : 2 * (B / 2 + 1) ≤ A)
    (hLast : A + 2 * (T - 1) ≤ blockPairTurningTarget B) :
    (∑ i ∈ Finset.range (T - 1),
        |canonicalTargetQuadraticWeight B (A + 2 * (i + 1)) b -
          canonicalTargetQuadraticWeight B (A + 2 * i) b|) ≤
      (B : ℝ) * (2 + 4 * b) := by
  have hstep : ∀ i ∈ Finset.range (T - 1),
      |canonicalTargetQuadraticWeight B (A + 2 * (i + 1)) b -
        canonicalTargetQuadraticWeight B (A + 2 * i) b| ≤ 2 + 4 * b := by
    intro i hi
    have hiBound : i + 1 ≤ T - 1 := by
      have hi' := Finset.mem_range.mp hi
      omega
    have hstepBound : A + 2 * (i + 1) ≤ A + 2 * (T - 1) :=
      Nat.add_le_add_left (Nat.mul_le_mul_left 2 hiBound) A
    have hTurni : A + 2 * i + 2 ≤ blockPairTurningTarget B := by
      have hEq : A + 2 * i + 2 = A + 2 * (i + 1) := by omega
      rw [hEq]
      exact hstepBound.trans hLast
    have hEq : A + 2 * (i + 1) = A + 2 * i + 2 := by omega
    rw [hEq]
    exact canonicalTargetQuadraticWeight_add_two_growing_abs_le
      B (A + 2 * i) b hB (by omega) hb (by omega) hTurni
  calc
    _ ≤ ∑ _i ∈ Finset.range (T - 1), (2 + 4 * b) := by
      exact Finset.sum_le_sum hstep
    _ = ((T - 1 : ℕ) : ℝ) * (2 + 4 * b) := by
      simp
      ring
    _ ≤ (B : ℝ) * (2 + 4 * b) := by
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast (show T - 1 ≤ B by
          simp only [blockPairTurningTarget] at hLast
          omega)
      · positivity

/-- The shrinking parity branch has total quadratic-weight variation at most
`B * (2 + 4*b)`. -/
theorem canonicalTargetQuadraticWeight_shrinking_branch_variation_le
    (B A T : ℕ) (b : ℝ)
    (hB : 2 ≤ B) (hBA : B ≤ A) (hb : 0 ≤ b)
    (hTurn : blockPairTurningTarget B ≤ A)
    (hLast : A + 2 * (T - 1) ≤ 2 * B) :
    (∑ i ∈ Finset.range (T - 1),
        |canonicalTargetQuadraticWeight B (A + 2 * (i + 1)) b -
          canonicalTargetQuadraticWeight B (A + 2 * i) b|) ≤
      (B : ℝ) * (2 + 4 * b) := by
  have hstep : ∀ i ∈ Finset.range (T - 1),
      |canonicalTargetQuadraticWeight B (A + 2 * (i + 1)) b -
        canonicalTargetQuadraticWeight B (A + 2 * i) b| ≤ 2 + 4 * b := by
    intro i hi
    have hiBound : i + 1 ≤ T - 1 := by
      have hi' := Finset.mem_range.mp hi
      omega
    have hstepBound : A + 2 * (i + 1) ≤ A + 2 * (T - 1) :=
      Nat.add_le_add_left (Nat.mul_le_mul_left 2 hiBound) A
    have hUpperi : A + 2 * i + 2 ≤ 2 * B := by
      have hEq : A + 2 * i + 2 = A + 2 * (i + 1) := by omega
      rw [hEq]
      exact hstepBound.trans hLast
    have hEq : A + 2 * (i + 1) = A + 2 * i + 2 := by omega
    rw [hEq]
    exact canonicalTargetQuadraticWeight_add_two_shrinking_abs_le
      B (A + 2 * i) b hB (by omega) hb (by omega) hUpperi
  calc
    _ ≤ ∑ _i ∈ Finset.range (T - 1), (2 + 4 * b) := by
      exact Finset.sum_le_sum hstep
    _ = ((T - 1 : ℕ) : ℝ) * (2 + 4 * b) := by
      simp
      ring
    _ ≤ (B : ℝ) * (2 + 4 * b) := by
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast (show T - 1 ≤ B by omega)
      · positivity

end GoldbachCircleMethodCanonicalQuadraticBranchVariationV18387
