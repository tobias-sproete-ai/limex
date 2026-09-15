import GoldbachCircleMethodCanonicalCoupledFirstMarginalAggregationV18378

/-!
# Goldbach V1.8.379: parity-complete aggregate first-marginal bound

V1.8.378 proves the source-normalized aggregate bound when multiplication by
two is invertible modulo the active conductor.  The complementary branch is
not an analytic loss: for an even conductor and even targets the Dirichlet
character vanishes pointwise.  This module closes the exhaustive parity split.

The result still concerns only the first coupled marginal.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodCanonicalCoupledFirstMarginalParityCompleteV18379

open GoldbachCircleMethodCanonicalCoupledFirstMarginalAbelV18376
open GoldbachCircleMethodCanonicalCoupledFirstMarginalAggregationV18378
open GoldbachCircleMethodCoupledFirstMarginalParityDichotomyV18374
open GoldbachCircleMethodPairwiseActiveCostAggregationV18318

/-- If the active conductor and the initial target are even, every target in
the consecutive-even progression has zero character factor. -/
theorem canonicalCoupledFirstMarginalAggregate_eq_zero_of_even_conductor
    {Q : ℕ} (r : GoldbachCircleMethodBoundedConductorReindexV18117.PositiveLevel Q)
    (chi : DirichletCharacter ℂ r.val)
    (v w : ℕ → ℂ) (B A T : ℕ) (b : ℝ)
    (hA : Even A) (hr : Even r.val) :
    canonicalCoupledFirstMarginalAggregate r chi v w B A T b = 0 := by
  unfold canonicalCoupledFirstMarginalAggregate
  apply Finset.sum_eq_zero
  intro l hl
  apply mul_eq_zero_of_right
  unfold canonicalCoupledFirstMarginalTargetSum
  apply Finset.sum_eq_zero
  intro i hi
  have htarget : Even (A + 2 * i) := by
    obtain ⟨a, ha⟩ := hA
    exact ⟨a + i, by omega⟩
  rw [coupled_first_marginal_eq_zero_of_even_conductor
    r.val l.val chi (A + 2 * i) htarget hr]
  simp

/-- Exhaustive conductor-parity result: on even target progressions the
aggregate is either identically zero or satisfies the stronger cubic bound.
No parity branch is omitted. -/
theorem canonical_coupled_first_marginal_aggregate_parity_complete {Q : ℕ}
    (r : GoldbachCircleMethodBoundedConductorReindexV18117.PositiveLevel Q)
    (chi : DirichletCharacter ℂ r.val) (hne : chi ≠ 1)
    (v w : ℕ → ℂ) (M : ℝ) (hM : 0 ≤ M)
    (hv : ∀ n, ‖v n‖ ≤ M) (hw : ∀ n, ‖w n‖ ≤ M)
    (B A K S : ℕ) (b : ℝ) (hb : 0 ≤ b) (hA : Even A)
    (hB : 1 ≤ B) (hBA : B ≤ A)
    (hNonempty : 2 * (B / 2 + 1) ≤ A)
    (hK : 1 ≤ K)
    (hGrowingLast : A + 2 * (K - 1) ≤
      GoldbachCircleMethodCanonicalTargetWeightPiecewiseGeometryV18368.blockPairTurningTarget B)
    (hS : 1 ≤ S)
    (hShrinkingFirst :
      GoldbachCircleMethodCanonicalTargetWeightPiecewiseGeometryV18368.blockPairTurningTarget B ≤
        A + 2 * K)
    (hFinal : A + 2 * K + 2 * (S - 1) ≤ 2 * B) :
    canonicalCoupledFirstMarginalAggregate r chi v w B A (K + S) b = 0 ∨
      ‖canonicalCoupledFirstMarginalAggregate r chi v w B A (K + S) b‖ ≤
        8 * (B : ℝ) * (Q : ℝ) ^ 3 * M ^ 2 := by
  by_cases hr : Even r.val
  · exact Or.inl
      (canonicalCoupledFirstMarginalAggregate_eq_zero_of_even_conductor
        r chi v w B A (K + S) b hA hr)
  · exact Or.inr
      (canonical_coupled_first_marginal_aggregate_norm_le_cubic
        r chi hne (coprime_two_of_not_even r.val hr)
        v w M hM hv hw B A K S b hb hB hBA hNonempty hK
          hGrowingLast hS hShrinkingFirst hFinal)

end GoldbachCircleMethodCanonicalCoupledFirstMarginalParityCompleteV18379
