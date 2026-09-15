import GoldbachCircleMethodCanonicalCoupledFirstMarginalParityCompleteV18379

/-!
# Goldbach V1.8.380: exact finite source binding

The aggregate controlled in V1.8.378/379 is identified with the target sum of
the active character factor times the complete finite coupled companion
diagonal.  This is a finite exchange of sums; no estimate or convergence
argument is used.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodCanonicalCoupledFirstMarginalSourceBindingV18380

open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodCanonicalCoupledFirstMarginalAbelV18376
open GoldbachCircleMethodCanonicalCoupledFirstMarginalAggregationV18378
open GoldbachCircleMethodCanonicalTargetLinearWeightBindingV18367
open GoldbachCircleMethodFiniteResiduePrefixV1866
open GoldbachCircleMethodPairwiseActiveCostAggregationV18318

/-- Exact finite coupled diagonal at a natural target, restricted only by the
original product/coprimality carrier. -/
noncomputable def activeCoupledDiagonalAtNat {Q : ℕ}
    (r : PositiveLevel Q) (v w : ℕ → ℂ) (N : ℕ) : ℂ :=
  ∑ l ∈ activeComplementCarrier r,
    coupledFirstMarginalCoefficient r l v w *
      unitCharacterSum l.val (N : ZMod l.val)

/-- Target-side presentation of the coupled first marginal before exchanging
the target and companion sums. -/
noncomputable def sourceCoupledFirstMarginalTargetSum {Q : ℕ}
    (r : PositiveLevel Q) (chi : DirichletCharacter ℂ r.val)
    (v w : ℕ → ℂ) (B A T : ℕ) (b : ℝ) : ℂ :=
  ∑ i ∈ Finset.range T,
    canonicalTargetLinearWeight B (A + 2 * i) b •
      ((((ArithmeticFunction.moebius r.val : ℤ) : ℂ) *
          chi ((A + 2 * i : ℕ) : ZMod r.val)) *
        activeCoupledDiagonalAtNat r v w (A + 2 * i))

/-- Exact source binding: the companion-first aggregate is the same finite
sum as the target-first coupled diagonal expression. -/
theorem canonicalCoupledFirstMarginalAggregate_eq_source
    {Q : ℕ} (r : PositiveLevel Q)
    (chi : DirichletCharacter ℂ r.val)
    (v w : ℕ → ℂ) (B A T : ℕ) (b : ℝ) :
    canonicalCoupledFirstMarginalAggregate r chi v w B A T b =
      sourceCoupledFirstMarginalTargetSum r chi v w B A T b := by
  unfold canonicalCoupledFirstMarginalAggregate
    canonicalCoupledFirstMarginalTargetSum
    sourceCoupledFirstMarginalTargetSum activeCoupledDiagonalAtNat
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro l _hl
  rw [Algebra.smul_def, Algebra.smul_def]
  ring

end GoldbachCircleMethodCanonicalCoupledFirstMarginalSourceBindingV18380
