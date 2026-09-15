import GoldbachCircleMethodCanonicalCoupledFirstMarginalSourceBindingV18380
import GoldbachCircleMethodActualFrozenModelCompleteDiagonalV18213

/-!
# Goldbach V1.8.381: binding to the original coupled diagonal

The finite active-carrier diagonal introduced for the target-average argument
is proved definitionally equal to the original `coupledDiagonal` from
V1.8.213 at a natural target.  The V1.8.380 source sum is then rewritten
without changing its target weight, product cutoff, or character factor.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodCanonicalCoupledFirstMarginalActualBindingV18381

open GoldbachCircleMethodActualFrozenModelCompleteDiagonalV18213
open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodCanonicalCoupledFirstMarginalSourceBindingV18380
open GoldbachCircleMethodCanonicalTargetLinearWeightBindingV18367
open GoldbachCircleMethodPairwiseActiveCostAggregationV18318

/-- The filtered finite diagonal is exactly the original conditional finite
sum when evaluated at the image of a natural target. -/
theorem coupledDiagonal_natCast_eq_activeCoupledDiagonalAtNat
    {Q K : ℕ} [NeZero K]
    (hK : ∀ q : PositiveLevel Q, q.val ∣ K)
    (r : PositiveLevel Q) (v w : ℕ → ℂ) (N : ℕ) :
    coupledDiagonal hK r v w (N : ZMod K) =
      activeCoupledDiagonalAtNat r v w N := by
  unfold coupledDiagonal activeCoupledDiagonalAtNat
    GoldbachCircleMethodCanonicalCoupledFirstMarginalAggregationV18378.coupledFirstMarginalCoefficient
    activeComplementCarrier
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro l _hl
  by_cases hactive : r.val * l.val ≤ Q ∧ Nat.Coprime r.val l.val
  · simp only [hactive, map_natCast]
    ring_nf
  · simp only [hactive, if_false]

/-- Literal target sum formed from the original V1.8.213 coupled diagonal. -/
noncomputable def actualCoupledFirstMarginalTargetSum
    {Q K : ℕ} [NeZero K]
    (hK : ∀ q : PositiveLevel Q, q.val ∣ K)
    (r : PositiveLevel Q) (chi : DirichletCharacter ℂ r.val)
    (v w : ℕ → ℂ) (B A T : ℕ) (b : ℝ) : ℂ :=
  ∑ i ∈ Finset.range T,
    canonicalTargetLinearWeight B (A + 2 * i) b •
      ((((ArithmeticFunction.moebius r.val : ℤ) : ℂ) *
          chi ((A + 2 * i : ℕ) : ZMod r.val)) *
        coupledDiagonal hK r v w ((A + 2 * i : ℕ) : ZMod K))

/-- The source presentation from V1.8.380 is exactly the target average of
the original coupled diagonal. -/
theorem sourceCoupledFirstMarginalTargetSum_eq_actual
    {Q K : ℕ} [NeZero K]
    (hK : ∀ q : PositiveLevel Q, q.val ∣ K)
    (r : PositiveLevel Q) (chi : DirichletCharacter ℂ r.val)
    (v w : ℕ → ℂ) (B A T : ℕ) (b : ℝ) :
    sourceCoupledFirstMarginalTargetSum r chi v w B A T b =
      actualCoupledFirstMarginalTargetSum hK r chi v w B A T b := by
  unfold sourceCoupledFirstMarginalTargetSum actualCoupledFirstMarginalTargetSum
  apply Finset.sum_congr rfl
  intro i _hi
  rw [coupledDiagonal_natCast_eq_activeCoupledDiagonalAtNat hK]

/-- End-to-end exact binding of the controlled aggregate to the original
V1.8.213 diagonal target average. -/
theorem canonicalCoupledFirstMarginalAggregate_eq_actual
    {Q K : ℕ} [NeZero K]
    (hK : ∀ q : PositiveLevel Q, q.val ∣ K)
    (r : PositiveLevel Q) (chi : DirichletCharacter ℂ r.val)
    (v w : ℕ → ℂ) (B A T : ℕ) (b : ℝ) :
    GoldbachCircleMethodCanonicalCoupledFirstMarginalAggregationV18378.canonicalCoupledFirstMarginalAggregate
        r chi v w B A T b =
      actualCoupledFirstMarginalTargetSum hK r chi v w B A T b := by
  rw [GoldbachCircleMethodCanonicalCoupledFirstMarginalSourceBindingV18380.canonicalCoupledFirstMarginalAggregate_eq_source]
  exact sourceCoupledFirstMarginalTargetSum_eq_actual hK r chi v w B A T b

end GoldbachCircleMethodCanonicalCoupledFirstMarginalActualBindingV18381
