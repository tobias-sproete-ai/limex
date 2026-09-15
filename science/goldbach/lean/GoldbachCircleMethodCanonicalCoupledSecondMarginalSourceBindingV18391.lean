import GoldbachCircleMethodCanonicalCoupledSecondMarginalAggregationV18390
import GoldbachCircleMethodCanonicalCoupledFirstMarginalActualBindingV18381

/-!
# Goldbach V1.8.391: exact source binding of the off-divisor second marginal

The V1.8.390 companion-first aggregate is identified with the target-first
off-divisor part of the original finite `coupledDiagonal`.  The omitted product
levels `r*l <= 2` are represented by a separate explicit low-frequency sum,
and the original diagonal is decomposed exactly into low plus off-divisor
pieces.

No estimate, convergence argument, or reserve sign is used.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodCanonicalCoupledSecondMarginalSourceBindingV18391

open GoldbachCircleMethodActualFrozenModelCompleteDiagonalV18213
open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodCanonicalCoupledFirstMarginalActualBindingV18381
open GoldbachCircleMethodCanonicalCoupledFirstMarginalAggregationV18378
open GoldbachCircleMethodCanonicalCoupledFirstMarginalSourceBindingV18380
open GoldbachCircleMethodCanonicalCoupledSecondMarginalAbelV18388
open GoldbachCircleMethodCanonicalCoupledSecondMarginalAggregationV18390
open GoldbachCircleMethodCanonicalTargetQuadraticWeightBindingV18385
open GoldbachCircleMethodFiniteResiduePrefixV1866
open GoldbachCircleMethodPairwiseActiveCostAggregationV18318

/-- Exact off-divisor piece of the finite coupled diagonal at a natural target. -/
noncomputable def offDivisorCoupledDiagonalAtNat {Q : ℕ}
    (r : PositiveLevel Q) (v w : ℕ → ℂ) (N : ℕ) : ℂ :=
  ∑ l ∈ offDivisorSecondCarrier r,
    coupledFirstMarginalCoefficient r l v w *
      unitCharacterSum l.val (N : ZMod l.val)

/-- Exact low-frequency complement (`r*l <= 2`) retained outside the
oscillatory pairwise-period estimate. -/
noncomputable def lowFrequencyCoupledDiagonalAtNat {Q : ℕ}
    (r : PositiveLevel Q) (v w : ℕ → ℂ) (N : ℕ) : ℂ :=
  ∑ l ∈ (activeComplementCarrier r).filter
      (fun l => ¬ 2 < r.val * l.val),
    coupledFirstMarginalCoefficient r l v w *
      unitCharacterSum l.val (N : ZMod l.val)

/-- Exact finite partition of the active diagonal into low-frequency and
off-divisor channels. -/
theorem activeCoupledDiagonalAtNat_eq_low_add_off {Q : ℕ}
    (r : PositiveLevel Q) (v w : ℕ → ℂ) (N : ℕ) :
    activeCoupledDiagonalAtNat r v w N =
      lowFrequencyCoupledDiagonalAtNat r v w N +
        offDivisorCoupledDiagonalAtNat r v w N := by
  unfold activeCoupledDiagonalAtNat lowFrequencyCoupledDiagonalAtNat
    offDivisorCoupledDiagonalAtNat offDivisorSecondCarrier
  have hs := Finset.sum_filter_add_sum_filter_not
    (activeComplementCarrier r)
    (fun l : PositiveLevel Q => 2 < r.val * l.val)
    (fun l => coupledFirstMarginalCoefficient r l v w *
      unitCharacterSum l.val (N : ZMod l.val))
  rw [add_comm]
  exact hs.symm

/-- Target-first presentation of the off-divisor second marginal. -/
noncomputable def sourceCoupledSecondMarginalTargetSum {Q : ℕ}
    (r : PositiveLevel Q) (v w : ℕ → ℂ)
    (B A T : ℕ) (b : ℝ) : ℂ :=
  ∑ i ∈ Finset.range T,
    canonicalTargetQuadraticWeight B (A + 2 * i) b •
      (unitCharacterSum r.val ((A + 2 * i : ℕ) : ZMod r.val) *
        offDivisorCoupledDiagonalAtNat r v w (A + 2 * i))

/-- Exact finite exchange of the companion and target sums. -/
theorem canonicalCoupledSecondMarginalAggregate_eq_source
    {Q : ℕ} (r : PositiveLevel Q)
    (v w : ℕ → ℂ) (B A T : ℕ) (b : ℝ) :
    canonicalCoupledSecondMarginalAggregate r v w B A T b =
      sourceCoupledSecondMarginalTargetSum r v w B A T b := by
  unfold canonicalCoupledSecondMarginalAggregate
    canonicalCoupledSecondMarginalTargetSum
    sourceCoupledSecondMarginalTargetSum offDivisorCoupledDiagonalAtNat
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro l _hl
  rw [Algebra.smul_def, Algebra.smul_def]
  ring

/-- The exact source-side off-divisor term inherits the V1.8.390 quartic
budget without any additional estimate. -/
theorem source_coupled_second_marginal_norm_le_quartic {Q : ℕ}
    (r : PositiveLevel Q)
    (v w : ℕ → ℂ) (M : ℝ) (hM : 0 ≤ M)
    (hv : ∀ n, ‖v n‖ ≤ M) (hw : ∀ n, ‖w n‖ ≤ M)
    (B A K S : ℕ) (b : ℝ) (hb : 0 ≤ b)
    (hB : 2 ≤ B) (hBA : B ≤ A)
    (hNonempty : 2 * (B / 2 + 1) ≤ A)
    (hK : 1 ≤ K)
    (hGrowingLast : A + 2 * (K - 1) ≤
      GoldbachCircleMethodCanonicalTargetWeightPiecewiseGeometryV18368.blockPairTurningTarget B)
    (hS : 1 ≤ S)
    (hShrinkingFirst :
      GoldbachCircleMethodCanonicalTargetWeightPiecewiseGeometryV18368.blockPairTurningTarget B ≤
        A + 2 * K)
    (hFinal : A + 2 * K + 2 * (S - 1) ≤ 2 * B) :
    ‖sourceCoupledSecondMarginalTargetSum r v w B A (K + S) b‖ ≤
      2 * (B : ℝ) * (3 + 4 * b) * (Q : ℝ) ^ 4 * M ^ 2 := by
  rw [← canonicalCoupledSecondMarginalAggregate_eq_source]
  exact canonical_coupled_second_marginal_aggregate_norm_le_quartic
    r v w M hM hv hw B A K S b hb hB hBA hNonempty hK
      hGrowingLast hS hShrinkingFirst hFinal

/-- Literal low-frequency target contribution. -/
noncomputable def lowFrequencyCoupledSecondMarginalTargetSum {Q : ℕ}
    (r : PositiveLevel Q) (v w : ℕ → ℂ)
    (B A T : ℕ) (b : ℝ) : ℂ :=
  ∑ i ∈ Finset.range T,
    canonicalTargetQuadraticWeight B (A + 2 * i) b •
      (unitCharacterSum r.val ((A + 2 * i : ℕ) : ZMod r.val) *
        lowFrequencyCoupledDiagonalAtNat r v w (A + 2 * i))

/-- Literal target sum formed from the original unfiltered coupled diagonal. -/
noncomputable def actualCoupledSecondMarginalTargetSum
    {Q K : ℕ} [NeZero K]
    (hK : ∀ q : PositiveLevel Q, q.val ∣ K)
    (r : PositiveLevel Q) (v w : ℕ → ℂ)
    (B A T : ℕ) (b : ℝ) : ℂ :=
  ∑ i ∈ Finset.range T,
    canonicalTargetQuadraticWeight B (A + 2 * i) b •
      (unitCharacterSum r.val ((A + 2 * i : ℕ) : ZMod r.val) *
        coupledDiagonal hK r v w ((A + 2 * i : ℕ) : ZMod K))

/-- The original second marginal is exactly low-frequency plus the controlled
off-divisor source term. -/
theorem actualCoupledSecondMarginalTargetSum_eq_low_add_off
    {Q K : ℕ} [NeZero K]
    (hK : ∀ q : PositiveLevel Q, q.val ∣ K)
    (r : PositiveLevel Q) (v w : ℕ → ℂ)
    (B A T : ℕ) (b : ℝ) :
    actualCoupledSecondMarginalTargetSum hK r v w B A T b =
      lowFrequencyCoupledSecondMarginalTargetSum r v w B A T b +
        sourceCoupledSecondMarginalTargetSum r v w B A T b := by
  unfold actualCoupledSecondMarginalTargetSum
    lowFrequencyCoupledSecondMarginalTargetSum
    sourceCoupledSecondMarginalTargetSum
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [coupledDiagonal_natCast_eq_activeCoupledDiagonalAtNat hK,
    activeCoupledDiagonalAtNat_eq_low_add_off]
  rw [Algebra.smul_def, Algebra.smul_def, Algebra.smul_def]
  ring

end GoldbachCircleMethodCanonicalCoupledSecondMarginalSourceBindingV18391
