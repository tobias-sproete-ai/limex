import GoldbachCircleMethodCanonicalCoupledSecondMarginalTwoBranchV18389
import GoldbachCircleMethodCanonicalCoupledFirstMarginalAggregationV18378

/-!
# Goldbach V1.8.390: Q^4 aggregation of the second coupled marginal

The exact companion coefficient from `coupledDiagonal` is applied to the
source-derived pairwise-period bound of V1.8.389 and summed over the actual
coupled carrier `r*l <= Q`, `Coprime r l`.  The aggregate is bounded by

`2 * B * (3 + 4*b) * Q^4 * M^2`.

No common LCM is used.  This statement is before the remaining active-level
prefactor `r/phi(r)^2` and before reserve absorption.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodCanonicalCoupledSecondMarginalAggregationV18390

open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodCanonicalCoupledFirstMarginalAggregationV18378
open GoldbachCircleMethodCanonicalCoupledSecondMarginalAbelV18388
open GoldbachCircleMethodCanonicalCoupledSecondMarginalTwoBranchV18389
open GoldbachCircleMethodPairwiseActiveCostAggregationV18318

/-- The genuine off-divisor carrier: the original coupled support with the
nonoscillatory product levels `1` and `2` removed explicitly. -/
def offDivisorSecondCarrier {Q : ℕ} (r : PositiveLevel Q) :
    Finset (PositiveLevel Q) :=
  (activeComplementCarrier r).filter (fun l => 2 < r.val * l.val)

/-- Source-normalized sum of all oscillatory one-companion second-marginal
target sums. -/
noncomputable def canonicalCoupledSecondMarginalAggregate {Q : ℕ}
    (r : PositiveLevel Q) (v w : ℕ → ℂ)
    (B A T : ℕ) (b : ℝ) : ℂ :=
  ∑ l ∈ offDivisorSecondCarrier r,
    coupledFirstMarginalCoefficient r l v w *
      canonicalCoupledSecondMarginalTargetSum r.val l.val B A T b

/-- The complete companion aggregation has quartic cutoff cost, with the
quadratic target-variation dependence kept explicit. -/
theorem canonical_coupled_second_marginal_aggregate_norm_le_quartic {Q : ℕ}
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
    ‖canonicalCoupledSecondMarginalAggregate r v w B A (K + S) b‖ ≤
      2 * (B : ℝ) * (3 + 4 * b) * (Q : ℝ) ^ 4 * M ^ 2 := by
  let C : ℝ := 2 * (B : ℝ) * (3 + 4 * b) * (Q : ℝ) ^ 3 * M ^ 2
  have hC : 0 ≤ C := by positivity
  have hterm : ∀ l ∈ offDivisorSecondCarrier r,
      ‖coupledFirstMarginalCoefficient r l v w *
        canonicalCoupledSecondMarginalTargetSum
          r.val l.val B A (K + S) b‖ ≤ C := by
    intro l hl
    have hoff := (Finset.mem_filter.mp hl)
    have hactive := hoff.1
    have hprod : 2 < r.val * l.val := hoff.2
    have hdata := (Finset.mem_filter.mp hactive).2
    have hrl_nat : r.val * l.val ≤ Q := hdata.1
    have hcop : Nat.Coprime r.val l.val := hdata.2
    have hrQ : r.val ≤ Q := (Finset.mem_Icc.mp r.property).2
    have hlQ : l.val ≤ Q := (Finset.mem_Icc.mp l.property).2
    have hphir_nat : r.val.totient ≤ Q := (Nat.totient_le r.val).trans hrQ
    have hphil_nat : l.val.totient ≤ Q := (Nat.totient_le l.val).trans hlQ
    have hrl : ((r.val * l.val : ℕ) : ℝ) ≤ (Q : ℝ) := by
      exact_mod_cast hrl_nat
    have hphir : (r.val.totient : ℝ) ≤ (Q : ℝ) := by
      exact_mod_cast hphir_nat
    have hphil : (l.val.totient : ℝ) ≤ (Q : ℝ) := by
      exact_mod_cast hphil_nat
    have htarget := canonical_coupled_second_marginal_two_branch_norm_le
      r.val l.val hcop hprod B A K S b hb hB hBA hNonempty hK
        hGrowingLast hS hShrinkingFirst hFinal
    have htargetQ :
        ‖canonicalCoupledSecondMarginalTargetSum
          r.val l.val B A (K + S) b‖ ≤
          2 * (B : ℝ) * (3 + 4 * b) * (Q : ℝ) ^ 3 := by
      calc
        _ ≤ (((r.val * l.val : ℕ) : ℝ) *
              ((r.val.totient : ℝ) * (l.val.totient : ℝ))) *
                (2 * ((B : ℝ) * (3 + 4 * b))) := htarget
        _ ≤ ((Q : ℝ) * ((Q : ℝ) * (Q : ℝ))) *
              (2 * ((B : ℝ) * (3 + 4 * b))) := by
          apply mul_le_mul
          · exact mul_le_mul hrl (mul_le_mul hphir hphil (by positivity) (by positivity))
              (by positivity) (by positivity)
          · rfl
          · positivity
          · positivity
        _ = 2 * (B : ℝ) * (3 + 4 * b) * (Q : ℝ) ^ 3 := by ring
    rw [norm_mul]
    calc
      _ ≤ M ^ 2 *
          (2 * (B : ℝ) * (3 + 4 * b) * (Q : ℝ) ^ 3) :=
        mul_le_mul
          (coupledFirstMarginalCoefficient_norm_le r l v w M hM hv hw)
          htargetQ (norm_nonneg _) (by positivity)
      _ = C := by ring
  unfold canonicalCoupledSecondMarginalAggregate
  calc
    _ ≤ ∑ l ∈ offDivisorSecondCarrier r,
        ‖coupledFirstMarginalCoefficient r l v w *
          canonicalCoupledSecondMarginalTargetSum
            r.val l.val B A (K + S) b‖ := norm_sum_le _ _
    _ ≤ ∑ _l ∈ offDivisorSecondCarrier r, C :=
      Finset.sum_le_sum (fun l hl => hterm l hl)
    _ = ((offDivisorSecondCarrier r).card : ℝ) * C := by simp
    _ ≤ (Q : ℝ) * C := by
      exact mul_le_mul_of_nonneg_right
        (by
          exact_mod_cast ((Finset.card_filter_le (activeComplementCarrier r)
            (fun l => 2 < r.val * l.val)).trans
              (activeComplementCarrier_card_le_cutoff r))) hC
    _ = 2 * (B : ℝ) * (3 + 4 * b) * (Q : ℝ) ^ 4 * M ^ 2 := by
      dsimp [C]
      ring

end GoldbachCircleMethodCanonicalCoupledSecondMarginalAggregationV18390
