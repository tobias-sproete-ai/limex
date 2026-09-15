import GoldbachCircleMethodCanonicalCoupledSecondMarginalAbelV18388

/-!
# Goldbach V1.8.389: two-branch coupled second-marginal bound

The canonical even-target range is split across the turning target.  Combining
the two source-derived V1.8.388 Abel estimates gives the full one-pair cost

`2 * (r*l) * phi(r) * phi(l) * B * (3 + 4*b)`.

Level aggregation and source normalization remain separate obligations.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodCanonicalCoupledSecondMarginalTwoBranchV18389

open GoldbachCircleMethodCanonicalCoupledSecondMarginalAbelV18388
open GoldbachCircleMethodCanonicalTargetWeightPiecewiseGeometryV18368

/-- Exact split into two consecutive parity-compatible target ranges. -/
theorem canonicalCoupledSecondMarginalTargetSum_add
    (r l : ℕ) [NeZero r] [NeZero l]
    (B A K S : ℕ) (b : ℝ) :
    canonicalCoupledSecondMarginalTargetSum r l B A (K + S) b =
      canonicalCoupledSecondMarginalTargetSum r l B A K b +
        canonicalCoupledSecondMarginalTargetSum r l B (A + 2 * K) S b := by
  unfold canonicalCoupledSecondMarginalTargetSum
  rw [Finset.sum_range_add]
  congr 1
  apply Finset.sum_congr rfl
  intro i _hi
  have htarget : A + 2 * (K + i) = A + 2 * K + 2 * i := by omega
  rw [htarget]

/-- Full one-pair estimate across the canonical turning point. -/
theorem canonical_coupled_second_marginal_two_branch_norm_le
    (r l : ℕ) [NeZero r] [NeZero l]
    (hcop : Nat.Coprime r l) (hprod : 2 < r * l)
    (B A K S : ℕ) (b : ℝ) (hb : 0 ≤ b)
    (hB : 2 ≤ B) (hBA : B ≤ A)
    (hNonempty : 2 * (B / 2 + 1) ≤ A)
    (hK : 1 ≤ K)
    (hGrowingLast : A + 2 * (K - 1) ≤ blockPairTurningTarget B)
    (hS : 1 ≤ S)
    (hShrinkingFirst : blockPairTurningTarget B ≤ A + 2 * K)
    (hFinal : A + 2 * K + 2 * (S - 1) ≤ 2 * B) :
    ‖canonicalCoupledSecondMarginalTargetSum r l B A (K + S) b‖ ≤
      (((r * l : ℕ) : ℝ) *
        ((r.totient : ℝ) * (l.totient : ℝ))) *
          (2 * ((B : ℝ) * (3 + 4 * b))) := by
  rw [canonicalCoupledSecondMarginalTargetSum_add r l B A K S b]
  calc
    _ ≤ ‖canonicalCoupledSecondMarginalTargetSum r l B A K b‖ +
          ‖canonicalCoupledSecondMarginalTargetSum
            r l B (A + 2 * K) S b‖ := norm_add_le _ _
    _ ≤ (((r * l : ℕ) : ℝ) *
            ((r.totient : ℝ) * (l.totient : ℝ))) *
              ((B : ℝ) * (3 + 4 * b)) +
          (((r * l : ℕ) : ℝ) *
            ((r.totient : ℝ) * (l.totient : ℝ))) *
              ((B : ℝ) * (3 + 4 * b)) := by
      apply add_le_add
      · exact canonical_coupled_second_marginal_growing_branch_norm_le
          r l hcop hprod B A K b hb hB hBA hNonempty hK hGrowingLast
      · exact canonical_coupled_second_marginal_shrinking_branch_norm_le
          r l hcop hprod B (A + 2 * K) S b hb hB (by omega)
            hShrinkingFirst hS hFinal
    _ = (((r * l : ℕ) : ℝ) *
        ((r.totient : ℝ) * (l.totient : ℝ))) *
          (2 * ((B : ℝ) * (3 + 4 * b))) := by ring

end GoldbachCircleMethodCanonicalCoupledSecondMarginalTwoBranchV18389
