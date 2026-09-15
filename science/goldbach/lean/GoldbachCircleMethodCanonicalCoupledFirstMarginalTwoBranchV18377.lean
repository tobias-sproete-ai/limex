import GoldbachCircleMethodCanonicalCoupledFirstMarginalAbelV18376

/-!
# Goldbach V1.8.377: two-branch coupled first-marginal bound

The canonical target range is split exactly at its turning point.  Combining
the two V1.8.376 branch estimates gives the full one-companion boundary cost
`8 * B * (r*l) * phi(l)`.

Companion aggregation and source normalization remain separate obligations.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodCanonicalCoupledFirstMarginalTwoBranchV18377

open GoldbachCircleMethodCanonicalCoupledFirstMarginalAbelV18376
open GoldbachCircleMethodCanonicalTargetWeightPiecewiseGeometryV18368

/-- Exact split of the coupled target sum into parity-compatible ranges. -/
theorem canonicalCoupledFirstMarginalTargetSum_add
    (r l : ℕ) [NeZero r] [NeZero l]
    (chi : DirichletCharacter ℂ r)
    (B A K S : ℕ) (b : ℝ) :
    canonicalCoupledFirstMarginalTargetSum r l chi B A (K + S) b =
      canonicalCoupledFirstMarginalTargetSum r l chi B A K b +
        canonicalCoupledFirstMarginalTargetSum r l chi B (A + 2 * K) S b := by
  unfold canonicalCoupledFirstMarginalTargetSum
  rw [Finset.sum_range_add]
  congr 1
  apply Finset.sum_congr rfl
  intro i _hi
  have htarget : A + 2 * (K + i) = A + 2 * K + 2 * i := by omega
  rw [htarget]

/-- Full one-companion estimate across the canonical turning point. -/
theorem canonical_coupled_first_marginal_two_branch_norm_le
    (r l : ℕ) [NeZero r] [NeZero l]
    (hcop : Nat.Coprime r l)
    (chi : DirichletCharacter ℂ r) (hne : chi ≠ 1)
    (h2 : Nat.Coprime 2 r)
    (B A K S : ℕ) (b : ℝ) (hb : 0 ≤ b)
    (hB : 1 ≤ B) (hBA : B ≤ A)
    (hNonempty : 2 * (B / 2 + 1) ≤ A)
    (hK : 1 ≤ K)
    (hGrowingLast : A + 2 * (K - 1) ≤ blockPairTurningTarget B)
    (hS : 1 ≤ S)
    (hShrinkingFirst : blockPairTurningTarget B ≤ A + 2 * K)
    (hFinal : A + 2 * K + 2 * (S - 1) ≤ 2 * B) :
    ‖canonicalCoupledFirstMarginalTargetSum r l chi B A (K + S) b‖ ≤
      (((r * l : ℕ) : ℝ) * (l.totient : ℝ)) * (8 * B) := by
  rw [canonicalCoupledFirstMarginalTargetSum_add r l chi B A K S b]
  calc
    _ ≤ ‖canonicalCoupledFirstMarginalTargetSum r l chi B A K b‖ +
          ‖canonicalCoupledFirstMarginalTargetSum
            r l chi B (A + 2 * K) S b‖ := norm_add_le _ _
    _ ≤ (((r * l : ℕ) : ℝ) * (l.totient : ℝ)) * (4 * B) +
          (((r * l : ℕ) : ℝ) * (l.totient : ℝ)) * (4 * B) := by
      apply add_le_add
      · exact canonical_coupled_first_marginal_growing_branch_norm_le
          r l hcop chi hne h2 B A K b hb hB hBA hNonempty hK hGrowingLast
      · exact canonical_coupled_first_marginal_shrinking_branch_norm_le
          r l hcop chi hne h2 B (A + 2 * K) S b hb hB (by omega)
            hShrinkingFirst hS hFinal
    _ = (((r * l : ℕ) : ℝ) * (l.totient : ℝ)) * (8 * B) := by ring

end GoldbachCircleMethodCanonicalCoupledFirstMarginalTwoBranchV18377
