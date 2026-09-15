import GoldbachCircleMethodCanonicalFirstMarginalAbelBoundV18371

/-!
# V1.8.372: two-branch bound for the canonical first marginal

A parity-compatible target interval that crosses the canonical turning target
is split exactly into one growing and one shrinking range.  Applying the
V1.8.371 single-branch estimate to both pieces and using the triangle
inequality gives the full first-marginal bound `8*r*B`.

No cross-turn variation estimate is needed and no common LCM is introduced.
The existence of a suitable split for every historical target block, the
aggregation over conductors/characters, and the second marginal remain open.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodCanonicalFirstMarginalTwoBranchBoundV18372

open GoldbachCircleMethodCanonicalFirstMarginalAbelBoundV18371
open GoldbachCircleMethodCanonicalTargetLinearWeightBindingV18367
open GoldbachCircleMethodCanonicalTargetWeightPiecewiseGeometryV18368

/-- The complete canonical first-marginal target sum. -/
noncomputable def canonicalFirstMarginalTargetSum
    (r : ℕ) [NeZero r] (chi : DirichletCharacter ℂ r)
    (B A T : ℕ) (b : ℝ) : ℂ :=
  ∑ i ∈ Finset.range T,
    canonicalTargetLinearWeight B (A + 2 * i) b •
      (((ArithmeticFunction.moebius r : ℤ) : ℂ) *
        chi ((A + 2 * i : ℕ) : ZMod r))

/-- Exact split of the target sum into consecutive parity-compatible ranges. -/
theorem canonicalFirstMarginalTargetSum_add
    (r : ℕ) [NeZero r] (chi : DirichletCharacter ℂ r)
    (B A K S : ℕ) (b : ℝ) :
    canonicalFirstMarginalTargetSum r chi B A (K + S) b =
      canonicalFirstMarginalTargetSum r chi B A K b +
        canonicalFirstMarginalTargetSum r chi B (A + 2 * K) S b := by
  unfold canonicalFirstMarginalTargetSum
  rw [Finset.sum_range_add]
  congr 1
  apply Finset.sum_congr rfl
  intro i _hi
  have htarget : A + 2 * (K + i) = A + 2 * K + 2 * i := by omega
  rw [htarget]

/-- If the explicit split lies on the two sides of the turning target, the
full source-bound first marginal is controlled by `8*r*B`. -/
theorem canonical_first_marginal_two_branch_norm_le
    (r : ℕ) [NeZero r]
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
    ‖canonicalFirstMarginalTargetSum r chi B A (K + S) b‖ ≤
      (r : ℝ) * (8 * B) := by
  rw [canonicalFirstMarginalTargetSum_add r chi B A K S b]
  calc
    _ ≤ ‖canonicalFirstMarginalTargetSum r chi B A K b‖ +
          ‖canonicalFirstMarginalTargetSum r chi B (A + 2 * K) S b‖ :=
      norm_add_le _ _
    _ ≤ (r : ℝ) * (4 * B) + (r : ℝ) * (4 * B) := by
      apply add_le_add
      · unfold canonicalFirstMarginalTargetSum
        exact canonical_first_marginal_growing_branch_norm_le
          r chi hne h2 B A K b hb hB hBA hNonempty hK hGrowingLast
      · unfold canonicalFirstMarginalTargetSum
        exact canonical_first_marginal_shrinking_branch_norm_le
          r chi hne h2 B (A + 2 * K) S b hb hB (by omega)
            hShrinkingFirst hS hFinal
    _ = (r : ℝ) * (8 * B) := by ring

end GoldbachCircleMethodCanonicalFirstMarginalTwoBranchBoundV18372
