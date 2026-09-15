import GoldbachCircleMethodCanonicalTargetLinearWeightBindingV18367

/-!
# V1.8.368: piecewise geometry of the canonical target weight

The canonical block-pair carrier has one exact turning target.  Before that
target its left endpoint is fixed and its right endpoint grows.  After it, the
right endpoint is fixed and the left endpoint grows.  This finite geometry is
the source-level prerequisite for any target-to-target variation estimate.

No monotonicity, variation budget, character cancellation, exceptional-set
bound, or Goldbach conclusion is asserted.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodCanonicalTargetWeightPiecewiseGeometryV18368

open GoldbachCircleMethodBlockPairCarrierV18227
open GoldbachCircleMethodCanonicalTargetLinearWeightBindingV18367
open GoldbachCircleMethodExceptionalWeightBoundaryV18128
open GoldbachCircleMethodLogCutoffPresieveBindingV18120

/-- The unique natural target at which the two endpoint regimes meet. -/
def blockPairTurningTarget (B : ℕ) : ℕ := B + B / 2 + 1

/-- On the growing side, the lower endpoint is fixed at the first point of
the upper-half source block. -/
theorem blockPairLower_eq_fixed_of_le_turn
    (B N : ℕ) (hBN : B ≤ N) (hTurn : N ≤ blockPairTurningTarget B) :
    blockPairLower B N = B / 2 + 1 := by
  simp only [blockPairTurningTarget] at hTurn
  unfold blockPairLower
  omega

/-- On the growing side, the upper endpoint is the moving complement edge. -/
theorem blockPairUpper_eq_moving_of_le_turn
    (B N : ℕ) (hTurn : N ≤ blockPairTurningTarget B) :
    blockPairUpper B N = N - (B / 2 + 1) := by
  simp only [blockPairTurningTarget] at hTurn
  unfold blockPairUpper
  omega

/-- On the shrinking side, the lower endpoint is the moving complement edge. -/
theorem blockPairLower_eq_moving_of_turn_le
    (B N : ℕ) (hTurn : blockPairTurningTarget B ≤ N) :
    blockPairLower B N = N - B := by
  simp only [blockPairTurningTarget] at hTurn
  unfold blockPairLower
  omega

/-- On the shrinking side, the upper endpoint is fixed at the source-block
endpoint. -/
theorem blockPairUpper_eq_fixed_of_turn_le
    (B N : ℕ) (hTurn : blockPairTurningTarget B ≤ N) :
    blockPairUpper B N = B := by
  simp only [blockPairTurningTarget] at hTurn
  unfold blockPairUpper
  omega

/-- Exact carrier normal form on the growing side of the turning target. -/
theorem pairFirstCarrier_eq_Icc_growing
    (B N : ℕ) (hB : 1 ≤ B) (hBN : B ≤ N)
    (hTurn : N ≤ blockPairTurningTarget B) :
    pairFirstCarrier (blockCarrier B) N =
      Finset.Icc (B / 2 + 1) (N - (B / 2 + 1)) := by
  rw [pairFirstCarrier_block_eq_Icc B N hB hBN,
    blockPairLower_eq_fixed_of_le_turn B N hBN hTurn,
    blockPairUpper_eq_moving_of_le_turn B N hTurn]

/-- Exact carrier normal form on the shrinking side of the turning target. -/
theorem pairFirstCarrier_eq_Icc_shrinking
    (B N : ℕ) (hB : 1 ≤ B) (hBN : B ≤ N)
    (hTurn : blockPairTurningTarget B ≤ N) :
    pairFirstCarrier (blockCarrier B) N = Finset.Icc (N - B) B := by
  rw [pairFirstCarrier_block_eq_Icc B N hB hBN,
    blockPairLower_eq_moving_of_turn_le B N hTurn,
    blockPairUpper_eq_fixed_of_turn_le B N hTurn]

/-- Source-bound real weight formula on the growing side. -/
theorem canonicalTargetLinearWeight_eq_growing_sum
    (B N : ℕ) (b : ℝ) (hB : 1 ≤ B) (hBN : B ≤ N)
    (hTurn : N ≤ blockPairTurningTarget B) :
    canonicalTargetLinearWeight B N b =
      2 * (∑ n ∈ Finset.Icc (B / 2 + 1) (N - (B / 2 + 1)),
        powerWeight b n) := by
  rw [canonicalTargetLinearWeight_eq_two_mul_sum B N b hBN,
    pairFirstCarrier_eq_Icc_growing B N hB hBN hTurn]

/-- Source-bound real weight formula on the shrinking side. -/
theorem canonicalTargetLinearWeight_eq_shrinking_sum
    (B N : ℕ) (b : ℝ) (hB : 1 ≤ B) (hBN : B ≤ N)
    (hTurn : blockPairTurningTarget B ≤ N) :
    canonicalTargetLinearWeight B N b =
      2 * (∑ n ∈ Finset.Icc (N - B) B, powerWeight b n) := by
  rw [canonicalTargetLinearWeight_eq_two_mul_sum B N b hBN,
    pairFirstCarrier_eq_Icc_shrinking B N hB hBN hTurn]

/-- At the turning target the two endpoint descriptions coincide with the
entire upper-half block. -/
theorem pairFirstCarrier_at_turn_eq_blockCarrier
    (B : ℕ) (hB : 1 ≤ B) :
    pairFirstCarrier (blockCarrier B) (blockPairTurningTarget B) =
      blockCarrier B := by
  rw [pairFirstCarrier_eq_Icc_growing B (blockPairTurningTarget B) hB
    (by unfold blockPairTurningTarget; omega) le_rfl]
  ext n
  simp only [blockPairTurningTarget, blockCarrier, Finset.mem_Icc,
    Finset.mem_Ioc]
  omega

end GoldbachCircleMethodCanonicalTargetWeightPiecewiseGeometryV18368
