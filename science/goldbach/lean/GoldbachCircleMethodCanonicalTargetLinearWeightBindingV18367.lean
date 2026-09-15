import GoldbachCircleMethodEvenTargetWeightedCharacterAverageV18366
import GoldbachCircleMethodVariableUnitPairCorrectionFactorizationV18345
import GoldbachCircleMethodSupportedModelIntervalDiagonalV18228

/-!
# V1.8.367: canonical target linear-weight binding

V1.8.366 controls an abstract target-weighted first character marginal by a
single-conductor period and the total variation of the target weights.  This
module removes one abstraction boundary: the scalar weight is bound exactly
to the canonical pair carrier of the upper-half block.

The pair carrier is invariant under the complement involution `n \mapsto N-n`.
Consequently the two one-sided power-weight sums agree, and the linear scalar
channel is exactly twice the one-sided carrier sum.  The interval-indexed
`variableLinearPowerWeightSum` from V1.8.345 is then identified with that
canonical carrier value.

No target-to-target variation estimate, sign estimate, exceptional-set bound,
or Goldbach conclusion is asserted.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodCanonicalTargetLinearWeightBindingV18367

open GoldbachCircleMethodBlockPairCarrierV18227
open GoldbachCircleMethodExceptionalWeightBoundaryV18128
open GoldbachCircleMethodLogCutoffPresieveBindingV18120
open GoldbachCircleMethodSupportedModelIntervalDiagonalV18228
open GoldbachCircleMethodUncorrectedSupportedErrorConvolutionV18184
open GoldbachCircleMethodVariableUnitPairCorrectionFactorizationV18345

/-- The real scalar coefficient of the first character marginal, defined on
the literal canonical pair carrier rather than on a free interval. -/
noncomputable def canonicalTargetLinearWeight
    (B N : ℕ) (b : ℝ) : ℝ :=
  ∑ n ∈ pairFirstCarrier (blockCarrier B) N,
    (powerWeight b (N - n) + powerWeight b n)

/-- Complementation preserves the canonical pair carrier. -/
theorem mem_pairFirstCarrier_complement_iff
    (B N n : ℕ) (hBN : B ≤ N) :
    N - n ∈ pairFirstCarrier (blockCarrier B) N ↔
      n ∈ pairFirstCarrier (blockCarrier B) N := by
  simp only [pairFirstCarrier, blockCarrier, Finset.mem_filter, Finset.mem_Ioc]
  constructor
  · rintro ⟨hcomp, hback⟩
    have hnN : n ≤ N := by omega
    simpa [Nat.sub_sub_self hnN] using And.intro hback hcomp
  · rintro ⟨hn, hcomp⟩
    have hnN : n ≤ N := hn.2.trans hBN
    simpa [Nat.sub_sub_self hnN] using And.intro hcomp hn

/-- The two one-sided power-weight sums agree by the complement involution. -/
theorem sum_powerWeight_complement_eq_sum_powerWeight
    (B N : ℕ) (b : ℝ) (hBN : B ≤ N) :
    (∑ n ∈ pairFirstCarrier (blockCarrier B) N,
        powerWeight b (N - n)) =
      ∑ n ∈ pairFirstCarrier (blockCarrier B) N, powerWeight b n := by
  apply Finset.sum_bij (fun n _hn => N - n)
  · intro n hn
    exact (mem_pairFirstCarrier_complement_iff B N n hBN).2 hn
  · intro n₁ hn₁ n₂ hn₂ heq
    have hn₁B : n₁ ≤ B := by
      exact (Finset.mem_Ioc.mp (Finset.mem_filter.mp hn₁).1).2
    have hn₂B : n₂ ≤ B := by
      exact (Finset.mem_Ioc.mp (Finset.mem_filter.mp hn₂).1).2
    have hn₁N : n₁ ≤ N := hn₁B.trans hBN
    have hn₂N : n₂ ≤ N := hn₂B.trans hBN
    omega
  · intro n hn
    refine ⟨N - n, (mem_pairFirstCarrier_complement_iff B N n hBN).2 hn, ?_⟩
    have hnB : n ≤ B :=
      (Finset.mem_Ioc.mp (Finset.mem_filter.mp hn).1).2
    have hnN : n ≤ N := hnB.trans hBN
    exact Nat.sub_sub_self hnN
  · intro n hn
    rfl

/-- The canonical linear scalar is exactly twice its one-sided block sum. -/
theorem canonicalTargetLinearWeight_eq_two_mul_sum
    (B N : ℕ) (b : ℝ) (hBN : B ≤ N) :
    canonicalTargetLinearWeight B N b =
      2 * (∑ n ∈ pairFirstCarrier (blockCarrier B) N, powerWeight b n) := by
  unfold canonicalTargetLinearWeight
  rw [Finset.sum_add_distrib,
    sum_powerWeight_complement_eq_sum_powerWeight B N b hBN]
  ring

/-- Exact source binding: the interval scalar from V1.8.345 is the complex
cast of the canonical carrier scalar. -/
theorem variableLinearPowerWeightSum_canonical_block_eq
    (B N : ℕ) (b : ℝ)
    (hB : 1 ≤ B) (hBN : B ≤ N)
    (hInterval : blockPairLower B N ≤ blockPairUpper B N) :
    variableLinearPowerWeightSum N (blockPairLower B N)
        (blockPairUpper B N - blockPairLower B N + 1) b =
      (canonicalTargetLinearWeight B N b : ℂ) := by
  unfold variableLinearPowerWeightSum canonicalTargetLinearWeight
  rw [pairFirstCarrier_block_eq_Icc B N hB hBN]
  rw [sum_Icc_eq_sum_range_shift
    (blockPairLower B N) (blockPairUpper B N) hInterval]
  push_cast
  rfl

/-- Combined normal form for the actual first scalar channel: twice the
one-sided canonical carrier sum. -/
theorem variableLinearPowerWeightSum_canonical_block_eq_two_mul_sum
    (B N : ℕ) (b : ℝ)
    (hB : 1 ≤ B) (hBN : B ≤ N)
    (hInterval : blockPairLower B N ≤ blockPairUpper B N) :
    variableLinearPowerWeightSum N (blockPairLower B N)
        (blockPairUpper B N - blockPairLower B N + 1) b =
      (2 * (∑ n ∈ pairFirstCarrier (blockCarrier B) N,
        powerWeight b n) : ℝ) := by
  rw [variableLinearPowerWeightSum_canonical_block_eq B N b hB hBN hInterval]
  exact_mod_cast canonicalTargetLinearWeight_eq_two_mul_sum B N b hBN

end GoldbachCircleMethodCanonicalTargetLinearWeightBindingV18367
