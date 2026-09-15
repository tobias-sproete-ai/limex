import GoldbachCircleMethodCoupledSecondMarginalPairwiseRemainderV18384
import GoldbachCircleMethodCanonicalTargetLinearWeightBindingV18367

/-!
# Goldbach V1.8.385: canonical target quadratic-weight binding

The second scalar channel in V1.8.345 is bound exactly to the canonical block
pair carrier.  Its target weight is no longer an abstract coefficient.  The
module also proves the elementary source-scale envelope `0 <= weight <= B`.

No target-to-target variation estimate, pairwise Abel estimate, aggregation,
or reserve absorption is asserted.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodCanonicalTargetQuadraticWeightBindingV18385

open GoldbachCircleMethodBlockPairCarrierV18227
open GoldbachCircleMethodExceptionalWeightBoundaryV18128
open GoldbachCircleMethodLogCutoffPresieveBindingV18120
open GoldbachCircleMethodRemovedConvolutionNormV18123
open GoldbachCircleMethodSupportedModelIntervalDiagonalV18228
open GoldbachCircleMethodVariableUnitPairCorrectionFactorizationV18345

/-- Literal quadratic scalar coefficient of the second Ramanujan marginal on
the canonical pair carrier. -/
noncomputable def canonicalTargetQuadraticWeight
    (B N : ℕ) (b : ℝ) : ℝ :=
  ∑ n ∈ pairFirstCarrier (blockCarrier B) N,
    powerWeight b (N - n) * powerWeight b n

/-- Exact source binding of the interval-indexed V1.8.345 scalar to the
canonical pair carrier. -/
theorem variableQuadraticPowerWeightSum_canonical_block_eq
    (B N : ℕ) (b : ℝ)
    (hB : 1 ≤ B) (hBN : B ≤ N)
    (hInterval : blockPairLower B N ≤ blockPairUpper B N) :
    variableQuadraticPowerWeightSum N (blockPairLower B N)
        (blockPairUpper B N - blockPairLower B N + 1) b =
      (canonicalTargetQuadraticWeight B N b : ℂ) := by
  unfold variableQuadraticPowerWeightSum canonicalTargetQuadraticWeight
  rw [pairFirstCarrier_block_eq_Icc B N hB hBN]
  rw [sum_Icc_eq_sum_range_shift
    (blockPairLower B N) (blockPairUpper B N) hInterval]
  push_cast
  rfl

/-- The canonical quadratic target weight is nonnegative and at most the
source block scale. -/
theorem canonicalTargetQuadraticWeight_mem_Icc
    (B N : ℕ) (b : ℝ) (hb : 0 ≤ b) :
    canonicalTargetQuadraticWeight B N b ∈ Set.Icc (0 : ℝ) B := by
  constructor
  · unfold canonicalTargetQuadraticWeight
    apply Finset.sum_nonneg
    intro n _hn
    exact mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  · unfold canonicalTargetQuadraticWeight
    calc
      (∑ n ∈ pairFirstCarrier (blockCarrier B) N,
          powerWeight b (N - n) * powerWeight b n) ≤
          ∑ _n ∈ pairFirstCarrier (blockCarrier B) N, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro n hn
        have hnBlock : n ∈ blockCarrier B := (Finset.mem_filter.mp hn).1
        have hcompBlock : N - n ∈ blockCarrier B :=
          (Finset.mem_filter.mp hn).2
        have hnLe : powerWeight b n ≤ 1 :=
          (le_abs_self (powerWeight b n)).trans
            (power_weight_abs_le_one B n b hb hnBlock)
        have hcompLe : powerWeight b (N - n) ≤ 1 :=
          (le_abs_self (powerWeight b (N - n))).trans
            (power_weight_abs_le_one B (N - n) b hb hcompBlock)
        exact (mul_le_mul hcompLe hnLe
          (Real.rpow_nonneg (Nat.cast_nonneg _) _) zero_le_one).trans_eq (mul_one 1)
      _ = (((pairFirstCarrier (blockCarrier B) N).card : ℕ) : ℝ) := by simp
      _ ≤ (((blockCarrier B).card : ℕ) : ℝ) := by
        exact_mod_cast Finset.card_filter_le (blockCarrier B)
          (fun n => N - n ∈ blockCarrier B)
      _ ≤ B := by exact_mod_cast block_carrier_card_le B

end GoldbachCircleMethodCanonicalTargetQuadraticWeightBindingV18385
