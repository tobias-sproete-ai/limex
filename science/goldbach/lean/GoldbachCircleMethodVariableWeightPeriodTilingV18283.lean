import GoldbachCircleMethodTwoSourceScaleActivePeriodCoverV18282

/-!
# Goldbach V1.8.283: exact variable-weight period tiling

The literal variable-weight interval is additive under concatenation and an
integer multiple of the conductor is exactly the sum of its consecutive
complete-period blocks.  No sign or analytic estimate enters these identities.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodVariableWeightPeriodTilingV18283

open GoldbachCircleMethodActualUnitPairArithmeticV18194
open GoldbachCircleMethodVariableWeightIntervalDiscrepancyV18272

/-- Exact concatenation of two adjacent literal variable-weight intervals. -/
theorem variableUnitPairInterval_add_length
    (r N A T U : ℕ) [NeZero r]
    (chi : DirichletCharacter ℂ r) (b : ℝ) :
    variableUnitPairInterval r N A (T+U) chi b =
      variableUnitPairInterval r N A T chi b +
        variableUnitPairInterval r N (A+T) U chi b := by
  unfold variableUnitPairInterval
  rw [Finset.sum_range_add]
  congr 1
  apply Finset.sum_congr rfl
  intro i _hi
  simp only [Nat.add_assoc]

/-- Exact tiling of a length `k*r` interval by `k` consecutive conductor
periods. -/
theorem variableUnitPairInterval_mul_period
    (r N A k : ℕ) [NeZero r]
    (chi : DirichletCharacter ℂ r) (b : ℝ) :
    variableUnitPairInterval r N A (k*r) chi b =
      ∑ j ∈ Finset.range k,
        variableUnitPairInterval r N (A+j*r) r chi b := by
  induction k with
  | zero => simp [variableUnitPairInterval]
  | succ k ih =>
      rw [Nat.succ_mul, variableUnitPairInterval_add_length, ih,
        Finset.sum_range_succ]

/-- If every tiled period has positive real part and at least one period is
present, the entire exact multiple has positive real part. -/
theorem variableUnitPairInterval_mul_period_pos
    (r N A k : ℕ) [NeZero r]
    (chi : DirichletCharacter ℂ r) (b : ℝ)
    (hk : 0 < k)
    (hpos : ∀ j ∈ Finset.range k,
      0 < (variableUnitPairInterval r N (A+j*r) r chi b).re) :
    0 < (variableUnitPairInterval r N A (k*r) chi b).re := by
  rw [variableUnitPairInterval_mul_period]
  rw [Complex.re_sum]
  exact Finset.sum_pos hpos (Finset.nonempty_range_iff.mpr (Nat.ne_of_gt hk))

end GoldbachCircleMethodVariableWeightPeriodTilingV18283
