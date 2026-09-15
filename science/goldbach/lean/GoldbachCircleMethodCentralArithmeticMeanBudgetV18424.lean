import GoldbachCircleMethodCanonicalCentralCenteredErrorAggregateV18405
import GoldbachCircleMethodCenteredDimensionlessBudgetV18411

/-!
# Goldbach V1.8.424: central arithmetic-mean budget

The targetwise arithmetic-factor loss is aggregated before numerical
absorption.  This avoids replacing a block mean by the worst individual
target.  No mean-value estimate for `arithmeticFactor` is proved here: the
exact finite mean remains an explicit interface.

This is algebraic budget bookkeeping only.  It neither supplies the character
source estimate nor changes `proof_status = NO_PROOF`.
-/

set_option autoImplicit false

open scoped BigOperators Classical ArithmeticFunction

namespace GoldbachCircleMethodCentralArithmeticMeanBudgetV18424

open GoldbachCircleMethodCanonicalCentralAdjustedPositiveV18403
open GoldbachCircleMethodCanonicalCentralCenteredErrorAggregateV18405
open GoldbachCircleMethodCenteredDimensionlessBudgetV18411
open GoldbachCircleMethodAdjustedCenteredCorrectionNumericAbsorptionV18254
open GoldbachCircleMethodGlobalSieveFiniteFactorV18173

/-- Exact arithmetic-factor mass on the canonical central target sweep. -/
noncomputable def centralArithmeticFactorSum (m : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (2 * m + 1), arithmeticFactor (centralTargetNat m i)

/-- Sum of the literal V1.8.254 pointwise budget expressions. -/
noncomputable def centralAdjustedCenteredBudgetSum
    (CE CB D c CH rho eta : ℝ) (m : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (2 * m + 1),
    adjustedCenteredCorrectionBudgetExpression
      CE CB D c CH rho eta (8 * m) (centralTargetNat m i)

/-- The whole block budget factors through the *sum* of arithmetic factors,
not their maximum. -/
theorem central_budget_sum_exact_factorization
    (CE CB D c CH rho eta : ℝ) (m : ℕ) :
    centralAdjustedCenteredBudgetSum CE CB D c CH rho eta m =
      ((8 * m : ℕ) : ℝ) * eta *
        centeredCorrectionDimensionlessCoefficient CE CB D c CH rho *
          centralArithmeticFactorSum m := by
  unfold centralAdjustedCenteredBudgetSum centralArithmeticFactorSum
  calc
    (∑ i ∈ Finset.range (2 * m + 1),
        adjustedCenteredCorrectionBudgetExpression
          CE CB D c CH rho eta (8 * m) (centralTargetNat m i)) =
      ∑ i ∈ Finset.range (2 * m + 1),
        (((8 * m : ℕ) : ℝ) * eta *
          centeredCorrectionDimensionlessCoefficient CE CB D c CH rho) *
            arithmeticFactor (centralTargetNat m i) := by
              apply Finset.sum_congr rfl
              intro i hi
              rw [adjusted_centered_budget_dimensionless_factorization]
              ring
    _ = (((8 * m : ℕ) : ℝ) * eta *
          centeredCorrectionDimensionlessCoefficient CE CB D c CH rho) *
        (∑ i ∈ Finset.range (2 * m + 1),
          arithmeticFactor (centralTargetNat m i)) := by
            rw [Finset.mul_sum]
    _ = _ := by ring

/-- A block-level dimensionless estimate absorbs the complete central budget.
Unlike V1.8.412, this hypothesis is genuinely averaged over targets. -/
theorem central_budget_sum_lt_one_over_2048_of_aggregate_smallness
    (CE CB D c CH rho eta : ℝ) (m : ℕ) (hm : 0 < m)
    (hsmall :
      eta * centeredCorrectionDimensionlessCoefficient CE CB D c CH rho *
          centralArithmeticFactorSum m <
        ((8 * m : ℕ) : ℝ) / 2048) :
    centralAdjustedCenteredBudgetSum CE CB D c CH rho eta m <
      ((8 * m : ℕ) : ℝ) ^ 2 / 2048 := by
  rw [central_budget_sum_exact_factorization]
  have hB : (0 : ℝ) < ((8 * m : ℕ) : ℝ) := by positivity
  have hmul := mul_lt_mul_of_pos_left hsmall hB
  nlinarith

/-- A uniform mean bound converts a fixed scalar source budget into the
aggregate threshold.  The constant `1/768` is the exact cost of the inequality
`2*m+1 <= 3*m` for `m >= 1`. -/
theorem central_budget_sum_lt_one_over_2048_of_mean_bound
    (CE CB D c CH rho eta Cmean : ℝ) (m : ℕ) (hm : 1 ≤ m)
    (heta : 0 ≤ eta)
    (hcoeff : 0 ≤ centeredCorrectionDimensionlessCoefficient CE CB D c CH rho)
    (hmean : centralArithmeticFactorSum m ≤ Cmean * (2 * m + 1 : ℕ))
    (hscalar :
      eta * centeredCorrectionDimensionlessCoefficient CE CB D c CH rho * Cmean <
        (1 : ℝ) / 768) :
    centralAdjustedCenteredBudgetSum CE CB D c CH rho eta m <
      ((8 * m : ℕ) : ℝ) ^ 2 / 2048 := by
  apply central_budget_sum_lt_one_over_2048_of_aggregate_smallness
    CE CB D c CH rho eta m (by omega)
  have hnonneg :
      0 ≤ eta * centeredCorrectionDimensionlessCoefficient CE CB D c CH rho :=
    mul_nonneg heta hcoeff
  have hmean' := mul_le_mul_of_nonneg_left hmean hnonneg
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hcount : (0 : ℝ) < 2 * m + 1 := by positivity
  have hscaled := mul_lt_mul_of_pos_right hscalar hcount
  push_cast at hmean'
  calc
    eta * centeredCorrectionDimensionlessCoefficient CE CB D c CH rho *
          centralArithmeticFactorSum m ≤
        (eta * centeredCorrectionDimensionlessCoefficient CE CB D c CH rho *
          Cmean) * (2 * (m : ℝ) + 1) := by
            calc
              _ ≤ eta * centeredCorrectionDimensionlessCoefficient
                    CE CB D c CH rho * (Cmean * (2 * (m : ℝ) + 1)) := hmean'
              _ = _ := by ring
    _ < ((1 : ℝ) / 768) * (2 * (m : ℝ) + 1) := hscaled
    _ ≤ ((8 * m : ℕ) : ℝ) / 2048 := by
      push_cast
      nlinarith

end GoldbachCircleMethodCentralArithmeticMeanBudgetV18424
