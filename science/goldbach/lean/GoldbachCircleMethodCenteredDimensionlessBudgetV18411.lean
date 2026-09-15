import GoldbachCircleMethodCanonicalCentralSingleObstructionV18410

/-!
# Goldbach V1.8.411: dimensionless centered-correction budget

The last V1.8.410 source-side obstruction is rewritten without hiding a block
scale inside big-O notation.  The V1.8.254 targetwise budget factors exactly
as

`B * eta * arithmeticFactor(N) * centeredCoefficient`.

Consequently, targetwise absorption at scale `B/2048` is equivalent to a
dimensionless smallness requirement after division by the positive block
scale.  This is a normalization lemma, not an analytic estimate for `eta` or
the arithmetic factor.
-/

set_option autoImplicit false

open scoped BigOperators Classical ArithmeticFunction

namespace GoldbachCircleMethodCenteredDimensionlessBudgetV18411

open GoldbachCircleMethodAdjustedCenteredCorrectionNumericAbsorptionV18254
open GoldbachCircleMethodBadPrimeUniformFrequencyV18169
open GoldbachCircleMethodDirectLambdaRadicalDominationV18178
open GoldbachCircleMethodGlobalSieveFiniteFactorV18173
open GoldbachCircleMethodMertensProductFromHarmonicV18174
open GoldbachCircleMethodRadicalCorrelationTransferV18161

/-- The scale-free coefficient multiplying `B * eta * arithmeticFactor N` in
the literal V1.8.254 budget. -/
noncomputable def centeredCorrectionDimensionlessCoefficient
    (CE CB D c CH rho : ℝ) : ℝ :=
  CE *
    ((128 * CH * (mertensProductConstant D c)^2 *
        (oneFrequencyConstant D c)^2 *
        (∫ ξ : ℝ, secondMomentDecay ξ)^2 / tenthDecayMass) / rho^3 +
     CB * (128 * CH * (mertensProductConstant D c)^2 *
        (oneFrequencyConstant D c)^2 *
        (∫ ξ : ℝ, secondMomentDecay ξ)^2) / rho^2)

/-- Exact factorization of the V1.8.254 budget. -/
theorem adjusted_centered_budget_dimensionless_factorization
    (CE CB D c CH rho eta : ℝ) (B N : ℕ) :
    adjustedCenteredCorrectionBudgetExpression CE CB D c CH rho eta B N =
      (B : ℝ) *
        (eta * arithmeticFactor N *
          centeredCorrectionDimensionlessCoefficient CE CB D c CH rho) := by
  unfold adjustedCenteredCorrectionBudgetExpression
    centeredCorrectionDimensionlessCoefficient
  ring

/-- A strict dimensionless bound discharges the exact targetwise numerical
budget for every positive block. -/
theorem adjusted_centered_budget_lt_one_over_2048_of_dimensionless
    (CE CB D c CH rho eta : ℝ) (B N : ℕ) (hB : 0 < B)
    (hdimensionless :
      eta * arithmeticFactor N *
          centeredCorrectionDimensionlessCoefficient CE CB D c CH rho <
        (1 : ℝ) / 2048) :
    adjustedCenteredCorrectionBudgetExpression CE CB D c CH rho eta B N <
      (B : ℝ) / 2048 := by
  rw [adjusted_centered_budget_dimensionless_factorization]
  have hBreal : (0 : ℝ) < B := by exact_mod_cast hB
  have hmul := mul_lt_mul_of_pos_left hdimensionless hBreal
  nlinarith

end GoldbachCircleMethodCenteredDimensionlessBudgetV18411
