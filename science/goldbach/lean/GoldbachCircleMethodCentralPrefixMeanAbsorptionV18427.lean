import GoldbachCircleMethodCentralCorrectionMeanMajorantV18425
import GoldbachCircleMethodCentralArithmeticPrefixReductionV18426

/-!
# Goldbach V1.8.427: central prefix-mean absorption

The exact correction majorant from V1.8.425 and the prefix reduction from
V1.8.426 are composed.  A linear full-prefix bound for `arithmeticFactor`
now suffices to absorb the whole central correction.  No targetwise subpower
or polynomial source decay is required by this interface.

The full-prefix estimate and source scalar smallness remain explicit premises;
therefore `proof_status = NO_PROOF`.
-/

set_option autoImplicit false

open scoped BigOperators Classical ArithmeticFunction

namespace GoldbachCircleMethodCentralPrefixMeanAbsorptionV18427

open GoldbachCircleMethodCanonicalCentralAdjustedPositiveV18403
open GoldbachCircleMethodCanonicalCentralSourceTransferV18404
open GoldbachCircleMethodCentralArithmeticMeanBudgetV18424
open GoldbachCircleMethodCentralArithmeticPrefixReductionV18426
open GoldbachCircleMethodCentralCorrectionMeanMajorantV18425
open GoldbachCircleMethodCenteredDimensionlessBudgetV18411
open GoldbachCircleMethodStructurallyAdmissibleActiveSlotV18258

/-- Deterministic final arithmetic step: an exact aggregate correction
majorant, a linear prefix estimate, and one fixed scalar inequality imply the
required central correction threshold. -/
theorem central_adjusted_centered_error_lt_of_prefix_mean
    (CE CB D c CH rho b eta Cmean : ℝ) (m : ℕ) (hm : 1 ≤ m)
    (e : StructurallyAdmissibleActiveSlot
      ⌊(((8 * m : ℕ) : ℝ) ^ rho) ^ 2⌋₊)
    (heta : 0 ≤ eta)
    (hcoeff : 0 ≤ centeredCorrectionDimensionlessCoefficient CE CB D c CH rho)
    (hcorrection :
      |centralAdjustedCenteredErrorTargetSum m rho b e| ≤
        centralAdjustedCenteredBudgetSum CE CB D c CH rho eta m)
    (hprefix : arithmeticFactorPrefixSum (7 * m + 1) ≤
      Cmean * (7 * m + 1 : ℕ))
    (hCmean : 0 ≤ Cmean)
    (hscalar :
      eta * centeredCorrectionDimensionlessCoefficient CE CB D c CH rho *
        (4 * Cmean) < (1 : ℝ) / 768) :
    |centralAdjustedCenteredErrorTargetSum m rho b e| <
      ((8 * m : ℕ) : ℝ) ^ 2 / 2048 := by
  have hmean := centralArithmeticFactorSum_le_four_mul_of_prefix_bound
    Cmean m hm hCmean hprefix
  have hbudget := central_budget_sum_lt_one_over_2048_of_mean_bound
    CE CB D c CH rho eta (4 * Cmean) m hm heta hcoeff hmean hscalar
  exact hcorrection.trans_lt hbudget

end GoldbachCircleMethodCentralPrefixMeanAbsorptionV18427
