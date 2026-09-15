import GoldbachCircleMethodArithmeticPrefixMeanClosedV18440
import GoldbachCircleMethodCentralPrefixMeanAbsorptionV18427

/-!
# Goldbach V1.8.441: central absorption with the arithmetic mean discharged

V1.8.440 supplies the full arithmetic-prefix mean bound unconditionally.
This module substitutes that kernel-checked result into the central correction
absorption theorem from V1.8.427.  Consequently no free mean-value premise
remains in this interface.

The exact aggregate correction majorant and the source-scalar smallness remain
explicit premises.  This is an intermediate gate closure, not a proof of the
Goldbach conjecture; `proof_status = NO_PROOF` remains in force.
-/

set_option autoImplicit false

open scoped BigOperators Classical ArithmeticFunction

namespace GoldbachCircleMethodCentralEulerMeanAbsorptionV18441

open GoldbachCircleMethodArithmeticEulerKernelBoundV18439
open GoldbachCircleMethodArithmeticPrefixMeanClosedV18440
open GoldbachCircleMethodCanonicalCentralAdjustedPositiveV18403
open GoldbachCircleMethodCanonicalCentralSourceTransferV18404
open GoldbachCircleMethodCentralArithmeticMeanBudgetV18424
open GoldbachCircleMethodCentralCorrectionMeanMajorantV18425
open GoldbachCircleMethodCentralPrefixMeanAbsorptionV18427
open GoldbachCircleMethodCenteredDimensionlessBudgetV18411
open GoldbachCircleMethodStructurallyAdmissibleActiveSlotV18258

/-- The V1.8.427 central threshold with its arithmetic prefix-mean premise
discharged by the finite Euler-kernel bound of V1.8.440. -/
theorem central_adjusted_centered_error_lt_of_euler_mean
    (CE CB D c CH rho b eta : ℝ) (m : ℕ) (hm : 1 ≤ m)
    (e : StructurallyAdmissibleActiveSlot
      ⌊(((8 * m : ℕ) : ℝ) ^ rho) ^ 2⌋₊)
    (heta : 0 ≤ eta)
    (hcoeff : 0 ≤ centeredCorrectionDimensionlessCoefficient CE CB D c CH rho)
    (hcorrection :
      |centralAdjustedCenteredErrorTargetSum m rho b e| ≤
        centralAdjustedCenteredBudgetSum CE CB D c CH rho eta m)
    (hscalar :
      eta * centeredCorrectionDimensionlessCoefficient CE CB D c CH rho *
        (4 * (eulerKernelConstant + 1)) < (1 : ℝ) / 768) :
    |centralAdjustedCenteredErrorTargetSum m rho b e| <
      ((8 * m : ℕ) : ℝ) ^ 2 / 2048 := by
  have hX : 1 ≤ 7 * m + 1 := by omega
  have hprefix := arithmeticFactorPrefixSum_le_eulerMean hX
  exact central_adjusted_centered_error_lt_of_prefix_mean
    CE CB D c CH rho b eta (eulerKernelConstant + 1) m hm e
    heta hcoeff hcorrection hprefix eulerMean_nonneg hscalar

end GoldbachCircleMethodCentralEulerMeanAbsorptionV18441
