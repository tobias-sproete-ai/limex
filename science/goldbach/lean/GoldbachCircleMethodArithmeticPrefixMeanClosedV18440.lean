import GoldbachCircleMethodArithmeticEulerKernelBoundV18439

/-!
# Goldbach V1.8.440: unconditional arithmetic prefix-mean closure

The support-correct Euler-kernel bound is transferred back to the complete
`arithmeticFactor` prefix.  The missing zero index costs exactly one, yielding
the uniform mean constant `eulerKernelConstant + 1`.

This closes the arithmetic mean-value input introduced at V1.8.427.  The
remaining source-scalar smallness and upstream analytic source estimates are
not asserted.  The top-level Goldbach status therefore remains `NO_PROOF`.
-/

set_option autoImplicit false

open scoped BigOperators Classical ArithmeticFunction

namespace GoldbachCircleMethodArithmeticPrefixMeanClosedV18440

open GoldbachCircleMethodArithmeticSupportedKernelV18436
open GoldbachCircleMethodArithmeticEulerKernelBoundV18439
open GoldbachCircleMethodCentralArithmeticPrefixReductionV18426
open GoldbachCircleMethodGlobalSieveFiniteFactorV18173

theorem arithmeticFactor_zero : arithmeticFactor 0 = 1 := by
  simp [arithmeticFactor]

theorem arithmeticFactorPrefixSum_eq_one_add_Ico {X : ℕ} (hX : 1 ≤ X) :
    arithmeticFactorPrefixSum X =
      1 + ∑ n ∈ Finset.Ico 1 X, arithmeticFactor n := by
  unfold arithmeticFactorPrefixSum
  rw [Finset.sum_range_eq_add_Ico arithmeticFactor hX]
  simp [arithmeticFactor_zero]

theorem arithmeticFactorPrefixSum_le_eulerMean {X : ℕ} (hX : 1 ≤ X) :
    arithmeticFactorPrefixSum X ≤
      (eulerKernelConstant + 1) * (X : ℝ) := by
  have htail := arithmeticFactor_prefix_le_scale_mul_supportedKernelSum hX
  have hkernel := supportedKernelSum_le_eulerKernelConstant X
  have htail' :
      (∑ n ∈ Finset.Ico 1 X, arithmeticFactor n) ≤
        (X : ℝ) * eulerKernelConstant :=
    htail.trans (mul_le_mul_of_nonneg_left hkernel (Nat.cast_nonneg X))
  have hXR : (1 : ℝ) ≤ X := by exact_mod_cast hX
  rw [arithmeticFactorPrefixSum_eq_one_add_Ico hX]
  calc
    1 + (∑ n ∈ Finset.Ico 1 X, arithmeticFactor n) ≤
        1 + (X : ℝ) * eulerKernelConstant := by linarith
    _ ≤ (X : ℝ) + (X : ℝ) * eulerKernelConstant :=
      by linarith
    _ = (eulerKernelConstant + 1) * (X : ℝ) := by ring

theorem eulerMean_nonneg : 0 ≤ eulerKernelConstant + 1 := by
  have h := one_le_eulerKernelConstant
  linarith

end GoldbachCircleMethodArithmeticPrefixMeanClosedV18440
