import GoldbachCircleMethodTotientFourthFiniteEulerProductV18568
import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# Goldbach V1.8.569: exponential majorant for the finite Euler product

This module uses the elementary inequality `1 + x ≤ exp x` termwise.
It does not yet bound the exponent uniformly in `Q`.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodTotientFourthEulerExponentialV18569

open GoldbachCircleMethodTotientFourthFiniteEulerProductV18568

noncomputable def primeFourthEulerExponent (Q : ℕ) : ℝ :=
  ∑ p ∈ primePrefixCarrier Q, (30 : ℝ) / (p : ℝ) ^ 2

theorem primeFourthEulerSummand_nonneg (p : ℕ) :
    0 ≤ (30 : ℝ) / (p : ℝ) ^ 2 := by
  positivity

/-- The finite Euler product is bounded by the exponential of its finite
prime reciprocal-square exponent. -/
theorem finiteEulerProduct_le_exp (Q : ℕ) :
    (∏ p ∈ primePrefixCarrier Q,
      (1 + (30 : ℝ) / (p : ℝ) ^ 2)) ≤
      Real.exp (primeFourthEulerExponent Q) := by
  unfold primeFourthEulerExponent
  exact Real.prod_one_add_le_exp_sum
    (primePrefixCarrier Q) primeFourthEulerSummand_nonneg

/-- The squarefree reciprocal-kernel prefix inherits the same exponential
majorant. -/
theorem squarefreeKernelPrefix_le_exp (Q : ℕ) :
    (∑ d ∈ Finset.Icc 1 Q,
      GoldbachCircleMethodTotientFourthSquarefreeKernelV18567.squarefreeReciprocalTotientFourthKernel d) ≤
      Real.exp (primeFourthEulerExponent Q) := by
  exact (squarefreeKernelPrefix_le_finiteEulerProduct Q).trans
    (finiteEulerProduct_le_exp Q)

end GoldbachCircleMethodTotientFourthEulerExponentialV18569
