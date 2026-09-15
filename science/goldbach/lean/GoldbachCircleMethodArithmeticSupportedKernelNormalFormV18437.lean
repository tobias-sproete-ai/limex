import GoldbachCircleMethodArithmeticSupportedKernelV18436

/-!
# Goldbach V1.8.437: supported reciprocal-kernel normal form

The reciprocal kernel has the square-denominator shape
`3 ^ omega(d) / d^2` only on the restored odd squarefree support.  This module
proves that exact statement and keeps the kernel zero off support.  It does not
assert a uniform Euler-product bound or the Goldbach conjecture.

`proof_status = NO_PROOF` for the top-level Goldbach quest.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodArithmeticSupportedKernelNormalFormV18437

open GoldbachCircleMethodArithmeticDivisorWeightNormalFormV18434
open GoldbachCircleMethodArithmeticSupportedKernelV18436

theorem primeRadical_eq_self_of_admissible {d : ℕ}
    (hd : AdmissibleDivisor d) : primeRadical d = d := by
  exact Nat.prod_primeFactors_of_squarefree hd.1

theorem supportedReciprocalKernel_eq_pow_div_sq_of_admissible {d : ℕ}
    (hd : AdmissibleDivisor d) :
    supportedReciprocalKernel d =
      (3 : ℝ) ^ primeOmega d / (d : ℝ) ^ 2 := by
  have hd0 : (d : ℝ) ≠ 0 := by
    exact_mod_cast hd.1.ne_zero
  rw [supportedReciprocalKernel, if_pos hd,
    divisorMajorant_eq_pow_div_radical,
    primeRadical_eq_self_of_admissible hd]
  field_simp

theorem supportedReciprocalKernel_normal_form (d : ℕ) :
    supportedReciprocalKernel d =
      if AdmissibleDivisor d then
        (3 : ℝ) ^ primeOmega d / (d : ℝ) ^ 2
      else 0 := by
  by_cases hd : AdmissibleDivisor d
  · rw [if_pos hd, supportedReciprocalKernel_eq_pow_div_sq_of_admissible hd]
  · rw [if_neg hd, supportedReciprocalKernel, if_neg hd]

end GoldbachCircleMethodArithmeticSupportedKernelNormalFormV18437
