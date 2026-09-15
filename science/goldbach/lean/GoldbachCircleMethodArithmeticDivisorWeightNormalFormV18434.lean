import GoldbachCircleMethodArithmeticPrefixDivisorBudgetV18433

/-!
# Goldbach V1.8.434: divisor-weight normal form

The positive divisor weight is normalized exactly as
`3 ^ omega(d) / rad(d)`, where both `omega` and `rad` are finite expressions
over `d.primeFactors`.  This exposes the convergent Euler-kernel shape after
the multiplicity gain from V1.8.433.

No bound for the resulting series is claimed. `proof_status = NO_PROOF`.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodArithmeticDivisorWeightNormalFormV18434

open GoldbachCircleMethodArithmeticFactorPositiveConvolutionV18428
open GoldbachCircleMethodArithmeticDivisorReindexV18430

def primeOmega (d : ℕ) : ℕ := d.primeFactors.card

def primeRadical (d : ℕ) : ℕ := ∏ p ∈ d.primeFactors, p

theorem divisorMajorant_eq_pow_div_radical (d : ℕ) :
    divisorMajorant d =
      (3 : ℝ) ^ primeOmega d / (primeRadical d : ℝ) := by
  unfold divisorMajorant arithmeticSubsetMajorant primeOmega primeRadical
  rw [Finset.prod_div_distrib]
  simp only [Finset.prod_const, Nat.cast_prod]

theorem primeRadical_pos (d : ℕ) : 0 < primeRadical d := by
  unfold primeRadical
  exact Finset.prod_pos fun p hp => (Nat.prime_of_mem_primeFactors hp).pos

theorem divisorMajorant_pos (d : ℕ) : 0 < divisorMajorant d := by
  rw [divisorMajorant_eq_pow_div_radical]
  have hrad : (0 : ℝ) < (primeRadical d : ℝ) := by
    exact_mod_cast primeRadical_pos d
  exact div_pos (pow_pos (by norm_num : (0 : ℝ) < 3) _) hrad

/-- Reciprocal kernel exposed after counting multiples. -/
noncomputable def reciprocalDivisorKernel (d : ℕ) : ℝ :=
  if d = 0 then 0 else divisorMajorant d / (d : ℝ)

theorem reciprocalDivisorKernel_nonneg (d : ℕ) :
    0 ≤ reciprocalDivisorKernel d := by
  unfold reciprocalDivisorKernel
  split_ifs with hd
  · positivity
  · exact div_nonneg (le_of_lt (divisorMajorant_pos d)) (Nat.cast_nonneg d)

end GoldbachCircleMethodArithmeticDivisorWeightNormalFormV18434
