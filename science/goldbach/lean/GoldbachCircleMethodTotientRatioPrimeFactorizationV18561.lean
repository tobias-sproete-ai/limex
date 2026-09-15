import GoldbachCircleMethodCollisionTotientFourthMomentTransferV18560

/-!
# Goldbach V1.8.561: prime-factor normal form of the totient ratio

For every positive integer, the remaining collision weight `n / phi(n)` is
rewritten exactly as the finite Euler product over the prime support of `n`.
This exposes the arithmetic input required for a linear fourth-moment bound;
the bound itself is not claimed in this module.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodTotientRatioPrimeFactorizationV18561

open GoldbachCircleMethodCollisionTotientFourthMomentTransferV18560
open GoldbachCircleMethodCollisionTotientRatioEnvelopeV18556

/-- Every prime-support denominator factor `p-1` is nonzero over the reals. -/
theorem primeFactor_sub_one_cast_ne_zero {n p : ℕ}
    (hp : p ∈ n.primeFactors) : ((p - 1 : ℕ) : ℝ) ≠ 0 := by
  have hpPrime : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hpTwo : 2 ≤ p := hpPrime.two_le
  exact_mod_cast (show p - 1 ≠ 0 by omega)

/-- Exact finite Euler-product formula for the positive totient ratio. -/
theorem levelTotientRatio_eq_primeFactorProduct
    (n : ℕ) (hn : n ≠ 0) :
    levelTotientRatio n =
      ∏ p ∈ n.primeFactors, (p : ℝ) / ((p - 1 : ℕ) : ℝ) := by
  have hphi : (n.totient : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.totient_pos.mpr (Nat.pos_of_ne_zero hn)))
  have hden :
      (∏ p ∈ n.primeFactors, ((p - 1 : ℕ) : ℝ)) ≠ 0 := by
    exact Finset.prod_ne_zero_iff.mpr fun p hp =>
      primeFactor_sub_one_cast_ne_zero hp
  have hEuler := congrArg (fun m : ℕ => (m : ℝ))
    (Nat.totient_mul_prod_primeFactors n)
  push_cast at hEuler
  unfold levelTotientRatio
  rw [Finset.prod_div_distrib]
  apply (div_eq_div_iff hphi hden).2
  calc
    (n : ℝ) * ∏ p ∈ n.primeFactors, ((p - 1 : ℕ) : ℝ) =
        (n.totient : ℝ) * ∏ p ∈ n.primeFactors, (p : ℝ) := hEuler.symm
    _ = (∏ p ∈ n.primeFactors, (p : ℝ)) * (n.totient : ℝ) := by ring

/-- The fourth power of the collision ratio is the product of the fourth
powers of its local prime factors. -/
theorem levelTotientRatio_pow_four_eq_primeFactorProduct
    (n : ℕ) (hn : n ≠ 0) :
    levelTotientRatio n ^ 4 =
      ∏ p ∈ n.primeFactors,
        ((p : ℝ) / ((p - 1 : ℕ) : ℝ)) ^ 4 := by
  rw [levelTotientRatio_eq_primeFactorProduct n hn, Finset.prod_pow]

end GoldbachCircleMethodTotientRatioPrimeFactorizationV18561
