import GoldbachCircleMethodCentralLiteralSourceScaleClosedV18415
import Mathlib.NumberTheory.ArithmeticFunction.Misc

/-!
# Goldbach V1.8.416: arithmetic factor bounded by the divisor count

The finite bad-prime factor that remains in the literal central source gate is
bounded by the ordinary divisor-counting function.  This removes a targetwise
finite product from the analytic interface without asserting any asymptotic
divisor estimate.

The eventual divisor bound and the literal character-family estimate remain
external analytic inputs.  This module does not prove Goldbach.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodArithmeticFactorDivisorBoundV18416

open GoldbachCircleMethodGlobalSieveFiniteFactorV18173

/-- Every local odd-prime correction lies between one and two. -/
theorem correctionFactor_le_two {p : ℕ} (hp2 : 2 < p) :
    correctionFactor p ≤ 2 := by
  have hp2r : (2 : ℝ) < p := by exact_mod_cast hp2
  have hd : (0 : ℝ) < (p : ℝ) - 2 := by linarith
  rw [correctionFactor]
  apply (div_le_iff₀ hd).2
  have hp3r : (3 : ℝ) ≤ p := by exact_mod_cast hp2
  linarith

/-- The arithmetic correction is strictly positive. -/
theorem arithmeticFactor_pos (m : ℕ) : 0 < arithmeticFactor m := by
  unfold arithmeticFactor
  apply Finset.prod_pos
  intro p hp
  have hp2 := (Finset.mem_filter.mp hp).2
  exact lt_of_lt_of_le zero_lt_one (correctionFactor_one_le hp2)

/-- The finite arithmetic correction is no larger than the number of divisors.
This is exact finite algebra; no asymptotic divisor estimate is imported. -/
theorem arithmeticFactor_le_divisors_card {m : ℕ} (hm : 0 < m) :
    arithmeticFactor m ≤ (m.divisors.card : ℝ) := by
  let s := m.primeFactors.filter (fun p => 2 < p)
  have hs : s ⊆ m.primeFactors := Finset.filter_subset _ _
  have hlocal :
      (∏ p ∈ s, correctionFactor p) ≤ ∏ p ∈ s, (2 : ℝ) := by
    apply Finset.prod_le_prod
    · intro p hp
      exact le_trans (by positivity : (0 : ℝ) ≤ 1)
        (correctionFactor_one_le (Finset.mem_filter.mp hp).2)
    · intro p hp
      exact correctionFactor_le_two (Finset.mem_filter.mp hp).2
  have hsubset :
      (∏ _p ∈ s, (2 : ℝ)) ≤ ∏ _p ∈ m.primeFactors, (2 : ℝ) := by
    apply Finset.prod_le_prod_of_subset_of_one_le hs
    · intro _p _hp
      positivity
    · intro _p _hp _hnot
      norm_num
  have hfactorization :
      (∏ p ∈ m.primeFactors, (2 : ℝ)) ≤
        ∏ p ∈ m.primeFactors, ((m.factorization p + 1 : ℕ) : ℝ) := by
    apply Finset.prod_le_prod
    · intro _p _hp
      positivity
    · intro p hp
      have hpPrime : p.Prime := Nat.prime_of_mem_primeFactors hp
      have hpDvd : p ∣ m := Nat.dvd_of_mem_primeFactors hp
      have hfac : 1 ≤ m.factorization p :=
        (hpPrime.dvd_iff_one_le_factorization hm.ne').1 hpDvd
      exact_mod_cast (show 2 ≤ m.factorization p + 1 by omega)
  calc
    arithmeticFactor m = ∏ p ∈ s, correctionFactor p := by
      rfl
    _ ≤ ∏ p ∈ s, (2 : ℝ) := hlocal
    _ ≤ ∏ p ∈ m.primeFactors, (2 : ℝ) := hsubset
    _ ≤ ∏ p ∈ m.primeFactors, ((m.factorization p + 1 : ℕ) : ℝ) :=
      hfactorization
    _ = (m.divisors.card : ℝ) := by
      rw [Nat.card_divisors hm.ne']
      norm_cast

/-- Any explicit divisor-function bound immediately controls the exact
arithmetic factor used by the central source gate. -/
theorem arithmeticFactor_subpower_of_divisor_bound
    (C eps : ℝ) (hdivisor : ∀ n : ℕ, 0 < n →
      (n.divisors.card : ℝ) ≤ C * (n : ℝ) ^ eps)
    {m : ℕ} (hm : 0 < m) :
    arithmeticFactor m ≤ C * (m : ℝ) ^ eps :=
  (arithmeticFactor_le_divisors_card hm).trans (hdivisor m hm)

end GoldbachCircleMethodArithmeticFactorDivisorBoundV18416
