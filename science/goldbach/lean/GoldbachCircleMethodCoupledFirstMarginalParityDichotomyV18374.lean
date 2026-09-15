import GoldbachCircleMethodCoupledFirstMarginalPairwisePeriodV18373

/-!
# Goldbach V1.8.374: parity dichotomy for the coupled first marginal

The active conductor has two exhaustive parity branches on even Goldbach
targets.  If it is even, the Dirichlet character vanishes pointwise because
the target is a nonunit.  If it is odd, multiplication by two is invertible
and V1.8.373 gives exact cancellation over each coprime pairwise period.

This closes the complete-period cancellation dichotomy only.  Boundary
remainders, companion-level aggregation, and the surviving second marginal
remain outside the theorem.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodCoupledFirstMarginalParityDichotomyV18374

open GoldbachCircleMethodFiniteResiduePrefixV1866
open GoldbachCircleMethodCoupledFirstMarginalPairwisePeriodV18373

/-- Every Dirichlet character modulo an even conductor vanishes at an even
natural target.  No primitivity assumption is needed. -/
theorem character_eq_zero_of_even_target_even_conductor
    (r : ℕ) [NeZero r]
    (chi : DirichletCharacter ℂ r)
    (N : ℕ) (hN : Even N) (hr : Even r) :
    chi (N : ZMod r) = 0 := by
  apply chi.map_nonunit
  intro hunit
  have hcop : Nat.Coprime N r :=
    (ZMod.isUnit_iff_coprime N r).mp hunit
  have hnot : ¬ Nat.Coprime N r := by
    rw [Nat.Prime.not_coprime_iff_dvd]
    exact ⟨2, Nat.prime_two, even_iff_two_dvd.mp hN,
      even_iff_two_dvd.mp hr⟩
  exact hnot hcop

/-- The actual linear character--Ramanujan product vanishes pointwise on the
even-target/even-conductor branch. -/
theorem coupled_first_marginal_eq_zero_of_even_conductor
    (r l : ℕ) [NeZero r] [NeZero l]
    (chi : DirichletCharacter ℂ r)
    (N : ℕ) (hN : Even N) (hr : Even r) :
    (((ArithmeticFunction.moebius r : ℤ) : ℂ) * chi (N : ZMod r)) *
        unitCharacterSum l (N : ZMod l) = 0 := by
  rw [character_eq_zero_of_even_target_even_conductor r chi N hN hr]
  simp

/-- Oddness of the active conductor is exactly the arithmetic gate needed to
make the even-target step `2` invertible. -/
theorem coprime_two_of_not_even
    (r : ℕ) (hr : ¬ Even r) :
    Nat.Coprime 2 r := by
  apply Nat.prime_two.coprime_iff_not_dvd.mpr
  intro htwo
  exact hr (even_iff_two_dvd.mpr htwo)

/-- Exhaustive source-level parity dichotomy.  The even-conductor branch is
pointwise zero on even targets; the odd-conductor branch cancels over every
complete coprime pairwise period `r*l`. -/
theorem coupled_first_marginal_parity_dichotomy
    (r l : ℕ) [NeZero r] [NeZero l]
    (hcop : Nat.Coprime r l)
    (chi : DirichletCharacter ℂ r) (hne : chi ≠ 1)
    (A : ℕ) :
    (Even r → ∀ N : ℕ, Even N →
      (((ArithmeticFunction.moebius r : ℤ) : ℂ) * chi (N : ZMod r)) *
        unitCharacterSum l (N : ZMod l) = 0) ∧
    (¬ Even r →
      (∑ x : ZMod (r * l),
        (((ArithmeticFunction.moebius r : ℤ) : ℂ) *
            chi ((A : ZMod r) + ((2 : ℕ) : ZMod r) *
              ZMod.castHom (Nat.dvd_mul_right r l) (ZMod r) x)) *
          unitCharacterSum l
            ((A : ZMod l) + ((2 : ℕ) : ZMod l) *
              ZMod.castHom (Nat.dvd_mul_left l r) (ZMod l) x)) = 0) := by
  constructor
  · intro hr N hN
    exact coupled_first_marginal_eq_zero_of_even_conductor r l chi N hN hr
  · intro hr
    exact even_target_character_ramanujan_complete_period_eq_zero
      r l hcop chi hne A (coprime_two_of_not_even r hr)

end GoldbachCircleMethodCoupledFirstMarginalParityDichotomyV18374
