import GoldbachCircleMethodOddOddEvenSmallKernelFormulaV18673

/-!
# V1.8.677: even-step denominator aliasing

Complete-period orthogonality at distinct denominators cannot be transferred
unchanged to a progression of even targets.  For every odd positive `q`, the
Ramanujan values at denominators `q` and `2*q` agree pointwise on `2*N`.

The smallest nontrivial instance is `q=3`: over the three even targets
`0,2,4`, the cross-correlation of the denominator-three and denominator-six
values is exactly `6`, not zero.  This is a typed negative witness against a
naive distinct-denominator orthogonality shortcut.  It supplies no estimate
for the actual weighted Goldbach coefficient and no Goldbach conclusion.

`proof_status = NO_PROOF`.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodEvenStepDenominatorAliasNegativeWitnessV18677

open GoldbachCircleMethodFiniteResiduePrefixV1866
open GoldbachCircleMethodGeneralCoprimeCharacterV1868
open GoldbachCircleMethodRamanujanCoprimeBindingV1840
open GoldbachCircleMethodRamanujanCharacterProductV1843
open GoldbachCircleMethodFullSquarefreeCoefficientV1847

/-- Odd moduli are coprime to two. -/
theorem two_coprime_of_odd {q : Nat} (hqOdd : Odd q) : Nat.Coprime 2 q := by
  rw [Nat.coprime_two_left]
  exact hqOdd

/-- General even-step alias: for every odd positive modulus `q`, the actual
Ramanujan values at denominators `q` and `2*q` coincide on every even target.
This is an exact finite identity, not an estimate. -/
theorem unitCharacterSum_two_mul_even_eq
    (q N : Nat) [NeZero q] (hqOdd : Odd q) :
    @unitCharacterSum (2 * q) ⟨Nat.mul_ne_zero (by norm_num) (NeZero.ne q)⟩
        ((2 * N : Nat) : ZMod (2 * q)) =
      unitCharacterSum q ((2 * N : Nat) : ZMod q) := by
  rw [← finiteFourierRamanujan_eq_unitCharacterSum (2 * q) (2 * N)
      (Nat.mul_ne_zero (by norm_num) (NeZero.ne q)),
    ← finiteFourierRamanujan_eq_unitCharacterSum q (2 * N) (NeZero.ne q),
    finiteFourierRamanujan_mul_of_coprime (by norm_num) (NeZero.ne q)
      (two_coprime_of_odd hqOdd) (2 * N),
    finiteFourierRamanujan_eq_totient_of_dvd (by norm_num) (by exact dvd_mul_right 2 N)]
  norm_num

/-- The denominator-three value at target zero. -/
theorem unitCharacterSum_three_zero :
    @unitCharacterSum 3 ⟨by norm_num⟩ (0 : ZMod 3) = 2 := by
  change @unitCharacterSum 3 ⟨by norm_num⟩ ((0 : Nat) : ZMod 3) = 2
  rw [← finiteFourierRamanujan_eq_unitCharacterSum 3 0 (by norm_num),
    finiteFourierRamanujan_eq_totient_of_dvd (by norm_num) (by norm_num)]
  have ht : Nat.totient 3 = 2 := by decide
  rw [ht]
  norm_num

/-- The denominator-three value at target two. -/
theorem unitCharacterSum_three_two :
    @unitCharacterSum 3 ⟨by norm_num⟩ (2 : ZMod 3) = -1 := by
  change @unitCharacterSum 3 ⟨by norm_num⟩ ((2 : Nat) : ZMod 3) = -1
  rw [← finiteFourierRamanujan_eq_unitCharacterSum 3 2 (by norm_num),
    finiteFourierRamanujan_eq_neg_one_of_prime (by norm_num) (by norm_num)]

/-- The denominator-three value at target four. -/
theorem unitCharacterSum_three_four :
    @unitCharacterSum 3 ⟨by norm_num⟩ (4 : ZMod 3) = -1 := by
  change @unitCharacterSum 3 ⟨by norm_num⟩ ((4 : Nat) : ZMod 3) = -1
  rw [← finiteFourierRamanujan_eq_unitCharacterSum 3 4 (by norm_num),
    finiteFourierRamanujan_eq_neg_one_of_prime (by norm_num) (by norm_num)]

/-- Denominator six aliases denominator three at target zero. -/
theorem unitCharacterSum_six_zero :
    @unitCharacterSum 6 ⟨by norm_num⟩ (0 : ZMod 6) = 2 := by
  rw [show @unitCharacterSum 6 ⟨by norm_num⟩ (0 : ZMod 6) =
      @unitCharacterSum 3 ⟨by norm_num⟩ (0 : ZMod 3) by
        simpa using unitCharacterSum_two_mul_even_eq 3 0 (by norm_num),
    unitCharacterSum_three_zero]

/-- Denominator six aliases denominator three at target two. -/
theorem unitCharacterSum_six_two :
    @unitCharacterSum 6 ⟨by norm_num⟩ (2 : ZMod 6) = -1 := by
  rw [show @unitCharacterSum 6 ⟨by norm_num⟩ (2 : ZMod 6) =
      @unitCharacterSum 3 ⟨by norm_num⟩ (2 : ZMod 3) by
        simpa using unitCharacterSum_two_mul_even_eq 3 1 (by norm_num),
    unitCharacterSum_three_two]

/-- Denominator six aliases denominator three at target four. -/
theorem unitCharacterSum_six_four :
    @unitCharacterSum 6 ⟨by norm_num⟩ (4 : ZMod 6) = -1 := by
  rw [show @unitCharacterSum 6 ⟨by norm_num⟩ (4 : ZMod 6) =
      @unitCharacterSum 3 ⟨by norm_num⟩ (4 : ZMod 3) by
        simpa using unitCharacterSum_two_mul_even_eq 3 2 (by norm_num),
    unitCharacterSum_three_four]

/-- The exact denominator-three/denominator-six cross-correlation on the
smallest complete even-step period. -/
noncomputable def threeSixEvenStepCorrelation : Complex :=
  ∑ i ∈ Finset.range 3,
    @unitCharacterSum 3 ⟨by norm_num⟩ ((2 * i : Nat) : ZMod 3) *
      @unitCharacterSum 6 ⟨by norm_num⟩ ((2 * i : Nat) : ZMod 6)

/-- Exact negative witness: the distinct denominators `3` and `6` have
cross-correlation `6`, rather than zero, on even targets. -/
theorem threeSixEvenStepCorrelation_eq_six :
    threeSixEvenStepCorrelation = 6 := by
  unfold threeSixEvenStepCorrelation
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  norm_num only [Nat.cast_zero, Nat.cast_ofNat]
  rw [unitCharacterSum_six_zero, unitCharacterSum_six_two,
    unitCharacterSum_six_four, unitCharacterSum_three_zero,
    unitCharacterSum_three_two, unitCharacterSum_three_four]
  norm_num

/-- Therefore the even-step cross-correlation is not zero. -/
theorem threeSixEvenStepCorrelation_ne_zero :
    threeSixEvenStepCorrelation ≠ 0 := by
  rw [threeSixEvenStepCorrelation_eq_six]
  norm_num

end GoldbachCircleMethodEvenStepDenominatorAliasNegativeWitnessV18677
