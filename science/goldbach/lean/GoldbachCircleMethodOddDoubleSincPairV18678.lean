import GoldbachCircleMethodEvenStepDenominatorAliasNegativeWitnessV18677

/-!
# V1.8.678: odd/double denominator pair at the actual signed sinc argument

V1.8.677 proves that the Ramanujan values at `q` and `2*q` alias on even
natural targets when `q` is odd.  This append-only module transports that
identity to the integer-frequency coefficient used by the literal
Ramanujan--sinc kernel, including its actual negated argument `-k`.

Only the Ramanujan coefficient is factored in the paired denominator term.
The two sinc factors retain their distinct radii `q` and `2*q`; no equality
between them is assumed or proved.

A global classification by 2-adic denominator classes is deliberately not
introduced here: `DROHENDES UNNÖTIGES KOMPLEXITÄTSWACHSTUM` until an exact
downstream estimate demonstrates that such a partition is necessary.

No sign, size, cancellation, moment, exceptional-set, or Goldbach conclusion
is asserted.  `proof_status = NO_PROOF`.
-/

set_option autoImplicit false

open scoped Classical

namespace GoldbachCircleMethodOddDoubleSincPairV18678

open GoldbachCircleMethodEvenStepDenominatorAliasNegativeWitnessV18677
open GoldbachCircleMethodGeneralCoprimeCharacterV1868
open GoldbachCircleMethodRamanujanCoprimeBindingV1840
open GoldbachCircleMethodSignedFullPrefixV1850
open GoldbachCircleMethodOriginalMaskModelBindingV1859
open GoldbachCircleMethodOddOddSignedFiberAdapterV18665

/-- Natural nonnegative even frequencies inherit the odd/double alias. -/
theorem integerFourierRamanujan_two_mul_nat_double_eq
    (q N : Nat) [NeZero q] (hqOdd : Odd q) :
    integerFourierRamanujan (2 * q) ((2 * N : Nat) : Int)
        (Nat.mul_ne_zero (by norm_num) (NeZero.ne q)) =
      integerFourierRamanujan q ((2 * N : Nat) : Int) (NeZero.ne q) := by
  rw [integerFourierRamanujan_natCast, integerFourierRamanujan_natCast,
    finiteFourierRamanujan_eq_unitCharacterSum,
    finiteFourierRamanujan_eq_unitCharacterSum]
  exact unitCharacterSum_two_mul_even_eq q N hqOdd

/-- Negative even frequencies inherit the same alias; this lemma records the
sign route explicitly rather than silently coercing a natural target. -/
theorem integerFourierRamanujan_two_mul_neg_nat_double_eq
    (q N : Nat) [NeZero q] (hqOdd : Odd q) :
    integerFourierRamanujan (2 * q) (-((2 * N : Nat) : Int))
        (Nat.mul_ne_zero (by norm_num) (NeZero.ne q)) =
      integerFourierRamanujan q (-((2 * N : Nat) : Int)) (NeZero.ne q) := by
  rw [integerFourierRamanujan_neg, integerFourierRamanujan_neg]
  exact integerFourierRamanujan_two_mul_nat_double_eq q N hqOdd

/-- The integer-frequency form: for odd positive `q`, the coefficients at
`q` and `2*q` agree at every even integer frequency, positive or negative. -/
theorem integerFourierRamanujan_two_mul_eq_of_even
    (q : Nat) [NeZero q] (hqOdd : Odd q) (k : Int) (hkEven : Even k) :
    integerFourierRamanujan (2 * q) k
        (Nat.mul_ne_zero (by norm_num) (NeZero.ne q)) =
      integerFourierRamanujan q k (NeZero.ne q) := by
  rcases hkEven with ⟨z, rfl⟩
  rcases Int.natAbs_eq z with hz | hz
  · rw [hz]
    simpa [two_mul] using
      integerFourierRamanujan_two_mul_nat_double_eq q z.natAbs hqOdd
  · rw [hz]
    simpa [two_mul] using
      integerFourierRamanujan_two_mul_neg_nat_double_eq q z.natAbs hqOdd

/-- Exact alias at the literal coefficient argument `-k` occurring in
`explicitDenominatorSincTerm`. -/
theorem integerFourierRamanujan_two_mul_neg_eq_of_even
    (q : Nat) [NeZero q] (hqOdd : Odd q) (k : Int) (hkEven : Even k) :
    integerFourierRamanujan (2 * q) (-k)
        (Nat.mul_ne_zero (by norm_num) (NeZero.ne q)) =
      integerFourierRamanujan q (-k) (NeZero.ne q) := by
  exact integerFourierRamanujan_two_mul_eq_of_even q hqOdd (-k) hkEven.neg

/-- The radius-dependent sinc factor of one literal denominator term.  This
definition exists only to make preservation of the two radii explicit. -/
noncomputable def explicitSincRadiusFactor
    (M P R : Nat) (k : Int) (q : Denominator R) : Complex :=
  (((Real.sin
      (2 * Real.pi * (k : Real) *
        ((P : Real) / ((q.val : Real) * (M : Real)))) /
      (Real.pi * (k : Real))) : Real) : Complex)

theorem explicitDenominatorSincTerm_eq_coefficient_mul_radius
    (M P R : Nat) (k : Int) (q : Denominator R) :
    explicitDenominatorSincTerm M P R k q =
      integerFourierRamanujan q.val (-k) (NeZero.ne q.val) *
        explicitSincRadiusFactor M P R k q := by
  rfl

/-- Exact odd/double pair formula.  The coefficient aliases, while the two
different sinc radii remain as separate summands. -/
theorem explicitDenominatorSincTerm_odd_double_pair
    (M P R : Nat) (k : Int) (q q₂ : Denominator R)
    (hqOdd : Odd q.val) (hq₂ : q₂.val = 2 * q.val)
    (hkEven : Even k) :
    explicitDenominatorSincTerm M P R k q +
        explicitDenominatorSincTerm M P R k q₂ =
      integerFourierRamanujan q.val (-k) (NeZero.ne q.val) *
        (explicitSincRadiusFactor M P R k q +
          explicitSincRadiusFactor M P R k q₂) := by
  rw [explicitDenominatorSincTerm_eq_coefficient_mul_radius,
    explicitDenominatorSincTerm_eq_coefficient_mul_radius]
  have hCoeff :
      integerFourierRamanujan q₂.val (-k) (NeZero.ne q₂.val) =
        integerFourierRamanujan q.val (-k) (NeZero.ne q.val) := by
    simpa only [hq₂] using
      (integerFourierRamanujan_two_mul_neg_eq_of_even q.val hqOdd k hkEven)
  rw [hCoeff]
  ring

/-- The retained odd-odd carrier supplies a genuinely nonzero even shift, so
the exact pair formula applies at an actual off-diagonal V1.8.665 fiber. -/
theorem explicitDenominatorSincTerm_odd_double_pair_on_retained_fiber
    {M P R N t : Nat} (hN : Even N)
    (ht : t ∈ oddOddOffDiagonalSumCarrier M N)
    (q q₂ : Denominator R) (hqOdd : Odd q.val)
    (hq₂ : q₂.val = 2 * q.val) :
    let k : Int := (N : Int) - (t : Int)
    k ≠ 0 ∧
      explicitDenominatorSincTerm M P R k q +
          explicitDenominatorSincTerm M P R k q₂ =
        integerFourierRamanujan q.val (-k) (NeZero.ne q.val) *
          (explicitSincRadiusFactor M P R k q +
            explicitSincRadiusFactor M P R k q₂) := by
  dsimp only
  constructor
  · have htNe : t ≠ N := (mem_oddOddOffDiagonalSumCarrier_iff M N t).mp ht |>.2.2
    omega
  · exact explicitDenominatorSincTerm_odd_double_pair M P R
      ((N : Int) - (t : Int)) q q₂ hqOdd hq₂
      (retained_oddOdd_shift_even hN ht)

end GoldbachCircleMethodOddDoubleSincPairV18678
