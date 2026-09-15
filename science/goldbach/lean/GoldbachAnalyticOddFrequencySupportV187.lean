import GoldbachCircleMethodCentralBandCorrelationV178

/-!
# Arithmetic support at odd frequencies, V1.8.7

This module kernelizes only the arithmetic support reduction used by the
V1.8.6 research note. For even `N` and odd `k`, both `N + k` and, when
`k ≤ N`, `N - k` are odd. Hence a decomposition of either target has
exactly one even coordinate. A nonzero von Mangoldt weight on that coordinate
forces it to be a positive power of two.

No cardinality estimate for powers of two, convolution bound, Fourier
estimate, or Goldbach result is introduced here.
-/

set_option autoImplicit false

open scoped ArithmeticFunction.vonMangoldt

namespace GoldbachAnalyticOddFrequencySupportV187

/-- The finite set of positive exponents available to powers of two bounded
by `N`. The exact connection to the inequality `2 ^ a ≤ N` is proved below
for nonzero `N`. -/
def twoPowerExponentsUpTo (N : Nat) : Finset Nat :=
  (Finset.range (Nat.log 2 N + 1)).erase 0

/-- Membership in `twoPowerExponentsUpTo` is exactly positivity of the
exponent together with the bound `2 ^ a ≤ N`. -/
theorem mem_twoPowerExponentsUpTo_iff {N a : Nat} (hN : N ≠ 0) :
    a ∈ twoPowerExponentsUpTo N ↔ 0 < a ∧ 2 ^ a ≤ N := by
  simp [twoPowerExponentsUpTo, Nat.pos_iff_ne_zero,
    Nat.le_log_iff_pow_le Nat.one_lt_two hN]

/-- There are exactly `Nat.log 2 N` positive exponent slots in the finite
support set. -/
theorem card_twoPowerExponentsUpTo (N : Nat) :
    (twoPowerExponentsUpTo N).card = Nat.log 2 N := by
  simp [twoPowerExponentsUpTo]

/-- An even target plus an odd frequency is odd. -/
theorem even_add_odd_frequency_is_odd {N k : Nat}
    (hN : Even N) (hk : Odd k) : Odd (N + k) :=
  hN.add_odd hk

/-- Under the natural-range condition, an even target minus an odd frequency
is odd. The range condition prevents truncated natural subtraction. -/
theorem even_sub_odd_frequency_is_odd {N k : Nat}
    (hkN : k ≤ N) (hN : Even N) (hk : Odd k) : Odd (N - k) :=
  Nat.Even.sub_odd hkN hN hk

/-- A decomposition of an odd natural number has exactly one even coordinate,
recorded together with the oddness of the other coordinate. -/
theorem odd_sum_has_exactly_one_even_coordinate {m n : Nat}
    (hOdd : Odd (m + n)) :
    (Even m ∧ Odd n) ∨ (Odd m ∧ Even n) := by
  rcases Nat.even_or_odd m with hmEven | hmOdd
  · left
    exact ⟨hmEven, (Nat.odd_add'.mp hOdd).mpr hmEven⟩
  · right
    exact ⟨hmOdd, (Nat.odd_add.mp hOdd).mp hmOdd⟩

/-- Every even natural prime power is a positive power of the unique even
prime, namely two. -/
theorem even_prime_power_eq_two_pow {x : Nat}
    (hxEven : Even x) (hxPrimePow : IsPrimePow x) :
    ∃ a : Nat, 0 < a ∧ x = 2 ^ a := by
  rw [isPrimePow_nat_iff] at hxPrimePow
  rcases hxPrimePow with ⟨p, a, hp, ha, hpa⟩
  have hPowEven : Even (p ^ a) := by
    rwa [hpa]
  have hpEven : Even p :=
    (Nat.even_pow' ha.ne').mp hPowEven
  have hpTwo : p = 2 := hp.even_iff.mp hpEven
  exact ⟨a, ha, by simpa [hpTwo] using hpa.symm⟩

/-- A nonzero von Mangoldt value on an even coordinate supplies an explicit
positive exponent witnessing that the coordinate is a power of two. -/
theorem even_vonMangoldt_support_eq_two_pow {x : Nat}
    (hxEven : Even x)
    (hxWeight : ArithmeticFunction.vonMangoldt x ≠ 0) :
    ∃ a : Nat, 0 < a ∧ x = 2 ^ a :=
  even_prime_power_eq_two_pow hxEven
    (ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hxWeight)

/-- On the even nonzero support, the von Mangoldt value is exactly `log 2`. -/
theorem even_vonMangoldt_support_weight_eq_log_two {x : Nat}
    (hxEven : Even x)
    (hxWeight : ArithmeticFunction.vonMangoldt x ≠ 0) :
    ArithmeticFunction.vonMangoldt x = Real.log 2 := by
  rcases even_vonMangoldt_support_eq_two_pow hxEven hxWeight with
    ⟨a, ha, rfl⟩
  rw [ArithmeticFunction.vonMangoldt_apply_pow ha.ne',
    ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
  norm_num

/-- A nonzero von Mangoldt product over an odd sum has a positive power of
two in exactly the even coordinate. -/
theorem odd_sum_nonzero_vonMangoldt_product_has_two_power_coordinate
    {m n : Nat} (hOdd : Odd (m + n))
    (hWeight : ArithmeticFunction.vonMangoldt m *
      ArithmeticFunction.vonMangoldt n ≠ 0) :
    (∃ a : Nat, 0 < a ∧ m = 2 ^ a ∧ Odd n) ∨
      (∃ a : Nat, 0 < a ∧ n = 2 ^ a ∧ Odd m) := by
  have hmWeight : ArithmeticFunction.vonMangoldt m ≠ 0 := by
    intro hmZero
    apply hWeight
    rw [hmZero, zero_mul]
  have hnWeight : ArithmeticFunction.vonMangoldt n ≠ 0 := by
    intro hnZero
    apply hWeight
    rw [hnZero, mul_zero]
  rcases odd_sum_has_exactly_one_even_coordinate hOdd with
    ⟨hmEven, hnOdd⟩ | ⟨hmOdd, hnEven⟩
  · left
    rcases even_vonMangoldt_support_eq_two_pow hmEven hmWeight with
      ⟨a, ha, hma⟩
    exact ⟨a, ha, hma, hnOdd⟩
  · right
    rcases even_vonMangoldt_support_eq_two_pow hnEven hnWeight with
      ⟨a, ha, hna⟩
    exact ⟨a, ha, hna, hmOdd⟩

/-- Exact parity split for a decomposition at the positive odd frequency
shift `N + k`. -/
theorem plus_odd_frequency_pair_has_exactly_one_even_coordinate
    {N k m n : Nat} (hN : Even N) (hk : Odd k)
    (hPair : m + n = N + k) :
    (Even m ∧ Odd n) ∨ (Odd m ∧ Even n) := by
  apply odd_sum_has_exactly_one_even_coordinate
  rw [hPair]
  exact even_add_odd_frequency_is_odd hN hk

/-- Exact parity split for a decomposition at the truncated-safe negative
odd frequency shift `N - k`. -/
theorem minus_odd_frequency_pair_has_exactly_one_even_coordinate
    {N k m n : Nat} (hkN : k ≤ N) (hN : Even N) (hk : Odd k)
    (hPair : m + n = N - k) :
    (Even m ∧ Odd n) ∨ (Odd m ∧ Even n) := by
  apply odd_sum_has_exactly_one_even_coordinate
  rw [hPair]
  exact even_sub_odd_frequency_is_odd hkN hN hk

/-- Nonzero von Mangoldt support at the positive odd frequency shift has a
power-of-two coordinate. -/
theorem plus_odd_frequency_nonzero_product_has_two_power_coordinate
    {N k m n : Nat} (hN : Even N) (hk : Odd k)
    (hPair : m + n = N + k)
    (hWeight : ArithmeticFunction.vonMangoldt m *
      ArithmeticFunction.vonMangoldt n ≠ 0) :
    (∃ a : Nat, 0 < a ∧ m = 2 ^ a ∧ Odd n) ∨
      (∃ a : Nat, 0 < a ∧ n = 2 ^ a ∧ Odd m) := by
  have hOdd : Odd (m + n) := by
    rw [hPair]
    exact even_add_odd_frequency_is_odd hN hk
  exact odd_sum_nonzero_vonMangoldt_product_has_two_power_coordinate
    hOdd hWeight

/-- Nonzero von Mangoldt support at the truncated-safe negative odd frequency
shift has a power-of-two coordinate. -/
theorem minus_odd_frequency_nonzero_product_has_two_power_coordinate
    {N k m n : Nat} (hkN : k ≤ N) (hN : Even N) (hk : Odd k)
    (hPair : m + n = N - k)
    (hWeight : ArithmeticFunction.vonMangoldt m *
      ArithmeticFunction.vonMangoldt n ≠ 0) :
    (∃ a : Nat, 0 < a ∧ m = 2 ^ a ∧ Odd n) ∨
      (∃ a : Nat, 0 < a ∧ n = 2 ^ a ∧ Odd m) := by
  have hOdd : Odd (m + n) := by
    rw [hPair]
    exact even_sub_odd_frequency_is_odd hkN hN hk
  exact odd_sum_nonzero_vonMangoldt_product_has_two_power_coordinate
    hOdd hWeight

end GoldbachAnalyticOddFrequencySupportV187
