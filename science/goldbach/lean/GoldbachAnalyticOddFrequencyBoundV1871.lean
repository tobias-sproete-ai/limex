import GoldbachAnalyticOddFrequencySupportV187

/-!
# Quantitative odd-frequency coefficient, V1.8.7.1

This module gives the V1.8.6 symbol `A_N(k)` an exact finite meaning compatible
with the signed frequency convention of V1.7.8: `k = N - n - m`.  The right
coordinate is reconstructed from `N`, `k`, and the left coordinate; both
coordinates remain in `[0,N]`.

The exact research-note target `A_N(k) ≤ 2 * log(N)^2` is not assumed.  The
module proves a weaker explicit finite-range bound and preserves the odd-
frequency power-of-two support theorem from V1.8.7.  No even-frequency claim
or Goldbach claim is introduced.
-/

set_option autoImplicit false

open scoped BigOperators ArithmeticFunction.vonMangoldt

namespace GoldbachAnalyticOddFrequencyBoundV1871

open GoldbachAnalyticOddFrequencySupportV187

/-- The signed right-coordinate expression dictated by the V1.7.8 Fourier
coefficient convention `k = N - n - m`. -/
def frequencyRightExpression (N n : Nat) (k : Int) : Int :=
  (N : Int) - k - (n : Int)

/-- The corresponding natural right coordinate.  Its use in the convolution
is guarded by `frequencyRightAdmissible`. -/
def frequencyRightIndex (N n : Nat) (k : Int) : Nat :=
  (frequencyRightExpression N n k).toNat

/-- The reconstructed right coordinate exists in the same finite box
`[0,N]` as the left coordinate. -/
def frequencyRightAdmissible (N n : Nat) (k : Int) : Prop :=
  0 ≤ frequencyRightExpression N n k ∧
    frequencyRightIndex N n k ≤ N

/-- Exact finite coefficient used as `A_N(k)`.  It sums the bounded
von-Mangoldt convolution on the signed diagonal `N - n - m = k`. -/
noncomputable def A_N (N : Nat) (k : Int) : Real :=
  by
    classical
    exact ∑ n ∈ Finset.range N.succ,
      if frequencyRightAdmissible N n k then
        ArithmeticFunction.vonMangoldt n *
          ArithmeticFunction.vonMangoldt (frequencyRightIndex N n k)
      else 0

/-- An admissible reconstructed coordinate satisfies the signed diagonal
equation exactly. -/
theorem frequencyRightIndex_equation {N n : Nat} {k : Int}
    (hAdmissible : frequencyRightAdmissible N n k) :
    (n : Int) + (frequencyRightIndex N n k : Int) = (N : Int) - k := by
  have hCast : (frequencyRightIndex N n k : Int) =
      frequencyRightExpression N n k := by
    simp [frequencyRightIndex, Int.toNat_of_nonneg hAdmissible.1]
  rw [hCast]
  simp only [frequencyRightExpression]
  ring

/-- Admissibility is equivalent to the existence of a bounded natural right
coordinate on the signed diagonal.  This is the adequacy bridge from the
one-dimensional reconstruction to the V1.7.8 double-sum coefficient. -/
theorem frequencyRightAdmissible_iff_exists_bounded_diagonal
    {N n : Nat} {k : Int} :
    frequencyRightAdmissible N n k ↔
      ∃ m : Nat, m ≤ N ∧
        (N : Int) - (n : Int) - (m : Int) = k := by
  constructor
  · intro hAdmissible
    refine ⟨frequencyRightIndex N n k, hAdmissible.2, ?_⟩
    have hEquation := frequencyRightIndex_equation hAdmissible
    omega
  · rintro ⟨m, hmN, hEquation⟩
    have hExpression : frequencyRightExpression N n k = (m : Int) := by
      simp only [frequencyRightExpression]
      omega
    constructor
    · rw [hExpression]
      exact Int.natCast_nonneg m
    · simp [frequencyRightIndex, hExpression, hmN]

/-- The exact finite coefficient is nonnegative. -/
theorem A_N_nonneg (N : Nat) (k : Int) : 0 ≤ A_N N k := by
  classical
  unfold A_N
  apply Finset.sum_nonneg
  intro n hn
  split_ifs
  · exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
      ArithmeticFunction.vonMangoldt_nonneg
  · exact le_rfl

/-- Every active summand is bounded by `log(N)^2`. -/
theorem A_N_summand_le_log_sq {N n : Nat} {k : Int}
    (hn : n ∈ Finset.range N.succ)
    (hAdmissible : frequencyRightAdmissible N n k) :
    ArithmeticFunction.vonMangoldt n *
        ArithmeticFunction.vonMangoldt (frequencyRightIndex N n k) ≤
      Real.log (N : Real) ^ 2 := by
  have hnN : n ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
  have hRightN : frequencyRightIndex N n k ≤ N := hAdmissible.2
  have hLeftBound :=
    GoldbachPrimePowerDefectBoundV161.vonMangoldt_le_log_nat_of_le hnN
  have hRightBound :=
    GoldbachPrimePowerDefectBoundV161.vonMangoldt_le_log_nat_of_le hRightN
  have hLogNonneg : 0 ≤ Real.log (N : Real) :=
    Real.log_natCast_nonneg N
  calc
    ArithmeticFunction.vonMangoldt n *
          ArithmeticFunction.vonMangoldt (frequencyRightIndex N n k) ≤
        Real.log (N : Real) *
          ArithmeticFunction.vonMangoldt (frequencyRightIndex N n k) :=
      mul_le_mul_of_nonneg_right hLeftBound
        ArithmeticFunction.vonMangoldt_nonneg
    _ ≤ Real.log (N : Real) * Real.log (N : Real) :=
      mul_le_mul_of_nonneg_left hRightBound hLogNonneg
    _ = Real.log (N : Real) ^ 2 := by ring

/-- A kernel-checked explicit fallback bound.  It is weaker than the V1.8.6
odd-support target because it charges every possible left coordinate rather
than only the power-of-two support. -/
theorem A_N_le_succ_mul_log_sq (N : Nat) (k : Int) :
    A_N N k ≤ (N.succ : Real) * Real.log (N : Real) ^ 2 := by
  classical
  unfold A_N
  calc
    (∑ n ∈ Finset.range N.succ,
        if frequencyRightAdmissible N n k then
          ArithmeticFunction.vonMangoldt n *
            ArithmeticFunction.vonMangoldt (frequencyRightIndex N n k)
        else 0) ≤
        ∑ _n ∈ Finset.range N.succ, Real.log (N : Real) ^ 2 := by
      apply Finset.sum_le_sum
      intro n hn
      split_ifs with hAdmissible
      · exact A_N_summand_le_log_sq hn hAdmissible
      · positivity
    _ = (N.succ : Real) * Real.log (N : Real) ^ 2 := by simp

/-- For an even base target and a positive odd frequency in range, every
active summand of `A_N(N,k)` has a positive power of two in exactly its even
coordinate. -/
theorem positive_odd_frequency_active_summand_has_two_power_coordinate
    {N k n : Nat} (hkN : k ≤ N) (hN : Even N) (hk : Odd k)
    (hAdmissible : frequencyRightAdmissible N n (k : Int))
    (hWeight : ArithmeticFunction.vonMangoldt n *
      ArithmeticFunction.vonMangoldt
        (frequencyRightIndex N n (k : Int)) ≠ 0) :
    (∃ a : Nat, 0 < a ∧ n = 2 ^ a ∧
      Odd (frequencyRightIndex N n (k : Int))) ∨
    (∃ a : Nat, 0 < a ∧
      frequencyRightIndex N n (k : Int) = 2 ^ a ∧ Odd n) := by
  have hEquation := frequencyRightIndex_equation hAdmissible
  have hPair : n + frequencyRightIndex N n (k : Int) = N - k := by
    omega
  exact minus_odd_frequency_nonzero_product_has_two_power_coordinate
    hkN hN hk hPair hWeight

/-- The negative signed frequency `-k` corresponds to the positive target
shift `N+k`; its active odd-frequency summands obey the same support
reduction. -/
theorem negative_odd_frequency_active_summand_has_two_power_coordinate
    {N k n : Nat} (hN : Even N) (hk : Odd k)
    (hAdmissible : frequencyRightAdmissible N n (-(k : Int)))
    (hWeight : ArithmeticFunction.vonMangoldt n *
      ArithmeticFunction.vonMangoldt
        (frequencyRightIndex N n (-(k : Int))) ≠ 0) :
    (∃ a : Nat, 0 < a ∧ n = 2 ^ a ∧
      Odd (frequencyRightIndex N n (-(k : Int)))) ∨
    (∃ a : Nat, 0 < a ∧
      frequencyRightIndex N n (-(k : Int)) = 2 ^ a ∧ Odd n) := by
  have hEquation := frequencyRightIndex_equation hAdmissible
  have hPair : n + frequencyRightIndex N n (-(k : Int)) = N + k := by
    omega
  exact plus_odd_frequency_nonzero_product_has_two_power_coordinate
    hN hk hPair hWeight

end GoldbachAnalyticOddFrequencyBoundV1871
