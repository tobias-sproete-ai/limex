import GoldbachCircleMethodCentralArithmeticMeanBudgetV18424
import GoldbachCircleMethodArithmeticFactorDivisorBoundV18416

/-!
# Goldbach V1.8.426: central arithmetic-factor prefix reduction

The exact central targets are `2 * (5*m+i)`.  Because `arithmeticFactor`
ignores the prime `2`, its central mean is an interval sum on the consecutive
integers `[5*m,7*m]`.  Positivity then bounds that interval by the full prefix
through `7*m`.

Thus the remaining mean-value input need not be a short-interval theorem: a
global linear prefix estimate is sufficient, at the explicit factor-four
cost.  The prefix estimate itself remains an analytic premise and
`proof_status = NO_PROOF`.
-/

set_option autoImplicit false

open scoped BigOperators Classical ArithmeticFunction

namespace GoldbachCircleMethodCentralArithmeticPrefixReductionV18426

open GoldbachCircleMethodArithmeticFactorDivisorBoundV18416
open GoldbachCircleMethodCanonicalCentralAdjustedPositiveV18403
open GoldbachCircleMethodCentralArithmeticMeanBudgetV18424
open GoldbachCircleMethodGlobalSieveFiniteFactorV18173
open GoldbachCircleMethodMertensProductFromHarmonicV18174

/-- Multiplication by two does not change the odd-prime correction product. -/
theorem arithmeticFactor_two_mul (n : ℕ) (hn : 0 < n) :
    arithmeticFactor (2 * n) = arithmeticFactor n := by
  unfold arithmeticFactor
  rw [Nat.primeFactors_mul (by norm_num) hn.ne']
  have htwo : Nat.primeFactors 2 = {2} := Nat.Prime.primeFactors Nat.prime_two
  rw [htwo]
  have hset : ({2} ∪ n.primeFactors).filter (fun p => 2 < p) =
      n.primeFactors.filter (fun p => 2 < p) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_singleton]
    constructor
    · rintro ⟨hp | hp, hpgt⟩
      · omega
      · exact ⟨hp, hpgt⟩
    · rintro ⟨hp, hpgt⟩
      exact ⟨Or.inr hp, hpgt⟩
  rw [hset]

/-- The canonical central target has a factor two and a consecutive base. -/
theorem centralTargetNat_eq_two_mul_base (m i : ℕ) :
    centralTargetNat m i = 2 * (5 * m + i) := by
  simp only [centralTargetNat]
  omega

/-- Consecutive-base form of the central arithmetic-factor mass. -/
noncomputable def centralBaseArithmeticFactorSum (m : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (2 * m + 1), arithmeticFactor (5 * m + i)

/-- Prefix mass used by the remaining standard mean-value interface. -/
noncomputable def arithmeticFactorPrefixSum (X : ℕ) : ℝ :=
  ∑ n ∈ Finset.range X, arithmeticFactor n

/-- Exact removal of the harmless factor two from every central target. -/
theorem centralArithmeticFactorSum_eq_base (m : ℕ) (hm : 1 ≤ m) :
    centralArithmeticFactorSum m = centralBaseArithmeticFactorSum m := by
  unfold centralArithmeticFactorSum centralBaseArithmeticFactorSum
  apply Finset.sum_congr rfl
  intro i hi
  rw [centralTargetNat_eq_two_mul_base,
    arithmeticFactor_two_mul (5 * m + i) (by omega)]

/-- The shifted range is exactly the closed integer interval `[5*m,7*m]`. -/
theorem centralBaseArithmeticFactorSum_eq_Ico (m : ℕ) :
    centralBaseArithmeticFactorSum m =
      ∑ n ∈ Finset.Ico (5 * m) (7 * m + 1), arithmeticFactor n := by
  have h := Finset.sum_Ico_eq_sum_range arithmeticFactor (5 * m) (7 * m + 1)
  unfold centralBaseArithmeticFactorSum
  have hdiff : 7 * m + 1 - 5 * m = 2 * m + 1 := by omega
  simpa only [hdiff] using h.symm

/-- Positivity embeds the central interval into the full prefix through
`7*m`. -/
theorem centralArithmeticFactorSum_le_prefix (m : ℕ) (hm : 1 ≤ m) :
    centralArithmeticFactorSum m ≤ arithmeticFactorPrefixSum (7 * m + 1) := by
  rw [centralArithmeticFactorSum_eq_base m hm,
    centralBaseArithmeticFactorSum_eq_Ico]
  unfold arithmeticFactorPrefixSum
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro n hn
    exact Finset.mem_range.mpr (Finset.mem_Ico.mp hn).2
  · intro n hn _hnot
    exact arithmeticFactor_nonneg n

/-- A linear full-prefix estimate yields the central mean bound required by
V1.8.424.  No short-interval theorem is needed. -/
theorem centralArithmeticFactorSum_le_four_mul_of_prefix_bound
    (Cmean : ℝ) (m : ℕ) (hm : 1 ≤ m) (hCmean : 0 ≤ Cmean)
    (hprefix : arithmeticFactorPrefixSum (7 * m + 1) ≤
      Cmean * (7 * m + 1 : ℕ)) :
    centralArithmeticFactorSum m ≤
      (4 * Cmean) * (2 * m + 1 : ℕ) := by
  have hcentral := (centralArithmeticFactorSum_le_prefix m hm).trans hprefix
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  push_cast at hcentral ⊢
  nlinarith

end GoldbachCircleMethodCentralArithmeticPrefixReductionV18426
