import GoldbachCircleMethodCentralArithmeticPrefixReductionV18426
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Goldbach V1.8.428: arithmetic-factor positive convolution

The correction product is expanded exactly into a positive finite convolution
over subsets of odd prime divisors.  Each local increment `1/(p-2)` is then
majorized by `3/p`.  This is the first kernel step toward a linear prefix mean
for `arithmeticFactor`; it does not yet sum the divisor convolution over `n`.

No asymptotic theorem is asserted and `proof_status = NO_PROOF`.
-/

set_option autoImplicit false

open scoped BigOperators Classical ArithmeticFunction

namespace GoldbachCircleMethodArithmeticFactorPositiveConvolutionV18428

open GoldbachCircleMethodGlobalSieveFiniteFactorV18173

/-- Odd prime support used by `arithmeticFactor`. -/
def oddPrimeFactors (n : ℕ) : Finset ℕ :=
  n.primeFactors.filter (fun p => 2 < p)

/-- Positive local increment in `(p-1)/(p-2) = 1 + 1/(p-2)`. -/
noncomputable def arithmeticIncrement (p : ℕ) : ℝ :=
  1 / ((p : ℝ) - 2)

/-- Exact local additive form of the correction factor. -/
theorem correctionFactor_eq_one_add_increment {p : ℕ} (hp : 2 < p) :
    correctionFactor p = 1 + arithmeticIncrement p := by
  have hpR : (2 : ℝ) < p := by exact_mod_cast hp
  have hden : (p : ℝ) - 2 ≠ 0 := by linarith
  unfold correctionFactor arithmeticIncrement
  field_simp
  ring

theorem arithmeticIncrement_nonneg {p : ℕ} (hp : 2 < p) :
    0 ≤ arithmeticIncrement p := by
  have hpR : (2 : ℝ) < p := by exact_mod_cast hp
  have hden : (0 : ℝ) < (p : ℝ) - 2 := by linarith
  unfold arithmeticIncrement
  exact one_div_nonneg.mpr (le_of_lt hden)

/-- A deliberately elementary local majorant. -/
theorem arithmeticIncrement_le_three_div {p : ℕ} (hp : 2 < p) :
    arithmeticIncrement p ≤ 3 / (p : ℝ) := by
  have hp3 : 3 ≤ p := hp
  have hp3R : (3 : ℝ) ≤ p := by exact_mod_cast hp3
  have hpR : (2 : ℝ) < p := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < p := by positivity
  have hden : (0 : ℝ) < (p : ℝ) - 2 := by linarith
  unfold arithmeticIncrement
  rw [div_le_div_iff₀ hden hp0]
  linarith

/-- Exact positive powerset expansion of the arithmetic factor. -/
theorem arithmeticFactor_eq_positive_powerset_sum (n : ℕ) :
    arithmeticFactor n =
      ∑ t ∈ (oddPrimeFactors n).powerset,
        ∏ p ∈ t, arithmeticIncrement p := by
  unfold arithmeticFactor oddPrimeFactors
  let s := n.primeFactors.filter (fun p => 2 < p)
  calc
    (∏ p ∈ s, correctionFactor p) =
        ∏ p ∈ s, (1 + arithmeticIncrement p) := by
          apply Finset.prod_congr rfl
          intro p hp
          rw [correctionFactor_eq_one_add_increment (Finset.mem_filter.mp hp).2]
    _ = ∑ t ∈ s.powerset, ∏ p ∈ t, arithmeticIncrement p :=
      Finset.prod_one_add s

/-- Product majorant attached to a finite prime subset. -/
noncomputable def arithmeticSubsetMajorant (t : Finset ℕ) : ℝ :=
  ∏ p ∈ t, 3 / (p : ℝ)

theorem arithmeticSubsetMajorant_nonneg (t : Finset ℕ) :
    0 ≤ arithmeticSubsetMajorant t := by
  unfold arithmeticSubsetMajorant
  positivity

/-- Every subset term is bounded by the elementary `3/p` product. -/
theorem arithmeticIncrement_subset_le_majorant
    {n : ℕ} {t : Finset ℕ} (ht : t ⊆ oddPrimeFactors n) :
    (∏ p ∈ t, arithmeticIncrement p) ≤ arithmeticSubsetMajorant t := by
  unfold arithmeticSubsetMajorant
  apply Finset.prod_le_prod
  · intro p hp
    have hpOdd : 2 < p := (Finset.mem_filter.mp (ht hp)).2
    exact arithmeticIncrement_nonneg hpOdd
  · intro p hp
    have hpOdd : 2 < p := (Finset.mem_filter.mp (ht hp)).2
    exact arithmeticIncrement_le_three_div hpOdd

/-- Finite positive-convolution majorant for the complete arithmetic factor. -/
theorem arithmeticFactor_le_positive_powerset_majorant (n : ℕ) :
    arithmeticFactor n ≤
      ∑ t ∈ (oddPrimeFactors n).powerset, arithmeticSubsetMajorant t := by
  rw [arithmeticFactor_eq_positive_powerset_sum]
  apply Finset.sum_le_sum
  intro t ht
  exact arithmeticIncrement_subset_le_majorant (Finset.mem_powerset.mp ht)

end GoldbachCircleMethodArithmeticFactorPositiveConvolutionV18428
