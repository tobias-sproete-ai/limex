import GoldbachCircleMethodTotientFourthEulerExponentialV18569
import Mathlib.Analysis.PSeries

/-!
# Goldbach V1.8.570: uniform bound for the Euler exponent

The prime reciprocal-square exponent is embedded into the full interval and
bounded by the standard finite telescoping estimate from `Mathlib.Analysis.PSeries`.
No numerical approximation or infinite Euler-product identity is used.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodTotientFourthEulerExponentBoundV18570

open GoldbachCircleMethodTotientFourthFiniteEulerProductV18568
open GoldbachCircleMethodTotientFourthEulerExponentialV18569

theorem primePrefixCarrier_subset_Icc (Q : ℕ) :
    primePrefixCarrier Q ⊆ Finset.Icc 2 Q := by
  exact Finset.filter_subset _ _

theorem Icc_two_eq_Ioc_one (Q : ℕ) :
    Finset.Icc 2 Q = Finset.Ioc 1 Q := by
  ext n
  simp only [Finset.mem_Icc, Finset.mem_Ioc]
  omega

theorem reciprocalSquare_Icc_le_one (Q : ℕ) :
    (∑ n ∈ Finset.Icc 2 Q, (((n : ℝ) ^ 2)⁻¹)) ≤ 1 := by
  by_cases hQ : 1 ≤ Q
  · rw [Icc_two_eq_Ioc_one]
    calc
      (∑ n ∈ Finset.Ioc 1 Q, (((n : ℝ) ^ 2)⁻¹)) ≤
          ((((1 : ℕ) : ℝ))⁻¹ - ((Q : ℝ)⁻¹)) :=
        sum_Ioc_inv_sq_le_sub (α := ℝ) one_ne_zero hQ
      _ ≤ 1 := by
        rw [Nat.cast_one, inv_one]
        exact sub_le_self (1 : ℝ)
          (inv_nonneg.mpr (Nat.cast_nonneg Q))
  · have hQ0 : Q = 0 := by omega
    subst Q
    simp

theorem primeReciprocalSquareSum_le_one (Q : ℕ) :
    (∑ p ∈ primePrefixCarrier Q, (((p : ℝ) ^ 2)⁻¹)) ≤ 1 := by
  calc
    (∑ p ∈ primePrefixCarrier Q, (((p : ℝ) ^ 2)⁻¹)) ≤
        ∑ n ∈ Finset.Icc 2 Q, (((n : ℝ) ^ 2)⁻¹) := by
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (primePrefixCarrier_subset_Icc Q)
        (fun n _hn _hnot => by positivity)
    _ ≤ 1 := reciprocalSquare_Icc_le_one Q

/-- Uniform, explicit upper bound for the exponent of the finite Euler-product
majorant. -/
theorem primeFourthEulerExponent_le_thirty (Q : ℕ) :
    primeFourthEulerExponent Q ≤ 30 := by
  unfold primeFourthEulerExponent
  calc
    (∑ p ∈ primePrefixCarrier Q, (30 : ℝ) / (p : ℝ) ^ 2) =
        30 * ∑ p ∈ primePrefixCarrier Q, (((p : ℝ) ^ 2)⁻¹) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      simp only [div_eq_mul_inv]
    _ ≤ 30 * 1 := by
      exact mul_le_mul_of_nonneg_left
        (primeReciprocalSquareSum_le_one Q) (by norm_num)
    _ = 30 := by norm_num

end GoldbachCircleMethodTotientFourthEulerExponentBoundV18570
