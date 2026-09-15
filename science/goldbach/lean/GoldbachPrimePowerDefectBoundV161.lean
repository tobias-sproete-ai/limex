import GoldbachVonMangoldtDecompositionV16
import Mathlib.NumberTheory.Chebyshev

/-!
# Quantitative prime-power defect bound, V1.6.1 candidate

This module bounds the exact complementary defect from V1.6 by a finite
Chebyshev mass. It does not prove a main-term lower bound or binary Goldbach.
-/

set_option autoImplicit false

open scoped BigOperators ArithmeticFunction.vonMangoldt Chebyshev

namespace GoldbachPrimePowerDefectBoundV161

open GoldbachVonMangoldtDecompositionV16

/-- Total von Mangoldt mass on the non-prime integers in `[0,N]`. -/
noncomputable def nonPrimeVonMangoldtMass (N : Nat) : Real :=
  ∑ n ∈ Finset.Icc 0 N with ¬ Nat.Prime n,
    ArithmeticFunction.vonMangoldt n

/-- The finite non-prime von Mangoldt mass is exactly `psi(N)-theta(N)`. -/
theorem nonPrimeVonMangoldtMass_eq_psi_sub_theta (N : Nat) :
    nonPrimeVonMangoldtMass N = Chebyshev.psi N - Chebyshev.theta N := by
  rw [Chebyshev.psi_sub_theta_eq_sum_not_prime]
  rw [show (⌊(N : Real)⌋₊ : Nat) = N by simp]
  simp only [nonPrimeVonMangoldtMass]
  symm
  apply Finset.sum_subset
  · intro n hn
    rcases Finset.mem_filter.mp hn with ⟨hnIoc, hnNotPrime⟩
    rcases Finset.mem_Ioc.mp hnIoc with ⟨_, hnN⟩
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨Nat.zero_le n, hnN⟩, hnNotPrime⟩
  · intro n hnIcc hnNotIoc
    rcases Finset.mem_filter.mp hnIcc with ⟨hnIccBounds, hnNotPrime⟩
    rcases Finset.mem_Icc.mp hnIccBounds with ⟨_, hnN⟩
    have hnZero : n = 0 := by
      by_contra hnNe
      have hnPos : 0 < n := Nat.pos_of_ne_zero hnNe
      exact hnNotIoc (Finset.mem_filter.mpr
        ⟨Finset.mem_Ioc.mpr ⟨hnPos, hnN⟩, hnNotPrime⟩)
    subst n
    simp

/-- The one-sided non-prime mass over the left coordinate. -/
noncomputable def leftNonPrimeMass (N : Nat) : Real :=
  ∑ n ∈ (Finset.range N).filter (fun n => ¬ Nat.Prime n),
    ArithmeticFunction.vonMangoldt n

/-- The one-sided non-prime mass over the reflected right coordinate. -/
noncomputable def rightNonPrimeMass (N : Nat) : Real :=
  ∑ n ∈ (Finset.range N).filter (fun n => ¬ Nat.Prime (N - n)),
    ArithmeticFunction.vonMangoldt (N - n)

theorem leftNonPrimeMass_le_total (N : Nat) :
    leftNonPrimeMass N ≤ nonPrimeVonMangoldtMass N := by
  classical
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro n hn
    rcases Finset.mem_filter.mp hn with ⟨hnRange, hnNotPrime⟩
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr
        ⟨Nat.zero_le n, Nat.le_of_lt (Finset.mem_range.mp hnRange)⟩,
        hnNotPrime⟩
  · intro n _ _
    exact ArithmeticFunction.vonMangoldt_nonneg

theorem rightNonPrimeMass_eq_total (N : Nat) :
    rightNonPrimeMass N = nonPrimeVonMangoldtMass N := by
  classical
  rw [rightNonPrimeMass, nonPrimeVonMangoldtMass]
  simp_rw [Finset.sum_filter]
  rw [show Finset.Icc 0 N = Finset.range (N + 1) by ext n; simp]
  let g : Nat → Real := fun j =>
    if ¬ Nat.Prime j then ArithmeticFunction.vonMangoldt j else 0
  change (∑ n ∈ Finset.range N, g (N - n)) =
    ∑ j ∈ Finset.range (N + 1), g j
  rw [Finset.sum_range_succ' g N]
  have hgZero : g 0 = 0 := by
    simp [g, Nat.not_prime_zero, ArithmeticFunction.vonMangoldt_apply,
      not_isPrimePow_zero]
  rw [hgZero, add_zero]
  rw [← Finset.sum_range_reflect (fun j => g (j + 1)) N]
  have hReflect :
      (∑ n ∈ Finset.range N, g (N - n)) =
      ∑ n ∈ Finset.range N, g (N - 1 - n + 1) := by
    apply Finset.sum_congr rfl
    intro n hn
    have hnlt : n < N := Finset.mem_range.mp hn
    have hIndex : N - 1 - n + 1 = N - n := by omega
    rw [hIndex]
  rw [hReflect]

/-- A von Mangoldt value inside `[0,N]` is bounded by `log N`. -/
theorem vonMangoldt_le_log_nat_of_le
    {n N : Nat} (hn : n ≤ N) :
    ArithmeticFunction.vonMangoldt n ≤ Real.log (N : Real) := by
  by_cases hnZero : n = 0
  · subst n
    simpa using Real.log_natCast_nonneg N
  · calc
      ArithmeticFunction.vonMangoldt n ≤ Real.log (n : Real) :=
        ArithmeticFunction.vonMangoldt_le_log
      _ ≤ Real.log (N : Real) := by
        have hnPos : (0 : Real) < n := by
          exact_mod_cast Nat.pos_of_ne_zero hnZero
        have hNPos : (0 : Real) < N := by
          exact_mod_cast (Nat.pos_of_ne_zero hnZero).trans_le hn
        exact (Real.log_le_log_iff hnPos hNPos).2 (by exact_mod_cast hn)

/-- Pointwise union bound: a non-pure convolution term is charged to at
least one non-prime von Mangoldt coordinate. -/
theorem defectTerm_le_split_nonPrime_charge
    {N n : Nat} (hn : n < N)
    (hNotPure : ¬ (Nat.Prime n ∧ Nat.Prime (N - n))) :
    ArithmeticFunction.vonMangoldt n *
        ArithmeticFunction.vonMangoldt (N - n) ≤
      Real.log (N : Real) *
          (if ¬ Nat.Prime n then ArithmeticFunction.vonMangoldt n else 0) +
        Real.log (N : Real) *
          (if ¬ Nat.Prime (N - n) then
            ArithmeticFunction.vonMangoldt (N - n) else 0) := by
  have hnLe : n ≤ N := Nat.le_of_lt hn
  have hRightLe : N - n ≤ N := Nat.sub_le N n
  have hLogNonneg : 0 ≤ Real.log (N : Real) :=
    Real.log_natCast_nonneg N
  by_cases hnPrime : Nat.Prime n
  · have hRightNotPrime : ¬ Nat.Prime (N - n) := by
      intro hRightPrime
      exact hNotPure ⟨hnPrime, hRightPrime⟩
    simp only [hnPrime, not_true_eq_false, ite_false,
      hRightNotPrime, not_false_eq_true, ite_true, mul_zero, zero_add]
    exact mul_le_mul_of_nonneg_right
      (vonMangoldt_le_log_nat_of_le hnLe)
      ArithmeticFunction.vonMangoldt_nonneg
  · simp only [hnPrime, not_false_eq_true, ite_true]
    have hBase :
        ArithmeticFunction.vonMangoldt n *
            ArithmeticFunction.vonMangoldt (N - n) ≤
          Real.log (N : Real) * ArithmeticFunction.vonMangoldt n := by
      have h := mul_le_mul_of_nonneg_left
        (vonMangoldt_le_log_nat_of_le hRightLe)
        (ArithmeticFunction.vonMangoldt_nonneg (n := n))
      simpa [mul_comm] using h
    have hExtra :
        0 ≤ Real.log (N : Real) *
          (if ¬ Nat.Prime (N - n) then
            ArithmeticFunction.vonMangoldt (N - n) else 0) := by
      apply mul_nonneg hLogNonneg
      by_cases hRightPrime : Nat.Prime (N - n)
      · simp [hRightPrime]
      · simp [hRightPrime,
          ArithmeticFunction.vonMangoldt_nonneg (n := N - n)]
    exact hBase.trans (le_add_of_nonneg_right hExtra)

/-- The total defect is bounded by the sum of the two one-sided non-prime
charges. -/
theorem primePowerDefect_le_log_mul_oneSidedMasses (N : Nat) :
    primePowerDefect N ≤
      Real.log (N : Real) * leftNonPrimeMass N +
        Real.log (N : Real) * rightNonPrimeMass N := by
  classical
  rw [primePowerDefect, leftNonPrimeMass, rightNonPrimeMass]
  simp_rw [Finset.sum_filter]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro n hn
  have hnLt : n < N := Finset.mem_range.mp hn
  by_cases hNotPure : ¬ (Nat.Prime n ∧ Nat.Prime (N - n))
  · simp only [hNotPure, not_false_eq_true, ite_true]
    exact defectTerm_le_split_nonPrime_charge hnLt hNotPure
  · simp only [hNotPure, ite_false]
    push Not at hNotPure
    rcases hNotPure with ⟨hnPrime, hRightPrime⟩
    simp [hnPrime, hRightPrime]

/-- The exact defect is at most twice `log N` times the Chebyshev
prime-power mass. -/
theorem primePowerDefect_le_two_log_mul_psi_sub_theta (N : Nat) :
    primePowerDefect N ≤
      2 * Real.log (N : Real) *
        (Chebyshev.psi N - Chebyshev.theta N) := by
  have hLogNonneg : 0 ≤ Real.log (N : Real) :=
    Real.log_natCast_nonneg N
  have hLeft := mul_le_mul_of_nonneg_left
    (leftNonPrimeMass_le_total N) hLogNonneg
  calc
    primePowerDefect N ≤
        Real.log (N : Real) * leftNonPrimeMass N +
          Real.log (N : Real) * rightNonPrimeMass N :=
      primePowerDefect_le_log_mul_oneSidedMasses N
    _ ≤ Real.log (N : Real) * nonPrimeVonMangoldtMass N +
          Real.log (N : Real) * nonPrimeVonMangoldtMass N := by
      rw [rightNonPrimeMass_eq_total]
      exact add_le_add hLeft le_rfl
    _ = 2 * Real.log (N : Real) *
          (Chebyshev.psi N - Chebyshev.theta N) := by
      rw [nonPrimeVonMangoldtMass_eq_psi_sub_theta]
      ring

/-- Explicit constructive defect bound obtained from Mathlib's Chebyshev
estimate. This is a defect bound only; it supplies no main-term lower bound. -/
theorem primePowerDefect_le_four_sqrt_mul_log_sq
    {N : Nat} (hN : 1 ≤ N) :
    primePowerDefect N ≤
      4 * Real.sqrt (N : Real) * (Real.log (N : Real)) ^ 2 := by
  have hLogNonneg : 0 ≤ Real.log (N : Real) :=
    Real.log_natCast_nonneg N
  have hChebyshev :
      Chebyshev.psi (N : Real) - Chebyshev.theta (N : Real) ≤
        2 * Real.sqrt (N : Real) * Real.log (N : Real) :=
    Chebyshev.psi_sub_theta_le (by exact_mod_cast hN)
  have hScaled := mul_le_mul_of_nonneg_left hChebyshev
    (mul_nonneg (by norm_num : (0 : Real) ≤ 2) hLogNonneg)
  calc
    primePowerDefect N ≤
        2 * Real.log (N : Real) *
          (Chebyshev.psi N - Chebyshev.theta N) :=
      primePowerDefect_le_two_log_mul_psi_sub_theta N
    _ ≤ 2 * Real.log (N : Real) *
          (2 * Real.sqrt (N : Real) * Real.log (N : Real)) := hScaled
    _ = 4 * Real.sqrt (N : Real) * (Real.log (N : Real)) ^ 2 := by
      ring

end GoldbachPrimePowerDefectBoundV161
