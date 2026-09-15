import GoldbachCircleMethodFiniteResiduePrefixV1866

/-! # V1.8.67: a deliberately coarse but proved nonreduced-prefix envelope.
Prime divisors and higher prime powers are charged separately. No SW bound.
-/
open scoped BigOperators
open GoldbachCircleMethodFiniteResiduePrefixV1866
open GoldbachPrimePowerDefectBoundV161

namespace GoldbachCircleMethodNonreducedMassEnvelopeV1867

attribute [local instance] Classical.propDecidable

noncomputable def primeDivisorPrefixMass (k q : ℕ) : ℝ :=
  ∑ n ∈ (Finset.range k.succ).filter (fun n => Nat.Prime n ∧ n ∣ q),
    ArithmeticFunction.vonMangoldt n

theorem nonreducedMass_eq_integer_sum (k q : ℕ) [NeZero q] :
    nonreducedMass k q = ∑ n ∈ Finset.range k.succ,
      if IsUnit (n : ZMod q) then 0 else ArithmeticFunction.vonMangoldt n := by
  have h := residue_reindex k q (fun r => if IsUnit r then 0 else 1)
  have hc : ((nonreducedMass k q : ℝ) : ℂ) =
      ((∑ n ∈ Finset.range k.succ,
        if IsUnit (n : ZMod q) then 0 else ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) := by
    simpa only [nonreducedMass, Complex.ofReal_sum, apply_ite, Complex.ofReal_zero,
      mul_ite, mul_zero, mul_one] using h
  exact Complex.ofReal_injective hc

theorem prime_nonunit_dvd (q n : ℕ) (hn : Nat.Prime n)
    (hu : ¬ IsUnit (n : ZMod q)) : n ∣ q := by
  by_contra hd
  exact hu ((ZMod.isUnit_prime_iff_not_dvd hn).mpr hd)

theorem nonreducedMass_le_prime_and_power (k q : ℕ) [NeZero q] :
    nonreducedMass k q ≤ primeDivisorPrefixMass k q + nonPrimeVonMangoldtMass k := by
  rw [nonreducedMass_eq_integer_sum]
  unfold primeDivisorPrefixMass nonPrimeVonMangoldtMass
  rw [show Finset.Icc 0 k = Finset.range k.succ by ext n; simp]
  simp only [Finset.sum_filter]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro n _
  by_cases hn : Nat.Prime n
  · by_cases hu : IsUnit (n : ZMod q)
    · simp only [hu, hn, if_true, true_and, not_true_eq_false, if_false, add_zero]
      split_ifs
      · exact ArithmeticFunction.vonMangoldt_nonneg
      · exact le_rfl
    · have hd := prime_nonunit_dvd q n hn hu
      simp [hu, hn, hd]
  · simp only [hn, false_and, if_false, not_false_eq_true, if_true, zero_add]
    split_ifs
    · exact ArithmeticFunction.vonMangoldt_nonneg
    · exact le_rfl

theorem primeDivisorPrefixMass_le (k q : ℕ) (hq : 0 < q) :
    primeDivisorPrefixMass k q ≤ (q+1 : ℝ)*Real.log (k : ℝ) := by
  let s := (Finset.range k.succ).filter (fun n => Nat.Prime n ∧ n ∣ q)
  have hc : s.card ≤ q+1 := by
    have hs : s ⊆ Finset.range (q+1) := by
      intro n hn
      have hd := (Finset.mem_filter.mp hn).2.2
      exact Finset.mem_range.mpr (by have := Nat.le_of_dvd hq hd; omega)
    simpa using Finset.card_le_card hs
  calc
    primeDivisorPrefixMass k q ≤ ∑ _n ∈ s, Real.log (k : ℝ) := by
      apply Finset.sum_le_sum
      intro n hn
      exact vonMangoldt_le_log_nat_of_le
        (by have := Finset.mem_range.mp (Finset.mem_filter.mp hn).1; omega)
    _ = (s.card : ℝ)*Real.log (k : ℝ) := by simp
    _ ≤ (q+1 : ℝ)*Real.log (k : ℝ) := by
      apply mul_le_mul_of_nonneg_right _ (Real.log_natCast_nonneg k)
      exact_mod_cast hc

theorem nonreducedMass_le_chebyshev_envelope (k q : ℕ) [NeZero q] (hk : 1 ≤ k) :
    nonreducedMass k q ≤ ((q+1 : ℝ)+2*Real.sqrt (k : ℝ))*Real.log (k : ℝ) := by
  have hpp : nonPrimeVonMangoldtMass k ≤ 2*Real.sqrt (k : ℝ)*Real.log (k : ℝ) := by
    rw [nonPrimeVonMangoldtMass_eq_psi_sub_theta]
    exact Chebyshev.psi_sub_theta_le (by exact_mod_cast hk)
  calc
    _ ≤ primeDivisorPrefixMass k q + nonPrimeVonMangoldtMass k :=
      nonreducedMass_le_prime_and_power k q
    _ ≤ (q+1 : ℝ)*Real.log (k : ℝ)+2*Real.sqrt (k : ℝ)*Real.log (k : ℝ) :=
      add_le_add (primeDivisorPrefixMass_le k q (Nat.pos_of_ne_zero (NeZero.ne q))) hpp
    _ = _ := by ring

theorem nonreducedMass_zero (q : ℕ) [NeZero q] : nonreducedMass 0 q = 0 := by
  rw [nonreducedMass_eq_integer_sum]
  simp

theorem nonreducedMass_le_uniform_envelope (M k q : ℕ) [NeZero q]
    (hkM : k ≤ M) :
    nonreducedMass k q ≤ ((q+1 : ℝ)+2*Real.sqrt (M : ℝ))*Real.log (M : ℝ) := by
  by_cases hk0 : k = 0
  · subst k
    rw [nonreducedMass_zero]
    positivity
  have hk : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk0
  have hlog : Real.log (k : ℝ) ≤ Real.log (M : ℝ) := by
    apply Real.log_le_log (by exact_mod_cast hk) (by exact_mod_cast hkM)
  have hsqrt : Real.sqrt (k : ℝ) ≤ Real.sqrt (M : ℝ) :=
    Real.sqrt_le_sqrt (by exact_mod_cast hkM)
  exact (nonreducedMass_le_chebyshev_envelope k q hk).trans
    (mul_le_mul (by linarith) hlog (Real.log_natCast_nonneg k) (by positivity))

end GoldbachCircleMethodNonreducedMassEnvelopeV1867
