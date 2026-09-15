import GoldbachCircleMethodPrincipalWindowBoundaryV18121
import Mathlib.Data.Nat.Log

set_option autoImplicit false
open scoped BigOperators Classical
open GoldbachCircleMethodLogCutoffPresieveBindingV18120

namespace GoldbachCircleMethodRemovedPrimePowerMassV18122

def smallPrimes (Q : ℕ) : Finset ℕ :=
  (Finset.Icc 1 Q).filter Nat.Prime

noncomputable def primePowerEnvelope (Q B n : ℕ) : ℝ :=
  ∑ p ∈ smallPrimes Q, ∑ k ∈ Finset.Icc 1 (Nat.log p B),
    if p^k = n then Real.log (p : ℝ) else 0

theorem log_smallPrime_nonneg (Q p : ℕ) (hp : p ∈ smallPrimes Q) :
    0 ≤ Real.log (p : ℝ) := by
  apply Real.log_nonneg
  exact_mod_cast (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1

theorem prime_power_envelope_nonneg (Q B n : ℕ) :
    0 ≤ primePowerEnvelope Q B n := by
  apply Finset.sum_nonneg
  intro p hp
  apply Finset.sum_nonneg
  intro k _
  split_ifs
  · exact log_smallPrime_nonneg Q p hp
  · exact le_rfl

/-- The complex norm is the actual nonnegative von Mangoldt value. -/
theorem removed_norm_of_nonzero (Q B n : ℕ) (hg : removedInput Q B n ≠ 0) :
    ‖removedInput Q B n‖ = ArithmeticFunction.vonMangoldt n := by
  have hn := (removed_input_prime_power_support Q B n hg).1
  have hr : ¬Rough Q n := by
    intro h
    exact hg (by simp only [removedInput, h, if_true])
  simp only [removedInput, hr, if_false, blockInput, hn, if_true,
    Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]

/-- A finite positive envelope over genuine small prime bases and bounded exponents. -/
theorem removed_norm_le_envelope (Q B n : ℕ) :
    ‖removedInput Q B n‖ ≤ primePowerEnvelope Q B n := by
  by_cases hg : removedInput Q B n = 0
  · rw [hg, norm_zero]
    exact prime_power_envelope_nonneg Q B n
  · obtain ⟨hn, p, k, hp, hpQ, hk, hpow⟩ :=
      removed_input_prime_power_support Q B n hg
    have hnB : n ≤ B := (mem_blockCarrier B n).mp hn |>.2
    have hpP : p ∈ smallPrimes Q :=
      Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hp.one_lt.le, hpQ⟩, hp⟩
    have hkK : k ∈ Finset.Icc 1 (Nat.log p B) :=
      Finset.mem_Icc.mpr ⟨hk, Nat.le_log_of_pow_le hp.one_lt (hpow ▸ hnB)⟩
    rw [removed_norm_of_nonzero Q B n hg, ← hpow,
      ArithmeticFunction.vonMangoldt_apply_pow (Nat.ne_of_gt hk),
      ArithmeticFunction.vonMangoldt_apply_prime hp]
    calc
      Real.log (p : ℝ) =
          (if p^k = p^k then Real.log (p : ℝ) else 0) := by rw [if_pos rfl]
      _ ≤ ∑ j ∈ Finset.Icc 1 (Nat.log p B),
          if p^j = p^k then Real.log (p : ℝ) else 0 := by
        apply Finset.single_le_sum (a := k)
          (f := fun j => if p^j = p^k then Real.log (p : ℝ) else 0)
        · intro j _
          split_ifs
          · exact log_smallPrime_nonneg Q p hpP
          · exact le_rfl
        · exact hkK
      _ ≤ primePowerEnvelope Q B (p^k) := by
        unfold primePowerEnvelope
        apply Finset.single_le_sum (a := p)
          (f := fun s => ∑ j ∈ Finset.Icc 1 (Nat.log s B),
            if s^j = p^k then Real.log (s : ℝ) else 0)
        · intro s hs
          apply Finset.sum_nonneg
          intro j _
          split_ifs
          · exact log_smallPrime_nonneg Q s hs
          · exact le_rfl
        · exact hpP

/-- Summing the finite envelope over a block cannot exceed all its exponent weights. -/
theorem envelope_mass_le_exponent_mass (Q B : ℕ) :
    (∑ n ∈ blockCarrier B, primePowerEnvelope Q B n) ≤
      ∑ p ∈ smallPrimes Q, ∑ _k ∈ Finset.Icc 1 (Nat.log p B),
        Real.log (p : ℝ) := by
  unfold primePowerEnvelope
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro p hp
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro k _
  by_cases hn : p^k ∈ blockCarrier B
  · rw [Finset.sum_eq_single (p^k)]
    · simp only [if_true, le_refl]
    · intro n _ hne
      simp only [Ne.symm hne, if_false]
    · exact fun h => False.elim (h hn)
  · have hz : (∑ n ∈ blockCarrier B,
        if p^k = n then Real.log (p : ℝ) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro n hn'
      have hne : p^k ≠ n := by
        intro h
        exact hn (h ▸ hn')
      simp only [hne, if_false]
    rw [hz]
    exact log_smallPrime_nonneg Q p hp

/-- Explicit basewise budget, including the empty exponent range when p>B. -/
theorem base_exponent_mass_le_log (p B : ℕ) (hp : p.Prime) (hB : 0 < B) :
    (∑ _k ∈ Finset.Icc 1 (Nat.log p B), Real.log (p : ℝ)) ≤ Real.log (B : ℝ) := by
  have hpow : p^(Nat.log p B) ≤ B :=
    Nat.pow_log_le_self p (Nat.ne_of_gt hB)
  have hlog := Real.log_le_log
    (Nat.cast_pos.mpr (pow_pos hp.pos (Nat.log p B)))
    (show ((p^(Nat.log p B) : ℕ) : ℝ) ≤ (B : ℝ) by exact_mod_cast hpow)
  simpa only [Finset.sum_const, nsmul_eq_mul, Nat.card_Icc,
    Nat.add_sub_cancel, Nat.cast_pow, Real.log_pow] using hlog

theorem small_primes_card_le (Q : ℕ) : (smallPrimes Q).card ≤ Q := by
  have h := Finset.card_filter_le (Finset.Icc 1 Q) Nat.Prime
  simpa only [smallPrimes, Nat.card_Icc, Nat.add_sub_cancel] using h

/-- Quantitative bound for the ACTUAL removed input, with explicit constant one. -/
theorem removed_mass_le_Q_log_B (Q B : ℕ) (hB : 2 ≤ B) :
    (∑ n ∈ blockCarrier B, ‖removedInput Q B n‖) ≤
      (Q : ℝ) * Real.log (B : ℝ) := by
  have hlogB : 0 ≤ Real.log (B : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (le_trans (by decide : 1 ≤ 2) hB))
  calc
    _ ≤ ∑ n ∈ blockCarrier B, primePowerEnvelope Q B n :=
      Finset.sum_le_sum (fun n _ => removed_norm_le_envelope Q B n)
    _ ≤ ∑ p ∈ smallPrimes Q, ∑ k ∈ Finset.Icc 1 (Nat.log p B),
        Real.log (p : ℝ) := envelope_mass_le_exponent_mass Q B
    _ ≤ ∑ _p ∈ smallPrimes Q, Real.log (B : ℝ) := by
      apply Finset.sum_le_sum
      intro p hp
      exact base_exponent_mass_le_log p B (Finset.mem_filter.mp hp).2
        (lt_of_lt_of_le (by decide : 0 < 2) hB)
    _ = ((smallPrimes Q).card : ℝ) * Real.log (B : ℝ) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (Q : ℝ) * Real.log (B : ℝ) :=
      mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (small_primes_card_le Q)) hlogB

/-- The intended real cutoff retains the same explicit bound. -/
theorem removed_mass_le_R_sq_log_B (R : ℝ) (B : ℕ) (hB : 2 ≤ B) :
    (∑ n ∈ blockCarrier B, ‖removedInput ⌊R^2⌋₊ B n‖) ≤
      R^2 * Real.log (B : ℝ) := by
  exact (removed_mass_le_Q_log_B ⌊R^2⌋₊ B hB).trans
    (mul_le_mul_of_nonneg_right (Nat.floor_le (sq_nonneg R))
      (Real.log_nonneg (by exact_mod_cast (le_trans (by decide : 1 ≤ 2) hB))))

end GoldbachCircleMethodRemovedPrimePowerMassV18122
