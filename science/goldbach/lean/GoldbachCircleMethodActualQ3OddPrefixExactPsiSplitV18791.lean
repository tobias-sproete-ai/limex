import GoldbachCircleMethodActualQ3ThreePowerDebitFinalGateV18790
import Mathlib.Data.Nat.Log

/-!
# V1.8.791: exact Chebyshev split of the remaining odd prefix

The only arithmetic channel left by V1.8.790 contains the incomplete total
odd von-Mangoldt mass.  This module removes its last finite-support ambiguity.
At the effective endpoint `U = min M (B - 1)`, the odd mass is exactly
Mathlib's Chebyshev `psi U` minus the contribution of the positive powers of
two.  That contribution is exactly `log_2 U` copies of `log 2`.

This is an identity, not a prime-number-theorem estimate.  No bound for
`psi U - U`, no signed correlation estimate, and no Goldbach conclusion is
claimed.  `proof_status = NO_PROOF`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

open scoped BigOperators Classical ArithmeticFunction.vonMangoldt

namespace GoldbachCircleMethodActualQ3OddPrefixExactPsiSplitV18791

open GoldbachCircleMethodOddOddFourierBesselBridgeV18668
open GoldbachCircleMethodActualOddLambdaQ3ResidueDiscrepancyV18752
open GoldbachCircleMethodActualLambdaPairSourceMeanChebyshevBoundV18719

/-- Effective integer endpoint of the incomplete prefix. -/
def actualQ3PrefixCutoff (M B : Nat) : Nat :=
  min M (B - 1)

/-- Odd and even pieces of the full von-Mangoldt prefix at an endpoint. -/
noncomputable def boundedOddLambdaMass (U : Nat) : Real :=
  ∑ a ∈ (Finset.range U.succ).filter Odd,
    ArithmeticFunction.vonMangoldt a

noncomputable def boundedEvenLambdaMass (U : Nat) : Real :=
  ∑ a ∈ (Finset.range U.succ).filter Even,
    ArithmeticFunction.vonMangoldt a

/-- Literal support of the nonzero even von-Mangoldt summands. -/
def boundedEvenLambdaSupport (U : Nat) : Finset Nat :=
  (Finset.range U.succ).filter fun a => Even a ∧ IsPrimePow a

/-- Exact positive exponent interval for the powers of two below `U`. -/
def boundedEvenLambdaExponentCarrier (U : Nat) : Finset Nat :=
  Finset.Icc 1 (Nat.log 2 U)

/-- The project prefix is exactly the odd part of the full prefix at its
effective endpoint. -/
theorem oddLambdaPrefixMass_eq_boundedOddLambdaMass (M B : Nat) :
    oddLambdaPrefixMass M B =
      (boundedOddLambdaMass (actualQ3PrefixCutoff M B) : Complex) := by
  unfold oddLambdaPrefixMass boundedOddLambdaMass actualQ3PrefixCutoff
  rw [← Finset.sum_filter]
  rw [Complex.ofReal_sum]
  apply Finset.sum_congr
  · ext a
    simp only [Finset.mem_filter, Finset.mem_range, oddCarrier]
    constructor
    · rintro ⟨⟨haM, haOdd⟩, haB⟩
      exact ⟨by omega, haOdd⟩
    · rintro ⟨haMin, haOdd⟩
      have haPos : 0 < a := haOdd.pos
      exact ⟨⟨by omega, haOdd⟩, by omega⟩
  · intro a _ha
    rfl

/-- Exact parity partition of the full finite von-Mangoldt mass. -/
theorem lambdaSum_eq_boundedOdd_add_even (U : Nat) :
    (∑ a ∈ Finset.range U.succ, ArithmeticFunction.vonMangoldt a) =
      boundedOddLambdaMass U + boundedEvenLambdaMass U := by
  unfold boundedOddLambdaMass boundedEvenLambdaMass
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _ha
  by_cases hOdd : Odd a
  · have hNotEven : ¬ Even a := (Nat.not_even_iff_odd.mpr hOdd)
    simp [hOdd, hNotEven]
  · have hEven : Even a := Nat.not_odd_iff_even.mp hOdd
    simp [hOdd, hEven]

/-- A nonzero even von-Mangoldt summand is exactly a positive power of two,
with weight `log 2`. -/
theorem vonMangoldt_eq_log_two_of_even
    {a : Nat}
    (hEven : Even a)
    (hLam : ArithmeticFunction.vonMangoldt a ≠ 0) :
    ∃ k : Nat, 0 < k ∧ a = 2 ^ k ∧
      ArithmeticFunction.vonMangoldt a = Real.log 2 := by
  have hpp : IsPrimePow a :=
    ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hLam
  obtain ⟨p, k, hp, hk, hpk⟩ := (isPrimePow_nat_iff a).mp hpp
  have h2dvdA : 2 ∣ a := even_iff_two_dvd.mp hEven
  have h2dvdPpow : 2 ∣ p ^ k := by simpa [hpk] using h2dvdA
  have h2prime : Nat.Prime 2 := by norm_num
  have h2dvdP : 2 ∣ p := h2prime.dvd_of_dvd_pow h2dvdPpow
  have hp2 : 2 = p :=
    (Nat.prime_dvd_prime_iff_eq h2prime hp).mp h2dvdP
  subst p
  refine ⟨k, hk, hpk.symm, ?_⟩
  rw [← hpk, ArithmeticFunction.vonMangoldt_apply_pow hk.ne',
    ArithmeticFunction.vonMangoldt_apply_prime h2prime]
  norm_num

/-- Exact support description by powers of two. -/
theorem mem_boundedEvenLambdaSupport_iff_exists_exponent
    {U a : Nat} :
    a ∈ boundedEvenLambdaSupport U ↔
      ∃ k ∈ boundedEvenLambdaExponentCarrier U, a = 2 ^ k := by
  constructor
  · intro ha
    rw [boundedEvenLambdaSupport, Finset.mem_filter] at ha
    rcases ha with ⟨haU, haEven, haPP⟩
    have hLam : ArithmeticFunction.vonMangoldt a ≠ 0 :=
      ArithmeticFunction.vonMangoldt_ne_zero_iff.mpr haPP
    obtain ⟨k, hk, hak, _hweight⟩ :=
      vonMangoldt_eq_log_two_of_even haEven hLam
    have haLe : a ≤ U := Finset.mem_range_succ_iff.mp haU
    have hkLog : k ≤ Nat.log 2 U := by
      apply Nat.le_log_of_pow_le (by norm_num)
      simpa [← hak] using haLe
    refine ⟨k, ?_, hak⟩
    rw [boundedEvenLambdaExponentCarrier, Finset.mem_Icc]
    exact ⟨by omega, hkLog⟩
  · rintro ⟨k, hkCarrier, rfl⟩
    rw [boundedEvenLambdaExponentCarrier, Finset.mem_Icc] at hkCarrier
    rcases hkCarrier with ⟨hkPos, hkLog⟩
    have hUNe : U ≠ 0 := by
      intro hzero
      rw [hzero] at hkLog
      simp at hkLog
      omega
    have hpow : 2 ^ k ≤ U := Nat.pow_le_of_le_log hUNe hkLog
    have hkNe : k ≠ 0 := by omega
    have hEven : Even (2 ^ k) := by
      exact even_iff_two_dvd.mpr (dvd_pow_self 2 hkNe)
    have hPP : IsPrimePow (2 ^ k) := by
      exact (show Nat.Prime 2 by norm_num).isPrimePow.pow hkNe
    rw [boundedEvenLambdaSupport, Finset.mem_filter]
    exact ⟨Finset.mem_range_succ_iff.mpr hpow, hEven, hPP⟩

theorem boundedEvenLambdaSupport_eq_image_exponents (U : Nat) :
    boundedEvenLambdaSupport U =
      (boundedEvenLambdaExponentCarrier U).image (fun k => 2 ^ k) := by
  ext a
  rw [mem_boundedEvenLambdaSupport_iff_exists_exponent]
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k, hk, rfl⟩
  · rintro ⟨k, hk, hka⟩
    exact ⟨k, hk, hka.symm⟩

theorem card_boundedEvenLambdaSupport (U : Nat) :
    (boundedEvenLambdaSupport U).card = Nat.log 2 U := by
  rw [boundedEvenLambdaSupport_eq_image_exponents]
  rw [Finset.card_image_of_injective _
    (Nat.pow_right_injective (by norm_num : 2 ≤ 2))]
  unfold boundedEvenLambdaExponentCarrier
  rw [Nat.card_Icc]
  omega

/-- Restriction to the actual nonzero even support. -/
theorem boundedEvenLambdaMass_eq_support_sum (U : Nat) :
    boundedEvenLambdaMass U =
      ∑ a ∈ boundedEvenLambdaSupport U,
        ArithmeticFunction.vonMangoldt a := by
  unfold boundedEvenLambdaMass boundedEvenLambdaSupport
  rw [Finset.sum_filter, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro a _ha
  by_cases hEven : Even a
  · rw [if_pos hEven]
    by_cases hPP : IsPrimePow a
    · rw [if_pos ⟨hEven, hPP⟩]
    · rw [if_neg (by tauto)]
      rw [ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hPP]
  · rw [if_neg hEven]
    rw [if_neg (by tauto)]

theorem boundedEvenLambdaMass_eq_log_count (U : Nat) :
    boundedEvenLambdaMass U = Nat.log 2 U * Real.log 2 := by
  rw [boundedEvenLambdaMass_eq_support_sum]
  calc
    (∑ a ∈ boundedEvenLambdaSupport U,
        ArithmeticFunction.vonMangoldt a) =
      ∑ _a ∈ boundedEvenLambdaSupport U, Real.log 2 := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [boundedEvenLambdaSupport, Finset.mem_filter] at ha
        rcases ha with ⟨_haU, haEven, haPP⟩
        exact vonMangoldt_eq_log_two_of_even haEven
          (ArithmeticFunction.vonMangoldt_ne_zero_iff.mpr haPP) |>.choose_spec.2.2
    _ = (boundedEvenLambdaSupport U).card * Real.log 2 := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ = Nat.log 2 U * Real.log 2 := by
      rw [card_boundedEvenLambdaSupport]

/-- Exact final arithmetic identity for the remaining prefix mass. -/
theorem boundedOddLambdaMass_eq_psi_sub_twoPowers (U : Nat) :
    boundedOddLambdaMass U =
      Chebyshev.psi (U : Real) - Nat.log 2 U * Real.log 2 := by
  have hFull := lambdaSum_range_succ_eq_psi U
  have hSplit := lambdaSum_eq_boundedOdd_add_even U
  rw [boundedEvenLambdaMass_eq_log_count] at hSplit
  linarith

theorem oddLambdaPrefixMass_eq_psi_sub_twoPowers (M B : Nat) :
    oddLambdaPrefixMass M B =
      ((Chebyshev.psi (actualQ3PrefixCutoff M B : Real) -
          Nat.log 2 (actualQ3PrefixCutoff M B) * Real.log 2 : Real) : Complex) := by
  rw [oddLambdaPrefixMass_eq_boundedOddLambdaMass,
    boundedOddLambdaMass_eq_psi_sub_twoPowers]

end GoldbachCircleMethodActualQ3OddPrefixExactPsiSplitV18791
