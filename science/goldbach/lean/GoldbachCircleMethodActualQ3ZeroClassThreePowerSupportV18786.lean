import GoldbachCircleMethodActualQ3LocalDensityThreeClassSplitV18785
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Log

/-!
# V1.8.786: exact three-power support of the q=3 zero class

The zero residue class isolated in V1.8.785 is not an uncontrolled prime
progression.  A nonzero von-Mangoldt summand divisible by three is exactly a
positive power of three, and every such summand has weight `log 3`.

This module proves that support statement and identifies the literal finite
support with a finite interval of exponents.  It introduces no asymptotic
estimate and no Goldbach conclusion.  `proof_status = NO_PROOF`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

open scoped BigOperators Classical ArithmeticFunction.vonMangoldt

namespace GoldbachCircleMethodActualQ3ZeroClassThreePowerSupportV18786

open GoldbachCircleMethodOddOddFourierBesselBridgeV18668
open GoldbachCircleMethodActualOddLambdaQ3ResidueDiscrepancyV18752

/-- The literal support contributing to the zero residue class. -/
def oddLambdaQ3ZeroSupport (M B : Nat) : Finset Nat :=
  (oddCarrier M).filter fun a =>
    a < B ∧ (a : ZMod 3) = 0 ∧ IsPrimePow a

/-- The exact exponent interval compatible with both carrier cutoffs. -/
def oddLambdaQ3ZeroExponentCarrier (M B : Nat) : Finset Nat :=
  Finset.Icc 1 (Nat.log 3 (min M (B - 1)))

/-- A nonzero von-Mangoldt value in the zero residue class modulo three is
exactly the logarithm of three at a positive power of three. -/
theorem vonMangoldt_eq_log_three_of_q3_zero
    {a : Nat}
    (hmod : (a : ZMod 3) = 0)
    (hLam : ArithmeticFunction.vonMangoldt a ≠ 0) :
    ∃ k : Nat, 0 < k ∧ a = 3 ^ k ∧
      ArithmeticFunction.vonMangoldt a = Real.log 3 := by
  have hpp : IsPrimePow a :=
    ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hLam
  obtain ⟨p, k, hp, hk, hpk⟩ := (isPrimePow_nat_iff a).mp hpp
  have h3dvdA : 3 ∣ a := (ZMod.natCast_eq_zero_iff a 3).mp hmod
  have h3dvdPpow : 3 ∣ p ^ k := by simpa [hpk] using h3dvdA
  have h3prime : Nat.Prime 3 := by norm_num
  have h3dvdP : 3 ∣ p := h3prime.dvd_of_dvd_pow h3dvdPpow
  have hp3 : 3 = p :=
    (Nat.prime_dvd_prime_iff_eq h3prime hp).mp h3dvdP
  subst p
  refine ⟨k, hk, hpk.symm, ?_⟩
  rw [← hpk, ArithmeticFunction.vonMangoldt_apply_pow hk.ne',
    ArithmeticFunction.vonMangoldt_apply_prime h3prime]
  norm_num

/-- Every element of the literal zero support has a unique exponent in the
declared finite exponent carrier. -/
theorem mem_zeroSupport_iff_exists_exponent
    {M B a : Nat} :
    a ∈ oddLambdaQ3ZeroSupport M B ↔
      ∃ k ∈ oddLambdaQ3ZeroExponentCarrier M B, a = 3 ^ k := by
  constructor
  · intro ha
    rw [oddLambdaQ3ZeroSupport, Finset.mem_filter] at ha
    rcases ha with ⟨haOdd, haB, haMod, haPP⟩
    have hLam : ArithmeticFunction.vonMangoldt a ≠ 0 :=
      ArithmeticFunction.vonMangoldt_ne_zero_iff.mpr haPP
    obtain ⟨k, hk, hak, _hweight⟩ :=
      vonMangoldt_eq_log_three_of_q3_zero haMod hLam
    have haM : a ≤ M := by
      exact Finset.mem_range_succ_iff.mp (Finset.mem_filter.mp haOdd).1
    have haBpred : a ≤ B - 1 := by omega
    have hpowMin : 3 ^ k ≤ min M (B - 1) := by
      rw [← hak]
      exact le_min haM haBpred
    have hkLog : k ≤ Nat.log 3 (min M (B - 1)) :=
      Nat.le_log_of_pow_le (by norm_num) hpowMin
    refine ⟨k, ?_, hak⟩
    rw [oddLambdaQ3ZeroExponentCarrier, Finset.mem_Icc]
    exact ⟨by omega, hkLog⟩
  · rintro ⟨k, hkCarrier, rfl⟩
    rw [oddLambdaQ3ZeroExponentCarrier, Finset.mem_Icc] at hkCarrier
    rcases hkCarrier with ⟨hkPos, hkLog⟩
    have hMinNe : min M (B - 1) ≠ 0 := by
      intro hzero
      rw [hzero] at hkLog
      simp at hkLog
      omega
    have hpow : 3 ^ k ≤ min M (B - 1) :=
      Nat.pow_le_of_le_log hMinNe hkLog
    have hpowM : 3 ^ k ≤ M := hpow.trans (min_le_left _ _)
    have hpowBpred : 3 ^ k ≤ B - 1 := hpow.trans (min_le_right _ _)
    have hpowB : 3 ^ k < B := by omega
    have hkNe : k ≠ 0 := by omega
    have hOdd : Odd (3 ^ k) := by exact Odd.pow ⟨1, by norm_num⟩
    have hCarrier : 3 ^ k ∈ oddCarrier M := by
      rw [oddCarrier, Finset.mem_filter]
      exact ⟨Finset.mem_range_succ_iff.mpr hpowM, hOdd⟩
    have hmod : ((3 ^ k : Nat) : ZMod 3) = 0 := by
      exact (ZMod.natCast_eq_zero_iff (3 ^ k) 3).mpr
        (dvd_pow_self 3 hkNe)
    have hPP : IsPrimePow (3 ^ k) := by
      exact (show Nat.Prime 3 by norm_num).isPrimePow.pow hkNe
    rw [oddLambdaQ3ZeroSupport, Finset.mem_filter]
    exact ⟨hCarrier, hpowB, hmod, hPP⟩

/-- The literal zero support is precisely the image of the finite positive
exponent interval under `k ↦ 3^k`. -/
theorem zeroSupport_eq_image_exponents (M B : Nat) :
    oddLambdaQ3ZeroSupport M B =
      (oddLambdaQ3ZeroExponentCarrier M B).image (fun k => 3 ^ k) := by
  ext a
  rw [mem_zeroSupport_iff_exists_exponent]
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k, hk, rfl⟩
  · rintro ⟨k, hk, hka⟩
    exact ⟨k, hk, hka.symm⟩

end GoldbachCircleMethodActualQ3ZeroClassThreePowerSupportV18786
