import GoldbachCircleMethodSquarefreeCoefficientBindingV1839
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
import Mathlib.NumberTheory.ArithmeticFunction.Moebius

/-!
# V1.8.40: finite Fourier Ramanujan coprime binding

This module defines the genuine finite additive-character sum over the unit carrier of
`ZMod q`.  It proves the complete boundary case `q = 1` and the prime-modulus case.
It does not claim the composite-modulus Möbius identity.
-/

open scoped BigOperators

namespace GoldbachCircleMethodRamanujanCoprimeBindingV1840

/-- The finite Fourier Ramanujan sum, expressed on the exact coprime/unit carrier. -/
noncomputable def finiteFourierRamanujan (q N : ℕ) (hq : q ≠ 0) : ℂ := by
  letI : NeZero q := ⟨hq⟩
  classical
  exact ∑ a : ZMod q, if IsUnit a then ZMod.stdAddChar (a * (N : ZMod q)) else 0

/-- The genuine Fourier sum has the correct boundary value at modulus one. -/
theorem finiteFourierRamanujan_one (N : ℕ) :
    finiteFourierRamanujan 1 N one_ne_zero =
      ((ArithmeticFunction.moebius 1 : ℤ) : ℂ) := by
  classical
  simp only [finiteFourierRamanujan]
  have hu (a : ZMod 1) : IsUnit a := by
    rw [Subsingleton.elim a 1]
    exact isUnit_one
  simp_rw [hu]
  rw [Fintype.sum_unique]
  simp only [if_true]
  have harg : (default : ZMod 1) * (N : ZMod 1) = 0 := Subsingleton.elim _ _
  calc
    ZMod.stdAddChar ((default : ZMod 1) * (N : ZMod 1)) =
        ZMod.stdAddChar (0 : ZMod 1) := congrArg ZMod.stdAddChar harg
    _ = ((ArithmeticFunction.moebius 1 : ℤ) : ℂ) := by simp

set_option linter.style.haveILetI false
/-- At a prime modulus, the coprime Fourier sum is `-1`, uniformly in coprime `N`. -/
theorem finiteFourierRamanujan_eq_neg_one_of_prime
    {q N : ℕ} (hq : q.Prime) (hN : Nat.Coprime N q) :
    finiteFourierRamanujan q N hq.ne_zero = -1 := by
  letI : Fact q.Prime := ⟨hq⟩
  letI : NeZero q := ⟨hq.ne_zero⟩
  have hNunit : IsUnit (N : ZMod q) := (ZMod.isUnit_iff_coprime N q).mpr hN
  have hNzero : (N : ZMod q) ≠ 0 := isUnit_iff_ne_zero.mp hNunit
  have hsum : (∑ a : ZMod q, ZMod.stdAddChar (a * (N : ZMod q))) = 0 := by
    simpa [hNzero] using
      (AddChar.sum_mulShift (R := ZMod q) (R' := ℂ) (N : ZMod q)
        (ZMod.isPrimitive_stdAddChar q))
  rw [finiteFourierRamanujan]
  simp_rw [isUnit_iff_ne_zero]
  rw [← Finset.sum_filter, Finset.filter_ne']
  have hsplit :
      (∑ a ∈ (Finset.univ.erase 0 : Finset (ZMod q)),
          ZMod.stdAddChar (a * (N : ZMod q))) +
          ZMod.stdAddChar ((0 : ZMod q) * (N : ZMod q)) =
        ∑ a : ZMod q, ZMod.stdAddChar (a * (N : ZMod q)) :=
    Finset.sum_erase_add Finset.univ
      (fun a : ZMod q => ZMod.stdAddChar (a * (N : ZMod q))) (Finset.mem_univ 0)
  have herase :
      (∑ a ∈ (Finset.univ.erase 0 : Finset (ZMod q)),
          ZMod.stdAddChar (a * (N : ZMod q))) =
        0 - ZMod.stdAddChar ((0 : ZMod q) * (N : ZMod q)) := by
    exact (eq_sub_iff_add_eq).2 (hsplit.trans hsum)
  simpa using herase

/-- Prime-modulus specialization of the classical coprime Ramanujan/Möbius identity. -/
theorem finiteFourierRamanujan_eq_moebius_of_prime
    {q N : ℕ} (hq : q.Prime) (hN : Nat.Coprime N q) :
    finiteFourierRamanujan q N hq.ne_zero =
      ((ArithmeticFunction.moebius q : ℤ) : ℂ) := by
  rw [finiteFourierRamanujan_eq_neg_one_of_prime hq hN,
    ArithmeticFunction.moebius_apply_prime hq]
  norm_num

end GoldbachCircleMethodRamanujanCoprimeBindingV1840
