import GoldbachCircleMethodRamanujanCRTMultiplicativityV1842

/-!
# V1.8.43: standard-character product over the scaled CRT carrier

This module targets the exact character identity and finite-sum product needed for
Ramanujan-sum multiplicativity. It introduces no analytic assumptions.
-/

open scoped BigOperators

namespace GoldbachCircleMethodRamanujanCharacterProductV1843

open GoldbachCircleMethodRamanujanCoprimeBindingV1840
open GoldbachCircleMethodRamanujanCRTMultiplicativityV1842

set_option linter.style.haveILetI false

/-- An explicit integral lift of the scaled CRT parametrization. -/
theorem scaledCRTEquiv_eq_intCast {q r : ℕ} (hq : q ≠ 0) (hr : r ≠ 0)
    (hqr : Nat.Coprime q r) (x : ZMod q × ZMod r) :
    scaledCRTEquiv hq hr hqr x =
      ((r * x.1.cast + q * x.2.cast : ℤ) : ZMod (q * r)) := by
  apply (ZMod.chineseRemainder hqr).injective
  rw [chineseRemainder_scaledCRTEquiv hq hr hqr]
  rw [map_intCast]
  apply Prod.ext
  · simp
  · simp

/-- The positive standard character factors over the scaled CRT coordinates, for every `N`. -/
theorem stdAddChar_scaledCRTEquiv {q r : ℕ} (hq : q ≠ 0) (hr : r ≠ 0)
    (hqr : Nat.Coprime q r) (N : ℕ) (x : ZMod q × ZMod r) :
    (@ZMod.stdAddChar (q * r) ⟨Nat.mul_ne_zero hq hr⟩)
        (scaledCRTEquiv hq hr hqr x * (N : ZMod (q * r))) =
      (@ZMod.stdAddChar q ⟨hq⟩) (x.1 * (N : ZMod q)) *
        (@ZMod.stdAddChar r ⟨hr⟩) (x.2 * (N : ZMod r)) := by
  letI : NeZero q := ⟨hq⟩
  letI : NeZero r := ⟨hr⟩
  letI : NeZero (q * r) := ⟨Nat.mul_ne_zero hq hr⟩
  have harg : scaledCRTEquiv hq hr hqr x * (N : ZMod (q * r)) =
      ((((r * x.1.cast + q * x.2.cast : ℤ) * N : ℤ)) : ZMod (q * r)) := by
    rw [scaledCRTEquiv_eq_intCast hq hr hqr]
    norm_cast
  have hargq : x.1 * (N : ZMod q) = ((x.1.cast * N : ℤ) : ZMod q) := by
    rw [← ZMod.intCast_zmod_cast x.1]
    norm_cast
  have hargr : x.2 * (N : ZMod r) = ((x.2.cast * N : ℤ) : ZMod r) := by
    rw [← ZMod.intCast_zmod_cast x.2]
    norm_cast
  rw [harg, hargq, hargr, ZMod.stdAddChar_coe, ZMod.stdAddChar_coe,
    ZMod.stdAddChar_coe, ← Complex.exp_add]
  congr 1
  push_cast
  field_simp

/-- Genuine multiplicativity of the finite Fourier Ramanujan sum at coprime moduli. -/
theorem finiteFourierRamanujan_mul_of_coprime {q r : ℕ} (hq : q ≠ 0) (hr : r ≠ 0)
    (hqr : Nat.Coprime q r) (N : ℕ) :
    finiteFourierRamanujan (q * r) N (Nat.mul_ne_zero hq hr) =
      finiteFourierRamanujan q N hq * finiteFourierRamanujan r N hr := by
  classical
  letI : NeZero q := ⟨hq⟩
  letI : NeZero r := ⟨hr⟩
  letI : NeZero (q * r) := ⟨Nat.mul_ne_zero hq hr⟩
  let e := scaledCRTEquiv hq hr hqr
  rw [finiteFourierRamanujan, finiteFourierRamanujan, finiteFourierRamanujan]
  rw [← e.sum_comp]
  have hterm (x : ZMod q × ZMod r) :
      (if IsUnit (e x) then
          ZMod.stdAddChar (e x * (N : ZMod (q * r))) else 0) =
        (if IsUnit x.1 then ZMod.stdAddChar (x.1 * (N : ZMod q)) else 0) *
          (if IsUnit x.2 then ZMod.stdAddChar (x.2 * (N : ZMod r)) else 0) := by
    by_cases h1 : IsUnit x.1 <;> by_cases h2 : IsUnit x.2 <;>
      simp [h1, h2, e, isUnit_scaledCRTEquiv_iff hq hr hqr,
        stdAddChar_scaledCRTEquiv hq hr hqr]
  simp_rw [hterm]
  rw [Fintype.sum_prod_type, Fintype.sum_mul_sum]

end GoldbachCircleMethodRamanujanCharacterProductV1843
