import GoldbachCircleMethodPrimitiveConductorRegroupingV18111
import GoldbachCircleMethodRamanujanCharacterProductV1843

set_option autoImplicit false
open scoped BigOperators Classical
open GoldbachCircleMethodFiniteResiduePrefixV1866
open GoldbachCircleMethodRamanujanCRTMultiplicativityV1842
open GoldbachCircleMethodRamanujanCharacterProductV1843

namespace GoldbachCircleMethodCoprimeInducedGaussV18112

variable (r l : ℕ) [NeZero r] [NeZero l]
variable (hcop : Nat.Coprime r l)
local instance productNeZero : NeZero (r*l) := ⟨Nat.mul_ne_zero (NeZero.ne r) (NeZero.ne l)⟩

/-- Actual lifted character on the scaled CRT carrier, including nonunits. -/
theorem changeLevel_scaledCRT (χ : DirichletCharacter ℂ r) (x : ZMod r × ZMod l) :
    (DirichletCharacter.changeLevel (Nat.dvd_mul_right r l) χ)
        (scaledCRTEquiv (NeZero.ne r) (NeZero.ne l) hcop x) =
      if IsUnit x.2 then χ (l : ZMod r) * χ x.1 else 0 := by
  let e := scaledCRTEquiv (NeZero.ne r) (NeZero.ne l) hcop
  have hcast : (ZMod.cast (e x) : ZMod r) = (l : ZMod r) * x.1 := by
    have hc := congrArg Prod.fst
      (chineseRemainder_scaledCRTEquiv (NeZero.ne r) (NeZero.ne l) hcop x)
    change (ZMod.cast (e x) : ZMod r × ZMod l).1 = _ at hc
    simpa only [Prod.fst_zmod_cast] using hc
  by_cases h2 : IsUnit x.2
  · rw [if_pos h2]
    by_cases h1 : IsUnit x.1
    · have hx : IsUnit (e x) :=
        (isUnit_scaledCRTEquiv_iff (NeZero.ne r) (NeZero.ne l) hcop x).mpr ⟨h1,h2⟩
      calc
        _ = χ (ZMod.cast (e x)) := by
          simpa only [hx.unit_spec] using
            DirichletCharacter.changeLevel_eq_cast_of_dvd χ (Nat.dvd_mul_right r l) hx.unit
        _ = _ := by rw [hcast, map_mul]
    · have hx : ¬ IsUnit (e x) := by
        rw [isUnit_scaledCRTEquiv_iff (NeZero.ne r) (NeZero.ne l) hcop x]
        exact fun h => h1 h.1
      rw [MulChar.map_nonunit _ hx, MulChar.map_nonunit χ h1, mul_zero]
  · rw [if_neg h2]
    apply MulChar.map_nonunit
    rw [isUnit_scaledCRTEquiv_iff (NeZero.ne r) (NeZero.ne l) hcop x]
    exact fun h => h2 h.2

include hcop in
/-- Coprime induction Gauss formula at EVERY natural frequency N.
No primitivity or nonvanishing hypothesis; Ramanujan complement is exact. -/
theorem induced_gauss_coprime (χ : DirichletCharacter ℂ r) (N : ℕ) :
    gaussSum (DirichletCharacter.changeLevel (Nat.dvd_mul_right r l) χ)
      (ZMod.stdAddChar.mulShift (N : ZMod (r*l))) =
    χ (l : ZMod r) * gaussSum χ (ZMod.stdAddChar.mulShift (N : ZMod r)) *
      unitCharacterSum l (N : ZMod l) := by
  let e := scaledCRTEquiv (NeZero.ne r) (NeZero.ne l) hcop
  simp only [gaussSum, AddChar.mulShift_apply, unitCharacterSum]
  rw [← e.sum_comp]
  have hterm (x : ZMod r × ZMod l) :
      (DirichletCharacter.changeLevel (Nat.dvd_mul_right r l) χ) (e x) *
          ZMod.stdAddChar ((N : ZMod (r*l)) * e x) =
      (χ (l : ZMod r) * χ x.1 * ZMod.stdAddChar ((N : ZMod r)*x.1)) *
        (if IsUnit x.2 then ZMod.stdAddChar ((N : ZMod l)*x.2) else 0) := by
    rw [changeLevel_scaledCRT]
    have hc := stdAddChar_scaledCRTEquiv (NeZero.ne r) (NeZero.ne l) hcop N x
    rw [mul_comm (N : ZMod (r*l)) (e x), hc]
    by_cases hx : IsUnit x.2 <;> simp only [hx, if_true, if_false, zero_mul, mul_zero]
    · rw [mul_comm x.1 (N : ZMod r), mul_comm x.2 (N : ZMod l)]
      ring
  simp_rw [hterm]
  rw [Fintype.sum_prod_type]
  simp only [← Finset.mul_sum, ← Finset.sum_mul]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring

include hcop in
/-- Primitive parent supplies the nonunit-frequency Gauss shift, explicitly. -/
theorem primitive_induced_gauss_coprime (χ : DirichletCharacter ℂ r)
    (hχ : χ.IsPrimitive) (N : ℕ) :
    gaussSum (DirichletCharacter.changeLevel (Nat.dvd_mul_right r l) χ)
      (ZMod.stdAddChar.mulShift (N : ZMod (r*l))) =
      χ (l : ZMod r) * χ⁻¹ (N : ZMod r) * gaussSum χ ZMod.stdAddChar *
        unitCharacterSum l (N : ZMod l) := by
  rw [induced_gauss_coprime r l hcop χ N,
    gaussSum_mulShift_of_isPrimitive ZMod.stdAddChar hχ]
  ring

include hcop in
/-- Frequency one gives the exact Mobius complement without assuming it nonzero. -/
theorem induced_standard_gauss_coprime (χ : DirichletCharacter ℂ r) :
    gaussSum (DirichletCharacter.changeLevel (Nat.dvd_mul_right r l) χ) ZMod.stdAddChar =
      χ (l : ZMod r) * gaussSum χ ZMod.stdAddChar *
        ((ArithmeticFunction.moebius l : ℤ) : ℂ) := by
  have h := induced_gauss_coprime r l hcop χ 1
  simpa only [Nat.cast_one, AddChar.mulShift_one,
    GoldbachCircleMethodGeneralCoprimeCharacterV1868.unitCharacterSum_eq_moebius
      l 1 isUnit_one] using h

include hcop in
/-- The nonsquarefree complement really vanishes; it is not discarded by a tag. -/
theorem induced_gauss_zero_of_nonsquarefree_complement (χ : DirichletCharacter ℂ r)
    (hl : ¬ Squarefree l) :
    gaussSum (DirichletCharacter.changeLevel (Nat.dvd_mul_right r l) χ) ZMod.stdAddChar = 0 := by
  rw [induced_standard_gauss_coprime r l hcop χ,
    ArithmeticFunction.moebius_eq_zero_of_not_squarefree hl]
  simp

end GoldbachCircleMethodCoprimeInducedGaussV18112
