import GoldbachCircleMethodNoncoprimeInducedGaussV18113

set_option autoImplicit false
open scoped BigOperators Classical
open GoldbachCircleMethodFiniteResiduePrefixV1866
open GoldbachCircleMethodUnitCharacterExpansionAuditV18110
open GoldbachCircleMethodCoprimeInducedGaussV18112
open GoldbachCircleMethodNoncoprimeInducedGaussV18113

namespace GoldbachCircleMethodPrimitiveGaussCoefficientV18114

variable {r : ℕ} [NeZero r]

omit [NeZero r] in
/-- Primitivity of the inverse is inherited from the actual conductor theorem. -/
theorem inverse_isPrimitive (χ : DirichletCharacter ℂ r) (hχ : χ.IsPrimitive) :
    χ⁻¹.IsPrimitive := by
  change χ⁻¹.conductor = r
  rw [DirichletCharacter.conductor_inv]
  exact hχ

/-- The sign-normalized primitive Gauss product on ANY positive level,
including level one; no field structure on ZMod r is assumed. -/
theorem primitive_gauss_product (χ : DirichletCharacter ℂ r) (hχ : χ.IsPrimitive) :
    χ⁻¹ (-1) * gaussSum χ ZMod.stdAddChar * gaussSum χ⁻¹ ZMod.stdAddChar =
      (r : ℂ) := by
  have hg := general_ramanujan_gauss_coefficient r χ 1
  have hp := primitive_ramanujan_coefficient r χ hχ 1
  rw [hp] at hg
  simpa only [AddChar.mulShift_one, map_one, mul_one] using hg.symm

variable (r l : ℕ) [NeZero r] [NeZero l]
local instance productNeZero : NeZero (r*l) := ⟨Nat.mul_ne_zero (NeZero.ne r) (NeZero.ne l)⟩

omit [NeZero r] [NeZero l] in
/-- Lifting preserves the inverse character's value at minus one exactly. -/
theorem lifted_inverse_neg_one (χ : DirichletCharacter ℂ r) :
    (DirichletCharacter.changeLevel (Nat.dvd_mul_right r l) χ)⁻¹ (-1) = χ⁻¹ (-1) := by
  rw [← map_inv]
  have h := DirichletCharacter.changeLevel_eq_cast_of_dvd χ⁻¹
    (Nat.dvd_mul_right r l) (-1 : (ZMod (r*l))ˣ)
  simpa only [Units.val_neg, Units.val_one, ZMod.cast_neg (Nat.dvd_mul_right r l),
    ZMod.cast_one (Nat.dvd_mul_right r l)] using h

/-- The complete Gauss coefficient of a primitive lift on a coprime complement.
The natural frequency N is arbitrary, including nonunit frequencies. -/
theorem lifted_gauss_coefficient_coprime (hcop : Nat.Coprime r l)
    (χ : DirichletCharacter ℂ r) (hχ : χ.IsPrimitive) (N : ℕ) :
    (DirichletCharacter.changeLevel (Nat.dvd_mul_right r l) χ)⁻¹ (-1) *
      gaussSum (DirichletCharacter.changeLevel (Nat.dvd_mul_right r l) χ) ZMod.stdAddChar *
      gaussSum (DirichletCharacter.changeLevel (Nat.dvd_mul_right r l) χ)⁻¹
        (ZMod.stdAddChar.mulShift (N : ZMod (r*l))) =
      (r : ℂ) * ((ArithmeticFunction.moebius l : ℤ) : ℂ) *
        unitCharacterSum l (N : ZMod l) * χ (N : ZMod r) := by
  rw [lifted_inverse_neg_one, induced_standard_gauss, ← map_inv,
    primitive_induced_gauss_coprime r l hcop χ⁻¹ (inverse_isPrimitive χ hχ) N, inv_inv]
  have hu : IsUnit (l : ZMod r) := (ZMod.isUnit_iff_coprime l r).mpr hcop.symm
  have hi : χ⁻¹ (l : ZMod r) * χ (l : ZMod r) = 1 := by
    have h := congrArg (fun ψ : DirichletCharacter ℂ r => ψ (l : ZMod r)) (inv_mul_cancel χ)
    simpa only [MulChar.mul_apply, MulChar.one_apply hu] using h
  calc
    _ = (χ⁻¹ (-1) * gaussSum χ ZMod.stdAddChar * gaussSum χ⁻¹ ZMod.stdAddChar) *
        (χ⁻¹ (l : ZMod r) * χ (l : ZMod r)) *
        ((ArithmeticFunction.moebius l : ℤ) : ℂ) *
        unitCharacterSum l (N : ZMod l) * χ (N : ZMod r) := by ring
    _ = _ := by rw [primitive_gauss_product χ hχ, hi, mul_one]

/-- Exact all-complements coefficient. A noncoprime lift contributes zero because
its standard Gauss factor vanishes, not by an unproved support restriction. -/
theorem lifted_gauss_coefficient (χ : DirichletCharacter ℂ r) (hχ : χ.IsPrimitive)
    (N : ℕ) :
    (DirichletCharacter.changeLevel (Nat.dvd_mul_right r l) χ)⁻¹ (-1) *
      gaussSum (DirichletCharacter.changeLevel (Nat.dvd_mul_right r l) χ) ZMod.stdAddChar *
      gaussSum (DirichletCharacter.changeLevel (Nat.dvd_mul_right r l) χ)⁻¹
        (ZMod.stdAddChar.mulShift (N : ZMod (r*l))) =
      if Nat.Coprime r l then
        (r : ℂ) * ((ArithmeticFunction.moebius l : ℤ) : ℂ) *
          unitCharacterSum l (N : ZMod l) * χ (N : ZMod r)
      else 0 := by
  by_cases hcop : Nat.Coprime r l
  · rw [if_pos hcop]
    exact lifted_gauss_coefficient_coprime r l hcop χ hχ N
  · rw [if_neg hcop, induced_gauss_zero_of_noncoprime r l hcop χ]
    ring

/-- The actual finite convolution coefficient equals the explicit primitive
formula; neither an abstract coefficient nor a conjectured Gauss identity is used. -/
theorem lifted_ramanujan_coefficient (χ : DirichletCharacter ℂ r) (hχ : χ.IsPrimitive)
    (N : ℕ) :
    (∑ v : ZMod (r*l), (DirichletCharacter.changeLevel (Nat.dvd_mul_right r l) χ) v *
      unitCharacterSum (r*l) ((N : ZMod (r*l))-v)) =
      if Nat.Coprime r l then
        (r : ℂ) * ((ArithmeticFunction.moebius l : ℤ) : ℂ) *
          unitCharacterSum l (N : ZMod l) * χ (N : ZMod r)
      else 0 := by
  rw [general_ramanujan_gauss_coefficient, lifted_gauss_coefficient r l χ hχ N]

end GoldbachCircleMethodPrimitiveGaussCoefficientV18114
