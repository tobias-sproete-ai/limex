import GoldbachCircleMethodCentralSingleSourceEnergyGateV18459
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.NumberTheory.DirichletCharacter.Bounds

/-!
# Goldbach V1.8.460: exact full-character Parseval identity on units

This module isolates the finite Fourier identity needed before estimating the
actual adjusted source energy.  It sums over every Dirichlet character of one
fixed nonzero modulus and over the unit group of that modulus.  No analytic
estimate, primitive-character reduction or Goldbach conclusion is asserted.

The result is deliberately exact: the character energy equals the totient
times the coefficient energy.  Later modules may bound the primitive slots by
this full family without paying the crude number-of-slots factor.
-/

set_option autoImplicit false

open scoped BigOperators Classical ComplexConjugate

namespace GoldbachCircleMethodFullCharacterUnitParsevalV18460

variable (q : ℕ) [NeZero q]

/-- Complex-valued character transform of a coefficient family on the unit
group modulo `q`. -/
noncomputable def unitCharacterTransform
    (A : (ZMod q)ˣ → ℂ) (chi : DirichletCharacter ℂ q) : ℂ :=
  ∑ u : (ZMod q)ˣ, A u * chi (u : ZMod q)

/-- Exact finite Parseval identity for all Dirichlet characters modulo `q`.
The equality is stated in `ℂ` so that character orthogonality can be used
without any loss-producing norm inequality. -/
theorem full_character_unit_parseval_complex (A : (ZMod q)ˣ → ℂ) :
    (∑ chi : DirichletCharacter ℂ q,
        star (unitCharacterTransform q A chi) * unitCharacterTransform q A chi) =
      (q.totient : ℂ) * ∑ u : (ZMod q)ˣ, star (A u) * A u := by
  unfold unitCharacterTransform
  simp only [star_sum, star_mul, MulChar.star_apply']
  simp_rw [Fintype.sum_mul_sum]
  rw [Finset.sum_comm]
  conv_lhs =>
    enter [2, u]
    rw [Finset.sum_comm]
  have hinv (chi : DirichletCharacter ℂ q) (u : (ZMod q)ˣ) :
      chi⁻¹ (u : ZMod q) = chi ((u : ZMod q)⁻¹) := by
    rw [MulChar.inv_apply_eq_inv']
    calc
      (chi (u : ZMod q))⁻¹ = (((chi.toUnitHom u : ℂˣ) : ℂ))⁻¹ := by
        rw [MulChar.coe_toUnitHom]
      _ = (((chi.toUnitHom u)⁻¹ : ℂˣ) : ℂ) := by
        rw [Units.val_inv_eq_inv_val]
      _ = ((chi.toUnitHom (u⁻¹) : ℂˣ) : ℂ) := by rw [map_inv]
      _ = chi ((u⁻¹ : (ZMod q)ˣ) : ZMod q) := by rw [MulChar.coe_toUnitHom]
      _ = chi ((u : ZMod q)⁻¹) := by rw [ZMod.inv_coe_unit]
  simp_rw [hinv]
  simp_rw [show ∀ (u v : (ZMod q)ˣ) (chi : DirichletCharacter ℂ q),
      (chi ((u : ZMod q)⁻¹) * star (A u)) * (A v * chi (v : ZMod q)) =
        (star (A u) * A v) *
          (chi ((u : ZMod q)⁻¹) * chi (v : ZMod q)) by
            intro u v chi
            ring]
  simp_rw [← Finset.mul_sum]
  have hortho (u v : (ZMod q)ˣ) :
      (∑ chi : DirichletCharacter ℂ q,
          chi ((u : ZMod q)⁻¹) * chi (v : ZMod q)) =
        if u = v then (q.totient : ℂ) else 0 := by
    simpa only [Units.val_inj] using
      DirichletCharacter.sum_char_inv_mul_char_eq ℂ u.isUnit (v : ZMod q)
  simp_rw [hortho]
  simp [mul_comm]
  rw [Finset.mul_sum]

end GoldbachCircleMethodFullCharacterUnitParsevalV18460
