import GoldbachCircleMethodGlobalCollisionAbsoluteRouteObstructionV18577
import Mathlib.NumberTheory.MulChar.Lemmas

/-!
# Goldbach V1.8.578: primitive lift separation

Primitive Dirichlet characters of distinct conductor levels remain distinct
after both are lifted to a common nonzero multiple.  Consequently their bare
character layers are Hermitian-orthogonal on that complete ambient residue
ring.  This does not yet prove orthogonality of the full twisted Ramanujan
atoms, whose complementary Ramanujan factors remain coupled.
-/

set_option autoImplicit false

open scoped BigOperators Classical ComplexConjugate

namespace GoldbachCircleMethodPrimitiveLiftSeparationV18578

/-- Distinct primitive conductor levels cannot become the same character after
change of level to a common nonzero multiple. -/
theorem primitive_changeLevel_ne_of_level_ne
    {r s d : ℕ} [NeZero d]
    (hr : r ∣ d) (hs : s ∣ d)
    (χ : DirichletCharacter ℂ r) (ψ : DirichletCharacter ℂ s)
    (hχ : χ.IsPrimitive) (hψ : ψ.IsPrimitive)
    (hrs : r ≠ s) :
    DirichletCharacter.changeLevel hr χ ≠
      DirichletCharacter.changeLevel hs ψ := by
  intro heq
  have hc := congrArg DirichletCharacter.conductor heq
  have hlevels : r = s := by
    rw [DirichletCharacter.conductor_changeLevel,
      DirichletCharacter.conductor_changeLevel] at hc
    exact hχ.symm.trans (hc.trans hψ)
  exact hrs hlevels

/-- The bare lifted primitive-character layers are Hermitian-orthogonal on the
common complete period.  No Ramanujan complement factor is present here. -/
theorem primitive_changeLevel_inner_zero
    {r s d : ℕ} [NeZero d]
    (hr : r ∣ d) (hs : s ∣ d)
    (χ : DirichletCharacter ℂ r) (ψ : DirichletCharacter ℂ s)
    (hχ : χ.IsPrimitive) (hψ : ψ.IsPrimitive)
    (hrs : r ≠ s) :
    (∑ x : ZMod d,
      star ((DirichletCharacter.changeLevel hr χ) x) *
        (DirichletCharacter.changeLevel hs ψ) x) = 0 := by
  let χd : DirichletCharacter ℂ d := DirichletCharacter.changeLevel hr χ
  let ψd : DirichletCharacter ℂ d := DirichletCharacter.changeLevel hs ψ
  have hne : χd ≠ ψd := by
    exact primitive_changeLevel_ne_of_level_ne hr hs χ ψ hχ hψ hrs
  have hprod : χd⁻¹ * ψd ≠ 1 := by
    intro h
    have hEq : ψd = χd := by
      simpa [mul_assoc] using congrArg (fun z => χd * z) h
    exact hne hEq.symm
  have hz := MulChar.sum_eq_zero_of_ne_one hprod
  simpa only [← MulChar.mul_apply, MulChar.star_apply'] using hz

end GoldbachCircleMethodPrimitiveLiftSeparationV18578
