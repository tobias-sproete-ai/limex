import GoldbachCircleMethodUnitCharacterExpansionAuditV18110

set_option autoImplicit false
open scoped BigOperators Classical
open GoldbachCircleMethodFiniteResiduePrefixV1866

namespace GoldbachCircleMethodPrimitiveConductorRegroupingV18111

/-- The index binds the actual primitive character to its actual level dividing q. -/
abbrev PrimitiveIndex (q : ℕ) :=
  Σ r : {r : ℕ // r ∣ q}, {χ : DirichletCharacter ℂ r.val // χ.IsPrimitive}

noncomputable def liftIndex {q : ℕ} (i : PrimitiveIndex q) : DirichletCharacter ℂ q :=
  DirichletCharacter.changeLevel i.1.property i.2.val

variable (q : ℕ) [NeZero q]

/-- Lifting a primitive character retains its conductor, not just a source tag. -/
theorem conductor_liftIndex (i : PrimitiveIndex q) :
    (liftIndex i).conductor = i.1.val := by
  exact (DirichletCharacter.conductor_changeLevel i.2.val i.1.property).trans i.2.property

omit [NeZero q] in
/-- Existence uses Mathlib's primitiveCharacter and its proved induction identity. -/
theorem liftIndex_surjective : Function.Surjective (@liftIndex q) := by
  intro χ
  exact ⟨⟨⟨χ.conductor, χ.conductor_dvd_level⟩,
    ⟨χ.primitiveCharacter, χ.primitiveCharacter_isPrimitive⟩⟩,
    χ.changeLevel_primitiveCharacter⟩

/-- Uniqueness first fixes the conductor, then uses injectivity of changeLevel. -/
theorem liftIndex_injective : Function.Injective (@liftIndex q) := by
  rintro ⟨⟨r, hr⟩, ⟨χ, hχ⟩⟩ ⟨⟨s, hs⟩, ⟨ψ, hψ⟩⟩ h
  have hrs : r = s := by
    have hc := congrArg DirichletCharacter.conductor h
    simpa only [conductor_liftIndex] using hc
  subst s
  have hχψ : χ = ψ := DirichletCharacter.changeLevel_injective hr h
  cases hχψ
  rfl

/-- A genuine bijection: no primitive-parent existence hypothesis is inserted. -/
noncomputable def primitiveConductorEquiv :
    PrimitiveIndex q ≃ DirichletCharacter ℂ q :=
  Equiv.ofBijective liftIndex ⟨liftIndex_injective q, liftIndex_surjective q⟩

noncomputable instance primitiveIndexFintype : Fintype (PrimitiveIndex q) :=
  Fintype.ofEquiv (DirichletCharacter ℂ q) (primitiveConductorEquiv q).symm

/-- Nonzero ambient level excludes the degenerate level-zero parent. -/
theorem primitive_index_ne_zero (i : PrimitiveIndex q) : i.1.val ≠ 0 := by
  intro hz
  have h := i.1.property
  rw [hz, zero_dvd_iff] at h
  exact NeZero.ne q h

/-- The principal ambient level is retained; it is not lost at q=1. -/
theorem level_one_index (i : PrimitiveIndex 1) : i.1.val = 1 :=
  Nat.dvd_one.mp i.1.property

/-- Exact finite reindexing of any complex coefficient function. -/
theorem sum_over_primitive_conductors (F : DirichletCharacter ℂ q → ℂ) :
    (∑ i : PrimitiveIndex q, F (liftIndex i)) =
      ∑ χ : DirichletCharacter ℂ q, F χ := by
  exact (primitiveConductorEquiv q).sum_comp F

/-- The actual full Gauss expansion, now indexed by unique primitive parents.
No squarefreeness of the conductor or nonvanishing Gauss sum is assumed. -/
theorem ramanujan_gauss_primitive_conductor_expansion
    (n u : ZMod q) (hu : IsUnit u) :
    (∑ i : PrimitiveIndex q, (liftIndex i) u⁻¹ *
      ((liftIndex i)⁻¹ (-1) * gaussSum (liftIndex i) ZMod.stdAddChar *
        gaussSum (liftIndex i)⁻¹ (ZMod.stdAddChar.mulShift n))) =
      (q.totient : ℂ) * unitCharacterSum q (n-u) := by
  calc
    _ = ∑ χ : DirichletCharacter ℂ q, χ u⁻¹ *
        (χ⁻¹ (-1) * gaussSum χ ZMod.stdAddChar *
          gaussSum χ⁻¹ (ZMod.stdAddChar.mulShift n)) :=
      sum_over_primitive_conductors q (fun χ => χ u⁻¹ *
        (χ⁻¹ (-1) * gaussSum χ ZMod.stdAddChar *
          gaussSum χ⁻¹ (ZMod.stdAddChar.mulShift n)))
    _ = _ :=
      GoldbachCircleMethodUnitCharacterExpansionAuditV18110.ramanujan_full_gauss_expansion
        q n u hu

end GoldbachCircleMethodPrimitiveConductorRegroupingV18111
