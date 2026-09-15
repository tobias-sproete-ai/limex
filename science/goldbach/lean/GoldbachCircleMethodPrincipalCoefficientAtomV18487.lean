import GoldbachCircleMethodSupportSeparatedWitnessTransferV18486

/-!
# Goldbach V1.8.487: exact principal-coefficient atom

The coefficient energy restricted to conductor one is not a growing family:
both its positive level and its primitive character are unique.  This module
collapses the restricted sum exactly to the squared norm of the canonical
finite companion.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodPrincipalCoefficientAtomV18487

open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodFiniteCompanionBindingV18118
open GoldbachCircleMethodPrincipalSupportEnergySplitV18483
open GoldbachCircleMethodPrincipalWindowBoundaryV18121

/-- The conductor-one coefficient energy is exactly one atom; there is no
hidden character-family cardinality loss. -/
theorem principalCoefficientEnergy_eq_finiteCompanion_sq
    (Q N : ℕ) (hQ : 1 ≤ Q) (w : ℕ → ℂ) :
    principalCoefficientEnergy Q N w =
      ‖finiteCompanion (oneLevel hQ) N w‖ ^ 2 := by
  unfold principalCoefficientEnergy
  rw [Fintype.sum_sigma]
  rw [Finset.sum_eq_single (oneLevel hQ)]
  · change (∑ chi : {chi : DirichletCharacter ℂ 1 // chi.IsPrimitive},
      if (1 : ℕ) = 1 then
        ‖windowCoefficient (oneLevel hQ) N w chi‖ ^ 2 else 0) = _
    rw [Finset.sum_eq_single
      (⟨1, DirichletCharacter.isPrimitive_one_level_one⟩ :
        {chi : DirichletCharacter ℂ 1 // chi.IsPrimitive})]
    · simp only [if_true]
      simp only [windowCoefficient, oneLevel, Nat.totient_one, Nat.cast_one,
        div_one, one_mul]
      erw [level_one_character_value (1 : DirichletCharacter ℂ 1) N]
      rw [one_mul]
    · intro chi _hmem hne
      exact False.elim (hne (primitive_level_one_unique chi))
    · simp only [Finset.mem_univ, not_true_eq_false, false_implies]
  · intro r _hmem hr
    have hne : r.val ≠ 1 := by
      intro hval
      exact hr (Subtype.ext hval)
    simp only [hne, if_false, Finset.sum_const_zero]
  · simp only [Finset.mem_univ, not_true_eq_false, false_implies]

end GoldbachCircleMethodPrincipalCoefficientAtomV18487
