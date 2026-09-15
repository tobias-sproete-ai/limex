import GoldbachCircleMethodHybridCenteredCorrelationEnergyV18501
import GoldbachCircleMethodPrincipalCoefficientAtomV18487

/-!
# Goldbach V1.8.502: exact hybrid principal atoms

The coefficient and source energies of the repaired principal channel are
collapsed to their unique conductor-one atom.  In particular, no character-
family cardinality or pre-triangle `Lambda`/constant separation is introduced.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodHybridPrincipalAtomsV18502

open GoldbachCircleMethodActiveExceptionalCenteringV18129
open GoldbachCircleMethodAdjustedCharacterSlotL2AdapterV18449
open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodFiniteCompanionBindingV18118
open GoldbachCircleMethodFiniteWindowConvolutionV18119
open GoldbachCircleMethodHybridCenteredCorrelationEnergyV18501
open GoldbachCircleMethodHybridCenteredSourceSplitV18500
open GoldbachCircleMethodLogCutoffPresieveBindingV18120
open GoldbachCircleMethodPrincipalCoefficientAtomV18487
open GoldbachCircleMethodPrincipalSupportEnergySplitV18483
open GoldbachCircleMethodPrincipalWindowBoundaryV18121

/-- The repaired coefficient energy is definitionally the old exact
conductor-one coefficient energy. -/
theorem centeredPrincipalCoefficientEnergy_eq_principalCoefficientEnergy
    (Q N : ℕ) (w : ℕ → ℂ) :
    centeredPrincipalCoefficientEnergy Q N w =
      principalCoefficientEnergy Q N w := by
  rfl

/-- Hence the repaired coefficient channel is exactly one finite-companion
atom. -/
theorem centeredPrincipalCoefficientEnergy_eq_finiteCompanion_sq
    (Q N : ℕ) (hQ : 1 ≤ Q) (w : ℕ → ℂ) :
    centeredPrincipalCoefficientEnergy Q N w =
      ‖finiteCompanion (oneLevel hQ) N w‖ ^ 2 := by
  rw [centeredPrincipalCoefficientEnergy_eq_principalCoefficientEnergy]
  exact principalCoefficientEnergy_eq_finiteCompanion_sq Q N hQ w

/-- The full literal coefficient energy partitions exactly into the principal
and nonprincipal supports used by V1.8.501. -/
theorem adjustedCoefficientEnergy_eq_hybridCoefficientEnergies
    (Q N : ℕ) (w : ℕ → ℂ) :
    adjustedCoefficientEnergy Q N w =
      centeredPrincipalCoefficientEnergy Q N w +
        nonprincipalCoefficientEnergy Q N w := by
  unfold adjustedCoefficientEnergy centeredPrincipalCoefficientEnergy
    nonprincipalCoefficientEnergy
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t _ht
  by_cases hprincipal : t.1.val = 1 <;> simp [hprincipal]

/-- The unique primitive character at conductor one, packaged as the literal
character-slot index. -/
noncomputable def principalCharacterSlot (Q : ℕ) (hQ : 1 ≤ Q) :
    CharacterSlot Q :=
  ⟨oneLevel hQ,
    ⟨1, DirichletCharacter.isPrimitive_one_level_one⟩⟩

/-- The repaired principal source energy contains exactly the unique
conductor-one source atom. -/
theorem centeredPrincipalSourceEnergy_eq_atom
    (Q B N : ℕ) (H : ℝ) (hQ : 1 ≤ Q) :
    centeredPrincipalSourceEnergy Q B N H =
      ‖centeredPrincipalSlotSource Q B N H
        (principalCharacterSlot Q hQ)‖ ^ 2 := by
  unfold centeredPrincipalSourceEnergy
  rw [Fintype.sum_sigma]
  rw [Finset.sum_eq_single (oneLevel hQ)]
  · change (∑ chi : {chi : DirichletCharacter ℂ 1 // chi.IsPrimitive},
      ‖centeredPrincipalSlotSource Q B N H ⟨oneLevel hQ, chi⟩‖ ^ 2) = _
    rw [Finset.sum_eq_single
      (⟨1, DirichletCharacter.isPrimitive_one_level_one⟩ :
        {chi : DirichletCharacter ℂ 1 // chi.IsPrimitive})]
    · rfl
    · intro chi _hmem hne
      exact False.elim (hne (primitive_level_one_unique chi))
    · simp only [Finset.mem_univ, not_true_eq_false, false_implies]
  · intro r _hmem hr
    have hne : r.val ≠ 1 := by
      intro hval
      exact hr (Subtype.ext hval)
    simp [centeredPrincipalSlotSource, hne]
  · simp only [Finset.mem_univ, not_true_eq_false, false_implies]

/-- Exact source readback: the unique principal atom is the normalized local
`blockInput - 1` discrepancy. -/
theorem centeredPrincipalSourceEnergy_eq_centered_discrepancy_sq
    (Q B N : ℕ) (H : ℝ) (hQ : 1 ≤ Q) :
    centeredPrincipalSourceEnergy Q B N H =
      ‖(2 * (H : ℂ))⁻¹ *
        ∑ U ∈ centeredWindow (blockCarrier B) N H,
          (blockInput B U - 1)‖ ^ 2 := by
  rw [centeredPrincipalSourceEnergy_eq_atom Q B N H hQ]
  rw [centeredPrincipalSlotSource_eq_centered_sum]
  · apply congrArg (fun z : ℂ => ‖z‖ ^ 2)
    congr 1
    apply Finset.sum_congr rfl
    intro U _hU
    have hcharacter :
        ((principalCharacterSlot Q hQ).2.val
          (U : ZMod (principalCharacterSlot Q hQ).1.val)) = 1 := by
      change (1 : DirichletCharacter ℂ 1) (U : ZMod 1) = 1
      exact level_one_character_value (1 : DirichletCharacter ℂ 1) U
    simp [hcharacter]
  · rfl

end GoldbachCircleMethodHybridPrincipalAtomsV18502
