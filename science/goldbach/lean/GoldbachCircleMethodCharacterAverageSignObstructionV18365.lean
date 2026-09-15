import GoldbachCircleMethodCanonicalChiFourAdequacyCorrectionV18364

/-!
# Goldbach V1.8.365: character-average sign obstruction

The pairwise `Q^4` boundary method removes the common-LCM cost, but the exact
arithmetic mean still contains a Moebius/character first marginal.  This
module tests whether complete target-residue averaging can eliminate that
remaining channel.

For every nontrivial self-inverse character with nonzero Moebius factor, the
positive and negative unit-target signs are both inhabited.  At the same
time, the complete finite marginal sum is exactly zero by character
orthogonality.  Thus residue averaging cancels the signed first moment but
does not provide a pointwise sign exclusion or an exceptional-set estimate.

This is a finite negative interface witness.  It asserts no exceptional zero,
no Goldbach counterexample, and no Goldbach theorem.
-/

set_option autoImplicit false
open scoped BigOperators Classical

namespace GoldbachCircleMethodCharacterAverageSignObstructionV18365

open GoldbachCircleMethodExceptionalModelDiagonalV18107
open GoldbachCircleMethodSourceMatchedExceptionalZeroGateV18363
open GoldbachCircleMethodStructurallyAdmissibleActiveSlotV18258

/-- If the Moebius sign is nonzero, a nontrivial self-inverse character has a
unit residue on which the first marginal is positive. -/
theorem exists_unit_positive_marginal
    (r : ℕ) [NeZero r]
    (chi : DirichletCharacter ℂ r)
    (hInv : chi⁻¹ = chi)
    (hne : chi ≠ 1)
    (hmu : ArithmeticFunction.moebius r = 1 ∨
      ArithmeticFunction.moebius r = -1) :
    ∃ a : ZMod r, IsUnit a ∧
      ((((ArithmeticFunction.moebius r : ℤ) : ℂ) * chi a).re) = 1 := by
  rcases hmu with hmu | hmu
  · refine ⟨1, isUnit_one, ?_⟩
    simp [hmu]
  · obtain ⟨u, hu⟩ := MulChar.ne_one_iff.mp hne
    let a : ZMod r := u
    have ha : IsUnit a := u.isUnit
    have hs := quadratic_value_square r chi hInv a
    rw [if_pos ha] at hs
    rcases mul_self_eq_one_iff.mp hs with hchi | hchi
    · exfalso
      apply hu
      simpa [a] using hchi
    · refine ⟨a, ha, ?_⟩
      simp [hmu, hchi]

/-- The opposite sign is inhabited as well. -/
theorem exists_unit_negative_marginal
    (r : ℕ) [NeZero r]
    (chi : DirichletCharacter ℂ r)
    (hInv : chi⁻¹ = chi)
    (hne : chi ≠ 1)
    (hmu : ArithmeticFunction.moebius r = 1 ∨
      ArithmeticFunction.moebius r = -1) :
    ∃ a : ZMod r, IsUnit a ∧
      ((((ArithmeticFunction.moebius r : ℤ) : ℂ) * chi a).re) = -1 := by
  rcases hmu with hmu | hmu
  · obtain ⟨u, hu⟩ := MulChar.ne_one_iff.mp hne
    let a : ZMod r := u
    have ha : IsUnit a := u.isUnit
    have hs := quadratic_value_square r chi hInv a
    rw [if_pos ha] at hs
    rcases mul_self_eq_one_iff.mp hs with hchi | hchi
    · exfalso
      apply hu
      simpa [a] using hchi
    · refine ⟨a, ha, ?_⟩
      simp [hmu, hchi]
  · refine ⟨1, isUnit_one, ?_⟩
    simp [hmu]

/-- Complete finite target-residue averaging cancels the first marginal
exactly.  This is a signed first-moment identity, not a pointwise bound. -/
theorem first_marginal_sum_eq_zero
    (r : ℕ) [NeZero r]
    (chi : DirichletCharacter ℂ r)
    (hne : chi ≠ 1) :
    ∑ a : ZMod r,
        ((ArithmeticFunction.moebius r : ℤ) : ℂ) * chi a = 0 := by
  rw [← Finset.mul_sum, MulChar.sum_eq_zero_of_ne_one hne, mul_zero]

/-- Source-structural readback: every admissible active slot with nonzero
Moebius factor contains both first-marginal signs.  An actual L-function zero
is neither assumed nor constructed. -/
theorem admissible_slot_has_both_marginal_signs
    {Q : ℕ} (e : StructurallyAdmissibleActiveSlot Q)
    (hmu : ArithmeticFunction.moebius e.val.1.val ≠ 0) :
    (∃ a : ZMod e.val.1.val, IsUnit a ∧
      ((((ArithmeticFunction.moebius e.val.1.val : ℤ) : ℂ) *
        e.val.2.val a).re) = 1) ∧
    (∃ a : ZMod e.val.1.val, IsUnit a ∧
      ((((ArithmeticFunction.moebius e.val.1.val : ℤ) : ℂ) *
        e.val.2.val a).re) = -1) := by
  have hsign := ArithmeticFunction.moebius_ne_zero_iff_eq_or.mp hmu
  constructor
  · exact exists_unit_positive_marginal e.val.1.val e.val.2.val
      e.property.2 (admissible_character_ne_one e) hsign
  · exact exists_unit_negative_marginal e.val.1.val e.val.2.val
      e.property.2 (admissible_character_ne_one e) hsign

end GoldbachCircleMethodCharacterAverageSignObstructionV18365
