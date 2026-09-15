import GoldbachCircleMethodArbitraryActiveSlotNegativeWitnessV18257

/-!
# Goldbach V1.8.258: structurally admissible active slots

This module repairs the overbroad raw `CharacterSlot` interface detected by
V1.8.257.  It retains only primitive character slots whose conductor exceeds
one and whose character is self-inverse.  These are structural conditions
only: no exceptional zero, zero location, source match, or analytic budget is
asserted here.
-/

open scoped BigOperators Classical

set_option autoImplicit false

namespace GoldbachCircleMethodStructurallyAdmissibleActiveSlotV18258

open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodActiveExceptionalCenteringV18129
open GoldbachCircleMethodArbitraryActiveSlotNegativeWitnessV18257

/-- Structural conditions required before a raw primitive character slot may
be considered by the active exceptional-character branch.  Self-inverse is
the kernel-level quadratic/reality condition used here; exceptional-zero
attestation remains outside this predicate. -/
def IsStructurallyAdmissibleActiveSlot {Q : ℕ} (e : CharacterSlot Q) : Prop :=
  1 < e.1.val ∧ e.2.val⁻¹ = e.2.val

/-- A dependent subtype prevents the conductor-one principal slot from being
passed to later active-branch interfaces. -/
abbrev StructurallyAdmissibleActiveSlot (Q : ℕ) :=
  {e : CharacterSlot Q // IsStructurallyAdmissibleActiveSlot e}

/-- Explicit forgetful map; using it loses only the proof fields, not the
underlying conductor or character. -/
def StructurallyAdmissibleActiveSlot.toCharacterSlot {Q : ℕ}
    (e : StructurallyAdmissibleActiveSlot Q) : CharacterSlot Q := e.val

theorem admissible_conductor_gt_one {Q : ℕ}
    (e : StructurallyAdmissibleActiveSlot Q) :
    1 < e.val.1.val :=
  e.property.1

theorem admissible_character_self_inverse {Q : ℕ}
    (e : StructurallyAdmissibleActiveSlot Q) :
    e.val.2.val⁻¹ = e.val.2.val :=
  e.property.2

theorem admissible_conductor_ne_one {Q : ℕ}
    (e : StructurallyAdmissibleActiveSlot Q) :
    e.val.1.val ≠ 1 := by
  exact Nat.ne_of_gt e.property.1

/-- The exact counterexample from V1.8.257 cannot satisfy the repaired
structural predicate. -/
theorem principalCharacterSlot_not_structurally_admissible
    (Q : ℕ) (hQ : 1 ≤ Q) :
    ¬ IsStructurallyAdmissibleActiveSlot (principalCharacterSlot Q hQ) := by
  intro h
  have hlt := h.1
  change 1 < 1 at hlt
  omega

/-- No inhabitant of the repaired subtype forgets to the conductor-one
principal slot. -/
theorem admissible_slot_ne_principalCharacterSlot
    (Q : ℕ) (hQ : 1 ≤ Q) (e : StructurallyAdmissibleActiveSlot Q) :
    e.toCharacterSlot ≠ principalCharacterSlot Q hQ := by
  intro heq
  have hlt : 1 < e.val.1.val := e.property.1
  have hconductor := congrArg (fun t : CharacterSlot Q => t.1.val) heq
  change e.val.1.val = 1 at hconductor
  omega

end GoldbachCircleMethodStructurallyAdmissibleActiveSlotV18258
