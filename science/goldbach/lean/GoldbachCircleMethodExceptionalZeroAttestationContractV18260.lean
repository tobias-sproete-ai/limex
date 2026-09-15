import GoldbachCircleMethodAdmissibleSlotAdjustedReserveV18259

/-!
# Goldbach V1.8.260: exceptional-zero attestation contract

An exceptional zero is not defined by bibliographic metadata and is not
inferred from structural character fields.  The exact analytic predicate is a
parameter.  An active attestation must carry a proof of that predicate, a
structurally admissible slot, and an exponent in `[0,1]`.
-/

open scoped Classical BigOperators

set_option autoImplicit false

namespace GoldbachCircleMethodExceptionalZeroAttestationContractV18260

open GoldbachCircleMethodActiveExceptionalCenteringV18129
open GoldbachCircleMethodStructurallyAdmissibleActiveSlotV18258

/-- Proof-carrying active exceptional-zero data.  `ExceptionalZeroAt` must be
instantiated by the later source-matched analytic module; this structure does
not define or assert that predicate. -/
structure ExceptionalZeroAttestation
    (Q : ℕ)
    (ExceptionalZeroAt : StructurallyAdmissibleActiveSlot Q → ℝ → Prop) where
  slot : StructurallyAdmissibleActiveSlot Q
  beta : ℝ
  beta_nonneg : 0 ≤ beta
  beta_le_one : beta ≤ 1
  attested : ExceptionalZeroAt slot beta

/-- A complete branch decision is itself proof-carrying: either the caller
proves absence in the declared predicate/range or supplies one active
attestation.  No branch is selected by this definition. -/
inductive ExceptionalZeroCase
    (Q : ℕ)
    (ExceptionalZeroAt : StructurallyAdmissibleActiveSlot Q → ℝ → Prop) : Type
  | absent
      (no_zero : ∀ (e : StructurallyAdmissibleActiveSlot Q) (beta : ℝ),
        0 ≤ beta → beta ≤ 1 → ¬ ExceptionalZeroAt e beta)
  | active (data : ExceptionalZeroAttestation Q ExceptionalZeroAt)

theorem attested_slot_conductor_gt_one
    {Q : ℕ}
    {ExceptionalZeroAt : StructurallyAdmissibleActiveSlot Q → ℝ → Prop}
    (d : ExceptionalZeroAttestation Q ExceptionalZeroAt) :
    1 < d.slot.val.1.val :=
  d.slot.property.1

theorem attested_slot_ne_principal
    {Q : ℕ}
    {ExceptionalZeroAt : StructurallyAdmissibleActiveSlot Q → ℝ → Prop}
    (hQ : 1 ≤ Q) (d : ExceptionalZeroAttestation Q ExceptionalZeroAt) :
    d.slot.toCharacterSlot ≠
      GoldbachCircleMethodArbitraryActiveSlotNegativeWitnessV18257.principalCharacterSlot Q hQ :=
  admissible_slot_ne_principalCharacterSlot Q hQ d.slot

theorem active_case_exposes_attested_predicate
    {Q : ℕ}
    {ExceptionalZeroAt : StructurallyAdmissibleActiveSlot Q → ℝ → Prop}
    (d : ExceptionalZeroAttestation Q ExceptionalZeroAt) :
    ExceptionalZeroAt d.slot d.beta :=
  d.attested

/-- Eliminator exposing that a supplied case contains actual proof data on
both branches, not a Boolean or metadata flag. -/
theorem exceptionalZeroCase_elim
    {Q : ℕ}
    {ExceptionalZeroAt : StructurallyAdmissibleActiveSlot Q → ℝ → Prop}
    (c : ExceptionalZeroCase Q ExceptionalZeroAt)
    (P : Prop)
    (hAbsent :
      (∀ (e : StructurallyAdmissibleActiveSlot Q) (beta : ℝ),
        0 ≤ beta → beta ≤ 1 → ¬ ExceptionalZeroAt e beta) → P)
    (hActive : ExceptionalZeroAttestation Q ExceptionalZeroAt → P) : P := by
  cases c with
  | absent h => exact hAbsent h
  | active d => exact hActive d

end GoldbachCircleMethodExceptionalZeroAttestationContractV18260

