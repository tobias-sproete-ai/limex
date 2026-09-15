import GoldbachCircleMethodPrimitiveChiFourFullMeanNegativeWitnessV18360
import GoldbachCircleMethodExceptionalZeroGapAttestationRepairV18263

/-!
# Goldbach V1.8.361: exceptional-predicate adequacy gap witness

The proof-carrying exceptional-zero interface is logically sound only relative
to the predicate supplied by its caller.  This module shows why the still
missing source-matched predicate is mathematically essential: the predicate
`True` admits the genuine primitive character modulo four and its exact
pairwise mean remains `-1/4`.

This is an adequacy boundary, not an inconsistency.  All theorems downstream
of the abstract predicate remain conditional.  Promotion requires a concrete
definition tying `ExceptionalZeroAt` to a zero of the corresponding
Dirichlet L-function and the analytic source range.
-/

set_option autoImplicit false
open scoped BigOperators Classical

namespace GoldbachCircleMethodExceptionalPredicateAdequacyGapWitnessV18361

open GoldbachCircleMethodActiveExceptionalCenteringV18129
open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodStructurallyAdmissibleActiveSlotV18258
open GoldbachCircleMethodExceptionalZeroGapAttestationRepairV18263
open GoldbachCircleMethodPrimitiveChiFourFullMeanNegativeWitnessV18360
open GoldbachCircleMethodSignedDiagonalResidualCounterexampleV18339
open GoldbachCircleMethodFullFrozenPairwiseIntervalV18323

noncomputable def chiFourCharacterSlot : CharacterSlot 4 :=
  ⟨fourLevel, complexChiFourPrimitive⟩

theorem chiFourCharacterSlot_structurally_admissible :
    IsStructurallyAdmissibleActiveSlot chiFourCharacterSlot := by
  constructor
  · norm_num [chiFourCharacterSlot, fourLevel]
  · exact complexChiFour_inv

noncomputable def chiFourAdmissibleSlot : StructurallyAdmissibleActiveSlot 4 :=
  ⟨chiFourCharacterSlot, chiFourCharacterSlot_structurally_admissible⟩

/-- A deliberately content-free predicate exposing the interface boundary. -/
def vacuousExceptionalZeroAt
    (_ : StructurallyAdmissibleActiveSlot 4) (_ : ℝ) : Prop := True

/-- The current generic contract can be inhabited for an arbitrary predicate;
that inhabitant by itself therefore cannot certify an actual L-function zero. -/
noncomputable def vacuousChiFourAttestation :
    ExceptionalZeroGapAttestation 4 vacuousExceptionalZeroAt where
  slot := chiFourAdmissibleSlot
  beta := 1 / 2
  beta_pos := by norm_num
  beta_lt_one := by norm_num
  attested := trivial

/-- Even a proof-carrying inhabitant of the generic interface can accompany a
negative exact full mean when the supplied predicate is not source-matched. -/
theorem generic_exceptional_predicate_admits_negative_full_mean :
    ∃ d : ExceptionalZeroGapAttestation 4 vacuousExceptionalZeroAt,
      (fullFrozenPairwiseMean (by norm_num : 1 ≤ 4)
        d.slot.val.1 d.slot.val.2
        (fun _ => ((1 : ℝ) : ℂ)) (fun _ => (1 : ℂ)) 1 1 4).re =
          -(1 : ℝ) / 4 := by
  refine ⟨vacuousChiFourAttestation, ?_⟩
  exact fullFrozenPairwiseMean_four_negative

/-- A bare universal claim that every generic attestation forces a
nonnegative full mean is therefore false. -/
theorem generic_attestation_does_not_force_full_mean_nonnegative :
    ¬ ∀ (ExceptionalZeroAt : StructurallyAdmissibleActiveSlot 4 → ℝ → Prop)
        (d : ExceptionalZeroGapAttestation 4 ExceptionalZeroAt),
      0 ≤ (fullFrozenPairwiseMean (by norm_num : 1 ≤ 4)
        d.slot.val.1 d.slot.val.2
        (fun _ => ((1 : ℝ) : ℂ)) (fun _ => (1 : ℂ)) 1 1 4).re := by
  intro h
  have hnonneg := h vacuousExceptionalZeroAt vacuousChiFourAttestation
  change 0 ≤
    (fullFrozenPairwiseMean (by norm_num : 1 ≤ 4)
      fourLevel complexChiFourPrimitive
      (fun _ => ((1 : ℝ) : ℂ)) (fun _ => (1 : ℂ)) 1 1 4).re at hnonneg
  rw [fullFrozenPairwiseMean_four_negative] at hnonneg
  norm_num at hnonneg

end GoldbachCircleMethodExceptionalPredicateAdequacyGapWitnessV18361
