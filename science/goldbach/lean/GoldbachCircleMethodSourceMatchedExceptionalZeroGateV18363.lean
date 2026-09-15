import GoldbachCircleMethodPowerWeightMeanSignThresholdV18362
import GoldbachCircleMethodExceptionalPredicateAdequacyGapWitnessV18361
import Mathlib.NumberTheory.LSeries.Nonvanishing

/-!
# Goldbach V1.8.363: source-matched exceptional-zero gate

The earlier exceptional-zero interface accepted a caller-supplied predicate.
This module fixes the semantic zero equation to Mathlib's Dirichlet L-function
and leaves only the quantitative exceptional window as a proof-carrying source
parameter.  A vacuous window cannot fabricate the L-function equation.

The module also connects that source-matched attestation to V1.8.362's exact
arithmetic-mean sign threshold.  It asserts no exceptional zero and leaves the
overall proof status at `NO_PROOF`.
-/

set_option autoImplicit false
open scoped BigOperators Classical

namespace GoldbachCircleMethodSourceMatchedExceptionalZeroGateV18363

open GoldbachCircleMethodStructurallyAdmissibleActiveSlotV18258
open GoldbachCircleMethodExceptionalZeroGapAttestationRepairV18263
open GoldbachCircleMethodExceptionalPredicateAdequacyGapWitnessV18361
open GoldbachCircleMethodExceptionalWeightBoundaryV18128
open GoldbachCircleMethodPowerWeightAbelIntervalV18331
open GoldbachCircleMethodPowerWeightMeanSignThresholdV18362

/-- Source-owned quantitative membership window.  The analytic zero equation
is not part of this parameter and therefore cannot be weakened by it. -/
structure ExceptionalZeroWindowSpec where
  inWindow : ℕ → ℝ → Prop

/-- Source-matched exceptional-zero predicate: membership in the declared
window plus an actual zero of the corresponding Mathlib L-function. -/
def sourceMatchedExceptionalZeroAt (W : ExceptionalZeroWindowSpec) {Q : ℕ}
    (e : StructurallyAdmissibleActiveSlot Q) (beta : ℝ) : Prop :=
  W.inWindow e.val.1.val beta ∧
    e.val.2.val.LFunction (beta : ℂ) = 0

theorem sourceMatchedExceptionalZeroAt_exposes_LFunction_zero
    (W : ExceptionalZeroWindowSpec) {Q : ℕ}
    {e : StructurallyAdmissibleActiveSlot Q} {beta : ℝ}
    (h : sourceMatchedExceptionalZeroAt W e beta) :
    e.val.2.val.LFunction (beta : ℂ) = 0 :=
  h.2

/-- Structural admissibility and primitivity exclude the principal character. -/
theorem admissible_character_ne_one {Q : ℕ}
    (e : StructurallyAdmissibleActiveSlot Q) : e.val.2.val ≠ 1 := by
  intro hOne
  have hc1 : DirichletCharacter.conductor e.val.2.val = 1 :=
    (DirichletCharacter.eq_one_iff_conductor_eq_one).mp hOne
  have hcr : DirichletCharacter.conductor e.val.2.val = e.val.1.val :=
    e.val.2.property
  have hr1 : e.val.1.val = 1 := by omega
  exact admissible_conductor_ne_one e hr1

/-- Mathlib's nonvanishing theorem closes the endpoint `beta=1` for every
structurally admissible slot, independently of the source window. -/
theorem sourceMatchedExceptionalZeroAt_not_at_one
    (W : ExceptionalZeroWindowSpec) {Q : ℕ}
    (e : StructurallyAdmissibleActiveSlot Q) :
    ¬ sourceMatchedExceptionalZeroAt W e 1 := by
  intro h
  have hz : e.val.2.val.LFunction (1 : ℂ) = 0 := h.2
  exact (DirichletCharacter.LFunction_apply_one_ne_zero
    (admissible_character_ne_one e)) hz

/-- A source-matched chi-four attestation inherits the exact mean sign gate.
No inhabitant of that attestation is constructed here. -/
theorem sourceMatched_chiFour_attestation_mean_negative
    (W : ExceptionalZeroWindowSpec)
    (d : ExceptionalZeroGapAttestation 4
      (sourceMatchedExceptionalZeroAt W))
    (hslot : d.slot = chiFourAdmissibleSlot)
    (hweight : (7 : ℝ) / 8 < (powerWeight d.zeroGap 2) ^ 2) :
    (powerPairwiseVariableMean
      (by norm_num : 1 ≤ 4) d.slot.val.1 d.slot.val.2
      (fun _ => ((1 : ℝ) : ℂ)) (fun _ => (1 : ℂ)) d.zeroGap 4 2 1).re < 0 := by
  rw [hslot]
  exact powerPairwiseVariableMean_four_symmetric_negative d.zeroGap hweight

/-- Conversely, nonnegativity forces the explicit endpoint-weight ceiling.
This exposes the quantitative analytic obligation hidden by a bare structural
or source-matched zero predicate. -/
theorem sourceMatched_chiFour_nonnegative_forces_weight_ceiling
    (W : ExceptionalZeroWindowSpec)
    (d : ExceptionalZeroGapAttestation 4
      (sourceMatchedExceptionalZeroAt W))
    (hslot : d.slot = chiFourAdmissibleSlot)
    (hnonneg : 0 ≤
      (powerPairwiseVariableMean
        (by norm_num : 1 ≤ 4) d.slot.val.1 d.slot.val.2
        (fun _ => ((1 : ℝ) : ℂ)) (fun _ => (1 : ℂ)) d.zeroGap 4 2 1).re) :
    (powerWeight d.zeroGap 2) ^ 2 ≤ (7 : ℝ) / 8 := by
  rw [hslot] at hnonneg
  change 0 ≤
    (powerPairwiseVariableMean
      (by norm_num : 1 ≤ 4)
      GoldbachCircleMethodSignedDiagonalResidualCounterexampleV18339.fourLevel
      GoldbachCircleMethodPrimitiveChiFourFullMeanNegativeWitnessV18360.complexChiFourPrimitive
      (fun _ => ((1 : ℝ) : ℂ)) (fun _ => (1 : ℂ)) d.zeroGap 4 2 1).re at hnonneg
  rw [powerPairwiseVariableMean_four_symmetric] at hnonneg
  linarith

end GoldbachCircleMethodSourceMatchedExceptionalZeroGateV18363
