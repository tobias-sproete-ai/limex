import GoldbachCircleMethodAdjustedModelReserveInterfaceV18286

/-!
# Goldbach V1.8.287: normalized-to-amplitude transfer obstruction

This constructive countermodel prevents a positivity theorem for the
normalized unit-pair kernel from being promoted uniformly to the
amplitude-aware adjusted model.  The companion weight is part of the model,
and a zero companion weight annihilates the latter while leaving the former
unchanged.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodNormalizedToAmplitudeTransferObstructionV18287

open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodFiniteCompanionBindingV18118
open GoldbachCircleMethodActiveExceptionalCenteringV18129
open GoldbachCircleMethodActualUnitPairArithmeticV18194
open GoldbachCircleMethodVariableWeightIntervalDiscrepancyV18272
open GoldbachCircleMethodSupportedAdjustedModelBindingAuditV18285

/-- A zero external companion weight annihilates every finite companion. -/
theorem finiteCompanion_zero_weight {Q : ℕ} (r : PositiveLevel Q) (N : ℕ) :
    finiteCompanion r N (fun _ => 0) = 0 := by
  unfold finiteCompanion
  simp

/-- Consequently the complete amplitude-aware point factor is zero. -/
theorem amplitudeAdjustedFactor_zero_weight {Q : ℕ} (hQ : 1 ≤ Q)
    (r : PositiveLevel Q)
    (chi : {χ : DirichletCharacter ℂ r.val // χ.IsPrimitive})
    (N : ℕ) (b : ℝ) :
    amplitudeAdjustedFactor hQ r chi N b (fun _ => 0) = 0 := by
  unfold amplitudeAdjustedFactor activeRadialAmplitude
  rw [finiteCompanion_zero_weight, finiteCompanion_zero_weight]
  ring

/-- The entire amplitude-aware pair sum then vanishes on every carrier. -/
theorem amplitudeAdjustedFullPairSum_zero_weight {Q : ℕ} (hQ : 1 ≤ Q)
    (J : Finset ℕ) (e : CharacterSlot Q) (N : ℕ) (b : ℝ) :
    amplitudeAdjustedFullPairSum hQ J e N b (fun _ => 0) = 0 := by
  unfold amplitudeAdjustedFullPairSum amplitudeAdjustedPairKernel
  simp_rw [amplitudeAdjustedFactor_zero_weight]
  simp

/-- Concrete non-implication: even when a normalized unit-pair interval is
strictly positive, no theorem can transfer that positivity uniformly over all
companion weights to the amplitude-aware full pair sum. -/
theorem no_weight_uniform_normalized_to_amplitude_transfer
    {Q : ℕ} (hQ : 1 ≤ Q) (J : Finset ℕ) (e : CharacterSlot Q)
    (N A T : ℕ) (b : ℝ)
    (hNormalized :
      0 < (variableUnitPairInterval e.1.val N A T e.2.val b).re) :
    ¬ (∀ w : ℕ → ℂ,
      0 < (variableUnitPairInterval e.1.val N A T e.2.val b).re →
        0 < (amplitudeAdjustedFullPairSum hQ J e N b w).re) := by
  intro hAll
  have hZeroPos := hAll (fun _ => 0) hNormalized
  rw [amplitudeAdjustedFullPairSum_zero_weight] at hZeroPos
  norm_num at hZeroPos

/-- Witness-bearing version of the same obstruction. -/
theorem exists_zero_amplitude_countermodel
    {Q : ℕ} (hQ : 1 ≤ Q) (J : Finset ℕ) (e : CharacterSlot Q)
    (N A T : ℕ) (b : ℝ)
    (hNormalized :
      0 < (variableUnitPairInterval e.1.val N A T e.2.val b).re) :
    ∃ w : ℕ → ℂ,
      0 < (variableUnitPairInterval e.1.val N A T e.2.val b).re ∧
      amplitudeAdjustedFullPairSum hQ J e N b w = 0 := by
  refine ⟨fun _ => 0, hNormalized, ?_⟩
  exact amplitudeAdjustedFullPairSum_zero_weight hQ J e N b

end GoldbachCircleMethodNormalizedToAmplitudeTransferObstructionV18287
