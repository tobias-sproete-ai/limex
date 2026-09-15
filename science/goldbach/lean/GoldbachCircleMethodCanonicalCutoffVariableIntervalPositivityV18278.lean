import GoldbachCircleMethodBoundedConductorVariableIntervalPositivityV18277
import GoldbachCircleMethodQuantitativeAdmittedPrincipalReserveV18236

/-!
# Goldbach V1.8.278: canonical-cutoff variable-interval positivity

The global scale premise of V1.8.277 is discharged for the canonical character
cutoff `Q = floor((B^rho)^2)` using the already admitted eighth-power corridor.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodCanonicalCutoffVariableIntervalPositivityV18278

open GoldbachCircleMethodResidualScaleAdmissionV18196
open GoldbachCircleMethodQuantitativeAdmittedPrincipalReserveV18236
open GoldbachCircleMethodStructurallyAdmissibleActiveSlotV18258
open GoldbachCircleMethodExceptionalZeroGapAttestationRepairV18263
open GoldbachCircleMethodVariableWeightIntervalDiscrepancyV18272
open GoldbachCircleMethodBoundedConductorVariableIntervalPositivityV18277

/-- The eighth-power budget used by the principal branch is stronger than the
quadratic cutoff budget required by V1.8.277. -/
theorem canonical_cutoff_square_lt_block_of_eighth_power_budget
    (B : ℕ) (rho : ℝ)
    (hR : 1 < (B : ℝ)^rho)
    (hBudget : 256*((B : ℝ)^rho)^8 < (B : ℝ)) :
    48*(⌊((B : ℝ)^rho)^2⌋₊ : ℝ)^2 < (B : ℝ) := by
  let R : ℝ := (B : ℝ)^rho
  let Q : ℕ := ⌊R^2⌋₊
  have hR0 : 0 ≤ R := by
    dsimp only [R]
    exact Real.rpow_nonneg (Nat.cast_nonneg B) rho
  have hQ0 : 0 ≤ (Q : ℝ) := by positivity
  have hQ : (Q : ℝ) ≤ R^2 := Nat.floor_le (sq_nonneg R)
  have hQ2 : (Q : ℝ)^2 ≤ (R^2)^2 :=
    pow_le_pow_left₀ hQ0 hQ 2
  have hRR2 : R ≤ R^2 := by
    dsimp only [R] at hR ⊢
    nlinarith
  have hR4R8 : R^4 ≤ R^8 := by
    calc
      R^4 ≤ (R^2)^4 := pow_le_pow_left₀ hR0 hRR2 4
      _ = R^8 := by ring
  have hQ2R8 : (Q : ℝ)^2 ≤ R^8 := by
    calc
      (Q : ℝ)^2 ≤ (R^2)^2 := hQ2
      _ = R^4 := by ring
      _ ≤ R^8 := hR4R8
  change 48*(Q : ℝ)^2 < (B : ℝ)
  change 256*R^8 < (B : ℝ) at hBudget
  have hnonneg : 0 ≤ (Q : ℝ)^2 := sq_nonneg _
  nlinarith

/-- The canonical cutoff inequality is automatic at every scale admitted by
the existing V1.8.196 contract. -/
theorem canonical_cutoff_square_lt_block_of_admitted_scale
    (rho : ℝ) (hrho : 0 < rho) (hrhoUpper : rho ≤ (1 : ℝ)/10000)
    (B : ℕ) (hB : blockThreshold rho ≤ B) :
    48*(⌊((B : ℝ)^rho)^2⌋₊ : ℝ)^2 < (B : ℝ) := by
  apply canonical_cutoff_square_lt_block_of_eighth_power_budget B rho
  · exact one_lt_power_of_admitted rho hrho hrhoUpper B hB
  · exact admitted_scale_two_fifty_six_eighth_power_budget
      rho hrho hrhoUpper B hB

/-- At an admitted canonical cutoff, one actual complete conductor period of
the corrected active exceptional-character model is strictly positive. -/
theorem attested_canonical_cutoff_variable_single_period_pos
    (rho : ℝ) (hrho : 0 < rho) (hrhoUpper : rho ≤ (1 : ℝ)/10000)
    (B : ℕ) (hBscale : blockThreshold rho ≤ B)
    {ExceptionalZeroAt :
      StructurallyAdmissibleActiveSlot ⌊((B : ℝ)^rho)^2⌋₊ → ℝ → Prop}
    (d : ExceptionalZeroGapAttestation ⌊((B : ℝ)^rho)^2⌋₊ ExceptionalZeroAt)
    (N A : ℕ)
    (hr3 : 3 < d.slot.val.1.val) (hEven : Even N)
    (hAN : A ≤ N) (hend : A + d.slot.val.1.val ≤ N + 1)
    (hA : A ∈ GoldbachCircleMethodLogCutoffPresieveBindingV18120.blockCarrier B)
    (hNA : N-A ∈ GoldbachCircleMethodLogCutoffPresieveBindingV18120.blockCarrier B)
    (hleft : ∀ i ∈ Finset.range d.slot.val.1.val,
      A+i ∈ GoldbachCircleMethodLogCutoffPresieveBindingV18120.blockCarrier B)
    (hright : ∀ i ∈ Finset.range d.slot.val.1.val,
      N-(A+i) ∈ GoldbachCircleMethodLogCutoffPresieveBindingV18120.blockCarrier B) :
    0 < (variableUnitPairInterval d.slot.val.1.val N A d.slot.val.1.val
      d.slot.val.2.val d.zeroGap).re := by
  have hB4 : 4 ≤ B := by
    have hB6 := (actual_scale_admission rho hrho hrhoUpper B hBscale).1
    omega
  apply attested_bounded_conductor_variable_single_period_pos d N A B
    hr3 hEven hB4 hAN hend hA hNA hleft hright
  exact canonical_cutoff_square_lt_block_of_admitted_scale
    rho hrho hrhoUpper B hBscale

end GoldbachCircleMethodCanonicalCutoffVariableIntervalPositivityV18278
