import GoldbachCircleMethodVariableMeanUnitPairNormalFormV18335
import GoldbachCircleMethodAttestedUnitPairZeroGapReserveV18271

/-!
# Goldbach V1.8.336: variable unit-pair bracket reserve

Every bracket in the V1.8.335 variable arithmetic mean inherits the existing
zero-gap unit-pair reserve pointwise.  Summing those bounds produces an exact
linear-in-interval-length reserve, with no freezing loss and no common-LCM
boundary term.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodVariableUnitPairBracketReserveV18336

open GoldbachCircleMethodActualUnitPairArithmeticV18194
open GoldbachCircleMethodActualUnitPairSignedResidualV18214
open GoldbachCircleMethodAttestedUnitPairZeroGapReserveV18271
open GoldbachCircleMethodExceptionalWeightBoundaryV18128
open GoldbachCircleMethodExceptionalZeroGapAttestationRepairV18263
open GoldbachCircleMethodLogCutoffPresieveBindingV18120
open GoldbachCircleMethodStructurallyAdmissibleActiveSlotV18258
open GoldbachCircleMethodVariableMeanUnitPairNormalFormV18335
open GoldbachCircleMethodZeroGapReserveScaleV18266

/-- A self-inverse character makes every finite unit-pair bracket real. -/
theorem unitPairBracket_im_eq_zero_of_selfInverse
    (r : ℕ) [NeZero r]
    (chi : DirichletCharacter ℂ r) (hInv : chi⁻¹ = chi)
    (m : ℤ) (t₁ t₂ : ℝ) :
    (unitPairBracket r m chi (t₁ : ℂ) (t₂ : ℂ)).im = 0 := by
  unfold unitPairBracket
  rw [Complex.im_sum]
  apply Finset.sum_eq_zero
  intro x hx
  have h₁ :=
    GoldbachCircleMethodActualUnitPairWeightedReserveV18195.self_inverse_character_im_zero
      r chi hInv x
  have h₂ :=
    GoldbachCircleMethodActualUnitPairWeightedReserveV18195.self_inverse_character_im_zero
      r chi hInv ((m : ZMod r) - x)
  simp [Complex.mul_im, h₁, h₂]

/-- The whole variable bracket sum is real. -/
theorem variableUnitPairBracketSum_im_eq_zero
    (r N A T : ℕ) [NeZero r]
    (chi : DirichletCharacter ℂ r) (hInv : chi⁻¹ = chi) (b : ℝ) :
    (variableUnitPairBracketSum r N A T chi b).im = 0 := by
  unfold variableUnitPairBracketSum
  rw [Complex.im_sum]
  apply Finset.sum_eq_zero
  intro i _hi
  exact unitPairBracket_im_eq_zero_of_selfInverse r chi hInv (N : ℤ)
    (powerWeight b (N - (A + i))) (powerWeight b (A + i))

/-- Pointwise attestation summed over all spatial indices.  Unlike the older
single-residue interval estimate, this is the exact bracket sum appearing in
the pairwise arithmetic mean. -/
theorem variableUnitPairBracketSum_re_lower
    {Q : ℕ}
    {ExceptionalZeroAt : StructurallyAdmissibleActiveSlot Q → ℝ → Prop}
    (d : ExceptionalZeroGapAttestation Q ExceptionalZeroAt)
    (N A T B : ℕ)
    (hr3 : 3 < d.slot.val.1.val) (hEven : Even N) (hB : 4 ≤ B)
    (hleft : ∀ i ∈ Finset.range T, A + i ∈ blockCarrier B)
    (hright : ∀ i ∈ Finset.range T, N - (A + i) ∈ blockCarrier B) :
    (T : ℝ) *
        ((unitPairCount d.slot.val.1.val (N : ℤ) : ℝ) *
          zeroGapReserveScale d.zeroGap B / 6) ≤
      (variableUnitPairBracketSum d.slot.val.1.val N A T
        d.slot.val.2.val d.zeroGap).re := by
  let C : ℝ :=
    (unitPairCount d.slot.val.1.val (N : ℤ) : ℝ) *
      zeroGapReserveScale d.zeroGap B / 6
  have hpoint : ∀ i ∈ Finset.range T,
      C ≤
        (unitPairBracket d.slot.val.1.val (N : ℤ) d.slot.val.2.val
          (powerWeight d.zeroGap (N - (A + i)) : ℂ)
          (powerWeight d.zeroGap (A + i) : ℂ)).re := by
    intro i hi
    have h := attested_actual_block_power_unit_pair_reserve d N B
      (N - (A + i)) (A + i) hr3 hEven hB (hright i hi) (hleft i hi)
    simpa [C, unitPairBracket, powerWeight] using h
  calc
    (T : ℝ) *
        ((unitPairCount d.slot.val.1.val (N : ℤ) : ℝ) *
          zeroGapReserveScale d.zeroGap B / 6) =
        ∑ i ∈ Finset.range T, C := by simp [C]
    _ ≤ ∑ i ∈ Finset.range T,
        (unitPairBracket d.slot.val.1.val (N : ℤ) d.slot.val.2.val
          (powerWeight d.zeroGap (N - (A + i)) : ℂ)
          (powerWeight d.zeroGap (A + i) : ℂ)).re := by
      exact Finset.sum_le_sum hpoint
    _ = (variableUnitPairBracketSum d.slot.val.1.val N A T
          d.slot.val.2.val d.zeroGap).re := by
      unfold variableUnitPairBracketSum
      simp only [Complex.re_sum]

end GoldbachCircleMethodVariableUnitPairBracketReserveV18336
