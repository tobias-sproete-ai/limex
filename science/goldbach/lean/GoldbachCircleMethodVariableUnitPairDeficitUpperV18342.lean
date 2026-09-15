import GoldbachCircleMethodCanonicalAdjustedDeficitAbsorptionV18341
import GoldbachCircleMethodVariableUnitPairBracketReserveV18336

/-!
# V1.8.342: variable unit-pair deficit upper bound

This module translates the already kernel-checked pointwise unit-pair bracket
reserve into an upper bound for the exact deficit isolated in V1.8.340.  The
result contains no common-LCM boundary term: spatial variation is retained
inside the pairwise bracket sum, while the only later boundary cost remains
the `Q^4` Abel budget from V1.8.333.

The resulting bound still depends on the zero-gap reserve scale.  No uniform
positive floor for that scale, and no Goldbach conclusion, is asserted.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodVariableUnitPairDeficitUpperV18342

open GoldbachCircleMethodActualUnitPairArithmeticV18194
open GoldbachCircleMethodExceptionalWeightBoundaryV18128
open GoldbachCircleMethodExceptionalZeroGapAttestationRepairV18263
open GoldbachCircleMethodLogCutoffPresieveBindingV18120
open GoldbachCircleMethodStructurallyAdmissibleActiveSlotV18258
open GoldbachCircleMethodVariableMeanCombinedReserveV18340
open GoldbachCircleMethodVariableMeanUnitPairNormalFormV18335
open GoldbachCircleMethodVariableUnitPairBracketReserveV18336
open GoldbachCircleMethodZeroGapReserveScaleV18266

/-- Pure scalar translation from a bracket lower bound to the corresponding
deficit upper bound. -/
theorem deficit_le_of_bracket_lower
    (T count scale bracket : ℝ)
    (hLower : T * (count * scale / 6) ≤ bracket) :
    T * count - bracket ≤ T * count * (1 - scale / 6) := by
  calc
    T * count - bracket ≤ T * count - T * (count * scale / 6) :=
      sub_le_sub_left hLower (T * count)
    _ = T * count * (1 - scale / 6) := by ring

/-- The exact V1.8.340 deficit is bounded using the pointwise unit-pair
reserve already proved in V1.8.336. -/
theorem variableUnitPairDeficit_le_zeroGap_loss
    {Q : ℕ}
    {ExceptionalZeroAt : StructurallyAdmissibleActiveSlot Q → ℝ → Prop}
    (d : ExceptionalZeroGapAttestation Q ExceptionalZeroAt)
    (N A T B : ℕ)
    (hr3 : 3 < d.slot.val.1.val) (hEven : Even N) (hB : 4 ≤ B)
    (hleft : ∀ i ∈ Finset.range T, A + i ∈ blockCarrier B)
    (hright : ∀ i ∈ Finset.range T, N - (A + i) ∈ blockCarrier B) :
    variableUnitPairDeficit d.slot.val.1.val N A T d.slot.val.2.val
        d.zeroGap ≤
      (T : ℝ) * (unitPairCount d.slot.val.1.val (N : ℤ) : ℝ) *
        (1 - zeroGapReserveScale d.zeroGap B / 6) := by
  unfold variableUnitPairDeficit
  apply deficit_le_of_bracket_lower
  exact variableUnitPairBracketSum_re_lower d N A T B hr3 hEven hB hleft hright

end GoldbachCircleMethodVariableUnitPairDeficitUpperV18342
