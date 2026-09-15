import GoldbachCircleMethodZeroGapUniformScaleAbsorptionV18276

/-!
# Goldbach V1.8.277: bounded-conductor variable-interval positivity

The local conductor inequality from V1.8.276 is discharged from the existing
proof-carrying bounded-conductor slot.  No new analytic premise is introduced
beyond one global character-level-to-block scale inequality.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodBoundedConductorVariableIntervalPositivityV18277

open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodStructurallyAdmissibleActiveSlotV18258
open GoldbachCircleMethodExceptionalZeroGapAttestationRepairV18263
open GoldbachCircleMethodVariableWeightIntervalDiscrepancyV18272
open GoldbachCircleMethodZeroGapUniformScaleAbsorptionV18276

/-- A conductor carried by `PositiveLevel Q` satisfies the V1.8.276 local
scale condition whenever the ambient level satisfies it. -/
theorem bounded_conductor_square_lt_block
    {Q B : ℕ} (r : PositiveLevel Q)
    (hQB : 48*(Q : ℝ)^2 < (B : ℝ)) :
    48*(r.val : ℝ)^2 < (B : ℝ) := by
  have hrQNat : r.val ≤ Q := (Finset.mem_Icc.mp r.property).2
  have hrQ : (r.val : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hrQNat
  have hr0 : 0 ≤ (r.val : ℝ) := by positivity
  have hQ0 : 0 ≤ (Q : ℝ) := by positivity
  have hsquare : (r.val : ℝ)^2 ≤ (Q : ℝ)^2 := by nlinarith
  nlinarith

/-- Uniform active-character positivity on one actual conductor period follows
from the single global scale premise `48*Q^2 < B`. -/
theorem attested_bounded_conductor_variable_single_period_pos
    {Q : ℕ}
    {ExceptionalZeroAt : StructurallyAdmissibleActiveSlot Q → ℝ → Prop}
    (d : ExceptionalZeroGapAttestation Q ExceptionalZeroAt)
    (N A B : ℕ)
    (hr3 : 3 < d.slot.val.1.val) (hEven : Even N)
    (hB : 4 ≤ B) (hAN : A ≤ N)
    (hend : A + d.slot.val.1.val ≤ N + 1)
    (hA : A ∈ GoldbachCircleMethodLogCutoffPresieveBindingV18120.blockCarrier B)
    (hNA : N-A ∈ GoldbachCircleMethodLogCutoffPresieveBindingV18120.blockCarrier B)
    (hleft : ∀ i ∈ Finset.range d.slot.val.1.val,
      A+i ∈ GoldbachCircleMethodLogCutoffPresieveBindingV18120.blockCarrier B)
    (hright : ∀ i ∈ Finset.range d.slot.val.1.val,
      N-(A+i) ∈ GoldbachCircleMethodLogCutoffPresieveBindingV18120.blockCarrier B)
    (hQB : 48*(Q : ℝ)^2 < (B : ℝ)) :
    0 < (variableUnitPairInterval d.slot.val.1.val N A d.slot.val.1.val
      d.slot.val.2.val d.zeroGap).re := by
  apply attested_variable_single_period_pos_of_uniform_scale d N A B
    hr3 hEven hB hAN hend hA hNA hleft hright
  exact bounded_conductor_square_lt_block d.slot.val.1 hQB

end GoldbachCircleMethodBoundedConductorVariableIntervalPositivityV18277
