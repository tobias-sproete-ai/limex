import GoldbachCircleMethodDyadicCompletePeriodAnchorExistenceV18280
import GoldbachCircleMethodActualBlockInteriorPairReserveV18231

/-!
# Goldbach V1.8.281: interior reserve to complete-period positivity

The pre-existing `HasInteriorPairReserve` target geometry is connected to the
new actual variable-weight complete-period result.  The remaining half-block
room condition is discharged from the canonical admitted cutoff budget.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodInteriorReserveCompletePeriodPositivityV18281

open GoldbachCircleMethodResidualScaleAdmissionV18196
open GoldbachCircleMethodActualBlockInteriorPairReserveV18231
open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodBoundedConductorVariableIntervalPositivityV18277
open GoldbachCircleMethodCanonicalCutoffVariableIntervalPositivityV18278
open GoldbachCircleMethodStructurallyAdmissibleActiveSlotV18258
open GoldbachCircleMethodExceptionalZeroGapAttestationRepairV18263
open GoldbachCircleMethodVariableWeightIntervalDiscrepancyV18272
open GoldbachCircleMethodDyadicCompletePeriodAnchorExistenceV18280

/-- The global quadratic level budget leaves room for every carried conductor
inside one half-block. -/
theorem half_block_room_of_level_square_budget
    {Q B : ℕ} (r : PositiveLevel Q)
    (hQB : 48*(Q : ℝ)^2 < (B : ℝ)) :
    B/2+r.val ≤ B := by
  have hrBudget : 48*(r.val : ℝ)^2 < (B : ℝ) :=
    bounded_conductor_square_lt_block r hQB
  have hrOne : (1 : ℝ) ≤ r.val := by
    exact_mod_cast (Finset.mem_Icc.mp r.property).1
  have hTwoR : (2 : ℝ)*(r.val : ℝ) < (B : ℝ) := by
    nlinarith [sq_nonneg ((r.val : ℝ)-1)]
  have hTwoRNat : 2*r.val ≤ B := by
    exact_mod_cast hTwoR.le
  omega

/-- An admitted canonical cutoff automatically gives half-block room to its
proof-carrying active conductor. -/
theorem attested_canonical_cutoff_half_block_room
    (rho : ℝ) (hrho : 0 < rho) (hrhoUpper : rho ≤ (1 : ℝ)/10000)
    (B : ℕ) (hBscale : blockThreshold rho ≤ B)
    {ExceptionalZeroAt :
      StructurallyAdmissibleActiveSlot ⌊((B : ℝ)^rho)^2⌋₊ → ℝ → Prop}
    (d : ExceptionalZeroGapAttestation ⌊((B : ℝ)^rho)^2⌋₊ ExceptionalZeroAt) :
    B/2+d.slot.val.1.val ≤ B := by
  apply half_block_room_of_level_square_budget d.slot.val.1
  exact canonical_cutoff_square_lt_block_of_admitted_scale
    rho hrho hrhoUpper B hBscale

/-- The established interior-reserve predicate with reserve equal to the
active conductor now yields positivity of one explicit complete period. -/
theorem attested_canonical_cutoff_interior_period_pos
    (rho : ℝ) (hrho : 0 < rho) (hrhoUpper : rho ≤ (1 : ℝ)/10000)
    (B : ℕ) (hBscale : blockThreshold rho ≤ B)
    {ExceptionalZeroAt :
      StructurallyAdmissibleActiveSlot ⌊((B : ℝ)^rho)^2⌋₊ → ℝ → Prop}
    (d : ExceptionalZeroGapAttestation ⌊((B : ℝ)^rho)^2⌋₊ ExceptionalZeroAt)
    (N : ℕ)
    (hr3 : 3 < d.slot.val.1.val) (hEven : Even N)
    (hInterior : HasInteriorPairReserve B N d.slot.val.1.val) :
    0 < (variableUnitPairInterval d.slot.val.1.val N (overlapAnchor N B)
      d.slot.val.1.val d.slot.val.2.val d.zeroGap).re := by
  have hRoom := attested_canonical_cutoff_half_block_room
    rho hrho hrhoUpper B hBscale d
  rcases hInterior with ⟨hLeft, hRight⟩
  apply attested_canonical_cutoff_overlap_period_pos
    rho hrho hrhoUpper B hBscale d N hr3 hEven hRoom
  · omega
  · exact hRight

end GoldbachCircleMethodInteriorReserveCompletePeriodPositivityV18281

