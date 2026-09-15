import GoldbachCircleMethodInteriorReserveCompletePeriodPositivityV18281
import GoldbachCircleMethodTwoSourceScaleCoverV18232

/-!
# Goldbach V1.8.282: two-source-scale active-period cover

Every even target in the historical dyadic block is connected to one positive
actual variable-weight complete active-conductor period at one of the two
source scales.  The result remains conditional on proof-carrying active-zero
attestations at both canonical cutoffs.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodTwoSourceScaleActivePeriodCoverV18282

open GoldbachCircleMethodTwoScaleEvenBlockDefectReserveV1833
open GoldbachCircleMethodTwoSourceScaleCoverV18232
open GoldbachCircleMethodActualBlockInteriorPairReserveV18231
open GoldbachCircleMethodResidualScaleAdmissionV18196
open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodBoundedConductorVariableIntervalPositivityV18277
open GoldbachCircleMethodCanonicalCutoffVariableIntervalPositivityV18278
open GoldbachCircleMethodStructurallyAdmissibleActiveSlotV18258
open GoldbachCircleMethodExceptionalZeroGapAttestationRepairV18263
open GoldbachCircleMethodVariableWeightIntervalDiscrepancyV18272
open GoldbachCircleMethodDyadicCompletePeriodAnchorExistenceV18280
open GoldbachCircleMethodInteriorReserveCompletePeriodPositivityV18281

/-- Interior reserve is monotone downward in the requested reserve length. -/
theorem HasInteriorPairReserve.anti
    {B N s t : ℕ} (hst : s ≤ t) (h : HasInteriorPairReserve B N t) :
    HasInteriorPairReserve B N s := by
  unfold HasInteriorPairReserve at h ⊢
  omega

/-- The canonical conductor fits inside the one-eighth linear reserve already
used by the two-source-scale carrier cover. -/
theorem attested_conductor_le_linearPairReserve
    (rho : ℝ) (hrho : 0 < rho) (hrhoUpper : rho ≤ (1 : ℝ)/10000)
    (B : ℕ) (hBscale : blockThreshold rho ≤ B)
    {ExceptionalZeroAt :
      StructurallyAdmissibleActiveSlot ⌊((B : ℝ)^rho)^2⌋₊ → ℝ → Prop}
    (d : ExceptionalZeroGapAttestation ⌊((B : ℝ)^rho)^2⌋₊ ExceptionalZeroAt) :
    d.slot.val.1.val ≤ linearPairReserve B := by
  have hBudget : 48*(d.slot.val.1.val : ℝ)^2 < (B : ℝ) := by
    apply bounded_conductor_square_lt_block d.slot.val.1
    exact canonical_cutoff_square_lt_block_of_admitted_scale
      rho hrho hrhoUpper B hBscale
  have hrOne : (1 : ℝ) ≤ d.slot.val.1.val := by
    exact_mod_cast (Finset.mem_Icc.mp d.slot.val.1.property).1
  have hEight : (8 : ℝ)*(d.slot.val.1.val : ℝ) < (B : ℝ) := by
    nlinarith [sq_nonneg ((d.slot.val.1.val : ℝ)-1)]
  have hEightNat : 8*d.slot.val.1.val ≤ B := by
    exact_mod_cast hEight.le
  unfold linearPairReserve
  omega

/-- Every even target in the dyadic target block has a positive complete
active-conductor period at one of the two canonical source scales. -/
theorem evenTargetBlock_two_source_scale_active_period_positive
    (M N : ℕ) (rho : ℝ) (hM : 19 ≤ M)
    (hN : N ∈ evenTargetBlock M)
    (hrho : 0 < rho) (hrhoUpper : rho ≤ (1 : ℝ)/10000)
    (hLow : blockThreshold rho ≤ lowerSourceScale M)
    (hHigh : blockThreshold rho ≤ upperSourceScale M)
    {ExceptionalZeroAtLow :
      StructurallyAdmissibleActiveSlot
        ⌊((lowerSourceScale M : ℝ)^rho)^2⌋₊ → ℝ → Prop}
    {ExceptionalZeroAtHigh :
      StructurallyAdmissibleActiveSlot
        ⌊((upperSourceScale M : ℝ)^rho)^2⌋₊ → ℝ → Prop}
    (dLow : ExceptionalZeroGapAttestation
      ⌊((lowerSourceScale M : ℝ)^rho)^2⌋₊ ExceptionalZeroAtLow)
    (dHigh : ExceptionalZeroGapAttestation
      ⌊((upperSourceScale M : ℝ)^rho)^2⌋₊ ExceptionalZeroAtHigh)
    (hr3Low : 3 < dLow.slot.val.1.val)
    (hr3High : 3 < dHigh.slot.val.1.val) :
    0 < (variableUnitPairInterval dLow.slot.val.1.val N
        (overlapAnchor N (lowerSourceScale M)) dLow.slot.val.1.val
        dLow.slot.val.2.val dLow.zeroGap).re ∨
      0 < (variableUnitPairInterval dHigh.slot.val.1.val N
        (overlapAnchor N (upperSourceScale M)) dHigh.slot.val.1.val
        dHigh.slot.val.2.val dHigh.zeroGap).re := by
  have hEven : Even N := ((mem_evenTargetBlock_iff M N).mp hN).2.2.1
  rcases evenTargetBlock_two_source_scale_cover M N hM hN with hCover | hCover
  · left
    have hrReserve := attested_conductor_le_linearPairReserve
      rho hrho hrhoUpper (lowerSourceScale M) hLow dLow
    have hInterior : HasInteriorPairReserve (lowerSourceScale M) N
        dLow.slot.val.1.val :=
      HasInteriorPairReserve.anti hrReserve hCover.2
    exact attested_canonical_cutoff_interior_period_pos
      rho hrho hrhoUpper (lowerSourceScale M) hLow dLow N hr3Low hEven hInterior
  · right
    have hrReserve := attested_conductor_le_linearPairReserve
      rho hrho hrhoUpper (upperSourceScale M) hHigh dHigh
    have hInterior : HasInteriorPairReserve (upperSourceScale M) N
        dHigh.slot.val.1.val :=
      HasInteriorPairReserve.anti hrReserve hCover.2
    exact attested_canonical_cutoff_interior_period_pos
      rho hrho hrhoUpper (upperSourceScale M) hHigh dHigh N hr3High hEven hInterior

end GoldbachCircleMethodTwoSourceScaleActivePeriodCoverV18282
