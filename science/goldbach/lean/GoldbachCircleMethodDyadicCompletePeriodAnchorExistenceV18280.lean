import GoldbachCircleMethodDyadicCompletePeriodCarrierPlacementV18279

/-!
# Goldbach V1.8.280: dyadic complete-period anchor existence

The anchor `max (B/2+1) (N-B)` is constructed inside the intersection of the
two dyadic summand carriers.  Three explicit room inequalities suffice to
place one complete conductor period in that intersection.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodDyadicCompletePeriodAnchorExistenceV18280

open GoldbachCircleMethodLogCutoffPresieveBindingV18120
open GoldbachCircleMethodResidualScaleAdmissionV18196
open GoldbachCircleMethodStructurallyAdmissibleActiveSlotV18258
open GoldbachCircleMethodExceptionalZeroGapAttestationRepairV18263
open GoldbachCircleMethodVariableWeightIntervalDiscrepancyV18272
open GoldbachCircleMethodDyadicCompletePeriodCarrierPlacementV18279

/-- The canonical left endpoint of the overlap of `(B/2,B]` and its
`N`-reflection. -/
def overlapAnchor (N B : ℕ) : ℕ := max (B/2+1) (N-B)

/-- Three finite room inequalities place one interval of length `r` inside
both dyadic coordinate carriers. -/
theorem overlapAnchor_endpoints
    (N r B : ℕ)
    (hRoom : B/2+r ≤ B)
    (hLeft : 2*(B/2)+r+1 ≤ N)
    (hRight : N+r ≤ 2*B+1) :
    B/2 < overlapAnchor N B ∧
      overlapAnchor N B+r ≤ B+1 ∧
      B/2+r ≤ N-overlapAnchor N B ∧
      N-overlapAnchor N B ≤ B := by
  dsimp [overlapAnchor]
  omega

/-- Under the canonical cutoff, the explicit overlap anchor carries a
strictly positive complete active-conductor interval. -/
theorem attested_canonical_cutoff_overlap_period_pos
    (rho : ℝ) (hrho : 0 < rho) (hrhoUpper : rho ≤ (1 : ℝ)/10000)
    (B : ℕ) (hBscale : blockThreshold rho ≤ B)
    {ExceptionalZeroAt :
      StructurallyAdmissibleActiveSlot ⌊((B : ℝ)^rho)^2⌋₊ → ℝ → Prop}
    (d : ExceptionalZeroGapAttestation ⌊((B : ℝ)^rho)^2⌋₊ ExceptionalZeroAt)
    (N : ℕ)
    (hr3 : 3 < d.slot.val.1.val) (hEven : Even N)
    (hRoom : B/2+d.slot.val.1.val ≤ B)
    (hLeft : 2*(B/2)+d.slot.val.1.val+1 ≤ N)
    (hRight : N+d.slot.val.1.val ≤ 2*B+1) :
    0 < (variableUnitPairInterval d.slot.val.1.val N (overlapAnchor N B)
      d.slot.val.1.val d.slot.val.2.val d.zeroGap).re := by
  obtain ⟨hAlo, hAhi, hClo, hChi⟩ :=
    overlapAnchor_endpoints N d.slot.val.1.val B hRoom hLeft hRight
  exact attested_canonical_cutoff_complete_period_pos_of_endpoints
    rho hrho hrhoUpper B hBscale d N (overlapAnchor N B) hr3 hEven
      hAlo hAhi hClo hChi

/-- Existential packaging of the constructed positive interval.  This is
still an active-model statement, not positivity of the full convolution. -/
theorem exists_attested_canonical_cutoff_complete_period_pos
    (rho : ℝ) (hrho : 0 < rho) (hrhoUpper : rho ≤ (1 : ℝ)/10000)
    (B : ℕ) (hBscale : blockThreshold rho ≤ B)
    {ExceptionalZeroAt :
      StructurallyAdmissibleActiveSlot ⌊((B : ℝ)^rho)^2⌋₊ → ℝ → Prop}
    (d : ExceptionalZeroGapAttestation ⌊((B : ℝ)^rho)^2⌋₊ ExceptionalZeroAt)
    (N : ℕ)
    (hr3 : 3 < d.slot.val.1.val) (hEven : Even N)
    (hRoom : B/2+d.slot.val.1.val ≤ B)
    (hLeft : 2*(B/2)+d.slot.val.1.val+1 ≤ N)
    (hRight : N+d.slot.val.1.val ≤ 2*B+1) :
    ∃ A : ℕ,
      A = overlapAnchor N B ∧
      0 < (variableUnitPairInterval d.slot.val.1.val N A
        d.slot.val.1.val d.slot.val.2.val d.zeroGap).re := by
  refine ⟨overlapAnchor N B, rfl, ?_⟩
  exact attested_canonical_cutoff_overlap_period_pos
    rho hrho hrhoUpper B hBscale d N hr3 hEven hRoom hLeft hRight

end GoldbachCircleMethodDyadicCompletePeriodAnchorExistenceV18280

