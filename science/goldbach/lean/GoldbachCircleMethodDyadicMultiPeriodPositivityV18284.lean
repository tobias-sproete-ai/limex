import GoldbachCircleMethodVariableWeightPeriodTilingV18283

/-!
# Goldbach V1.8.284: dyadic multi-period positivity

Every complete conductor period in one endpoint-certified dyadic interval is
positive at the admitted canonical cutoff.  Exact tiling then gives positivity
of the entire multiple-period interval.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodDyadicMultiPeriodPositivityV18284

open GoldbachCircleMethodLogCutoffPresieveBindingV18120
open GoldbachCircleMethodResidualScaleAdmissionV18196
open GoldbachCircleMethodStructurallyAdmissibleActiveSlotV18258
open GoldbachCircleMethodExceptionalZeroGapAttestationRepairV18263
open GoldbachCircleMethodVariableWeightIntervalDiscrepancyV18272
open GoldbachCircleMethodDyadicCompletePeriodCarrierPlacementV18279
open GoldbachCircleMethodVariableWeightPeriodTilingV18283

/-- Every subperiod of an endpoint-certified `k*r` interval inherits the four
single-period endpoint inequalities. -/
theorem subperiod_endpoints
    (N A r k B j : ℕ) (hj : j < k)
    (hAlo : B/2 < A) (hAhi : A+k*r ≤ B+1)
    (hClo : B/2+k*r ≤ N-A) (hChi : N-A ≤ B) :
    B/2 < A+j*r ∧
      A+j*r+r ≤ B+1 ∧
      B/2+r ≤ N-(A+j*r) ∧
      N-(A+j*r) ≤ B := by
  have hstep : j*r+r ≤ k*r := by
    have hmul := Nat.mul_le_mul_right r (Nat.succ_le_of_lt hj)
    simpa [Nat.add_mul] using hmul
  omega

/-- Positivity of the entire complete-period portion of an actual
variable-weight interval. -/
theorem attested_canonical_cutoff_multi_period_pos_of_endpoints
    (rho : ℝ) (hrho : 0 < rho) (hrhoUpper : rho ≤ (1 : ℝ)/10000)
    (B : ℕ) (hBscale : blockThreshold rho ≤ B)
    {ExceptionalZeroAt :
      StructurallyAdmissibleActiveSlot ⌊((B : ℝ)^rho)^2⌋₊ → ℝ → Prop}
    (d : ExceptionalZeroGapAttestation ⌊((B : ℝ)^rho)^2⌋₊ ExceptionalZeroAt)
    (N A k : ℕ)
    (hr3 : 3 < d.slot.val.1.val) (hEven : Even N) (hk : 0 < k)
    (hAlo : B/2 < A)
    (hAhi : A+k*d.slot.val.1.val ≤ B+1)
    (hClo : B/2+k*d.slot.val.1.val ≤ N-A)
    (hChi : N-A ≤ B) :
    0 < (variableUnitPairInterval d.slot.val.1.val N A
      (k*d.slot.val.1.val) d.slot.val.2.val d.zeroGap).re := by
  apply variableUnitPairInterval_mul_period_pos
    d.slot.val.1.val N A k d.slot.val.2.val d.zeroGap hk
  intro j hj
  obtain ⟨hAloJ, hAhiJ, hCloJ, hChiJ⟩ :=
    subperiod_endpoints N A d.slot.val.1.val k B j
      (Finset.mem_range.mp hj) hAlo hAhi hClo hChi
  exact attested_canonical_cutoff_complete_period_pos_of_endpoints
    rho hrho hrhoUpper B hBscale d N (A+j*d.slot.val.1.val)
      hr3 hEven hAloJ hAhiJ hCloJ hChiJ

end GoldbachCircleMethodDyadicMultiPeriodPositivityV18284

