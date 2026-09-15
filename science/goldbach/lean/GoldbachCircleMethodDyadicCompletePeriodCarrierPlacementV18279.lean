import GoldbachCircleMethodCanonicalCutoffVariableIntervalPositivityV18278

/-!
# Goldbach V1.8.279: dyadic complete-period carrier placement

The pointwise interval-membership premises retained by V1.8.278 are discharged
from four endpoint inequalities.  Both summand coordinates remain inside the
same literal half-open dyadic block during one complete conductor period.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodDyadicCompletePeriodCarrierPlacementV18279

open GoldbachCircleMethodLogCutoffPresieveBindingV18120
open GoldbachCircleMethodResidualScaleAdmissionV18196
open GoldbachCircleMethodStructurallyAdmissibleActiveSlotV18258
open GoldbachCircleMethodExceptionalZeroGapAttestationRepairV18263
open GoldbachCircleMethodVariableWeightIntervalDiscrepancyV18272
open GoldbachCircleMethodCanonicalCutoffVariableIntervalPositivityV18278

/-- An increasing interval stays in `(B/2,B]` when its two extremal integer
inequalities are satisfied. -/
theorem increasing_interval_mem_blockCarrier
    (A T B : ℕ) (hlo : B/2 < A) (hhi : A+T ≤ B+1) :
    ∀ i ∈ Finset.range T, A+i ∈ blockCarrier B := by
  intro i hi
  rw [mem_blockCarrier]
  have hiT : i < T := Finset.mem_range.mp hi
  omega

/-- The complementary decreasing interval stays in the same block. -/
theorem decreasing_interval_mem_blockCarrier
    (N A T B : ℕ) (hT : 0 < T)
    (hlo : B/2+T ≤ N-A) (hhi : N-A ≤ B) :
    ∀ i ∈ Finset.range T, N-(A+i) ∈ blockCarrier B := by
  intro i hi
  rw [mem_blockCarrier]
  have hiT : i < T := Finset.mem_range.mp hi
  omega

/-- Four endpoint inequalities generate every carrier and subtraction premise
needed by the variable-weight discrepancy theorem. -/
theorem complete_period_carrier_placement
    (N A r B : ℕ) (hr : 0 < r)
    (hAlo : B/2 < A) (hAhi : A+r ≤ B+1)
    (hClo : B/2+r ≤ N-A) (hChi : N-A ≤ B) :
    A ≤ N ∧ A+r ≤ N+1 ∧
      A ∈ blockCarrier B ∧ N-A ∈ blockCarrier B ∧
      (∀ i ∈ Finset.range r, A+i ∈ blockCarrier B) ∧
      (∀ i ∈ Finset.range r, N-(A+i) ∈ blockCarrier B) := by
  have hAN : A ≤ N := by omega
  have hend : A+r ≤ N+1 := by omega
  have hA : A ∈ blockCarrier B := by
    rw [mem_blockCarrier]
    omega
  have hNA : N-A ∈ blockCarrier B := by
    rw [mem_blockCarrier]
    omega
  exact ⟨hAN, hend, hA, hNA,
    increasing_interval_mem_blockCarrier A r B hAlo hAhi,
    decreasing_interval_mem_blockCarrier N A r B hr hClo hChi⟩

/-- Canonical-cutoff active positivity with the full interval carrier replaced
by four checkable endpoint inequalities. -/
theorem attested_canonical_cutoff_complete_period_pos_of_endpoints
    (rho : ℝ) (hrho : 0 < rho) (hrhoUpper : rho ≤ (1 : ℝ)/10000)
    (B : ℕ) (hBscale : blockThreshold rho ≤ B)
    {ExceptionalZeroAt :
      StructurallyAdmissibleActiveSlot ⌊((B : ℝ)^rho)^2⌋₊ → ℝ → Prop}
    (d : ExceptionalZeroGapAttestation ⌊((B : ℝ)^rho)^2⌋₊ ExceptionalZeroAt)
    (N A : ℕ)
    (hr3 : 3 < d.slot.val.1.val) (hEven : Even N)
    (hAlo : B/2 < A) (hAhi : A+d.slot.val.1.val ≤ B+1)
    (hClo : B/2+d.slot.val.1.val ≤ N-A) (hChi : N-A ≤ B) :
    0 < (variableUnitPairInterval d.slot.val.1.val N A d.slot.val.1.val
      d.slot.val.2.val d.zeroGap).re := by
  obtain ⟨hAN, hend, hA, hNA, hleft, hright⟩ :=
    complete_period_carrier_placement N A d.slot.val.1.val B
      (by omega) hAlo hAhi hClo hChi
  exact attested_canonical_cutoff_variable_single_period_pos
    rho hrho hrhoUpper B hBscale d N A hr3 hEven hAN hend hA hNA hleft hright

end GoldbachCircleMethodDyadicCompletePeriodCarrierPlacementV18279
