import GoldbachCircleMethodThreeScalePrincipalChannelBoundsV18247

/-!
# Goldbach V1.8.248: centered-correction source-budget interface

This module states exactly the centered-correction smallness needed by the
three-scale forcing theorem.  If the contract is supplied, the six-channel
exception set contracts to the union of the three principal-residual sets.

The contract is a proposition and has no inhabitant in this module.  No
character-family estimate is smuggled into the kernel.
-/

open scoped Classical BigOperators

set_option autoImplicit false

namespace GoldbachCircleMethodCenteredCorrectionSourceBudgetInterfaceV18248

open GoldbachCircleMethodActualResidualLargeValueTransferV18224
open GoldbachCircleMethodActualResidualExactDecompositionV18225
open GoldbachCircleMethodResidualScaleAdmissionV18196
open GoldbachCircleMethodTwoScaleEvenBlockDefectReserveV1833
open GoldbachCircleMethodThreeScaleCenteredContractCoverV18242
open GoldbachCircleMethodThreeScaleTwoErrorForcingV18245
open GoldbachCircleMethodFourChannelExceptionDecompositionV18239
open GoldbachCircleMethodSixChannelExceptionDecompositionV18246
open GoldbachCircleMethodBoundedConductorReindexV18117

/-- Exact pointwise centered-correction budget required on the complete
target block at all three endpoint-safe source scales. -/
def ThreeScaleCenteredCorrectionSubthreshold
    (M : ℕ) (rho : ℝ) : Prop :=
  ∀ N ∈ evenTargetBlock M,
    ‖canonicalCenteredErrorCorrectionAt
        (analyticLowerSourceScale M) rho (N : ℤ)‖ < (M : ℝ) / 2048 ∧
    ‖canonicalCenteredErrorCorrectionAt
        (analyticMiddleSourceScale M) rho (N : ℤ)‖ < (M : ℝ) / 2048 ∧
    ‖canonicalCenteredErrorCorrectionAt
        (analyticUpperSourceScale M) rho (N : ℤ)‖ < (M : ℝ) / 2048

/-- Union of only the three principal-residual large-value sets. -/
noncomputable def threePrincipalBadUnion
    (M : ℕ) (rho : ℝ)
    (hLow : blockThreshold rho ≤ analyticLowerSourceScale M)
    (hMid : blockThreshold rho ≤ analyticMiddleSourceScale M)
    (hHigh : blockThreshold rho ≤ analyticUpperSourceScale M)
    (hrho : 0 < rho) (hrhoUpper : rho ≤ (1 : ℝ) / 10000) : Finset ℕ :=
  (principalBadTargets M (analyticLowerSourceScale M) rho
      (actual_scale_admission rho hrho hrhoUpper
        (analyticLowerSourceScale M) hLow).2.1 ∪
   principalBadTargets M (analyticMiddleSourceScale M) rho
      (actual_scale_admission rho hrho hrhoUpper
        (analyticMiddleSourceScale M) hMid).2.1) ∪
   principalBadTargets M (analyticUpperSourceScale M) rho
      (actual_scale_admission rho hrho hrhoUpper
        (analyticUpperSourceScale M) hHigh).2.1

/-- Supplying the centered-correction contract eliminates all three centered
branches from the V1.8.245 alternative. -/
theorem nonGoldbachTargets_subset_threePrincipalBadUnion
    {K : ℕ} [NeZero K]
    (M : ℕ) (rho : ℝ) (hM : 128 ≤ M)
    (hrho : 0 < rho) (hrhoUpper : rho ≤ (1 : ℝ) / 10000)
    (hLow : blockThreshold rho ≤ analyticLowerSourceScale M)
    (hMid : blockThreshold rho ≤ analyticMiddleSourceScale M)
    (hHigh : blockThreshold rho ≤ analyticUpperSourceScale M)
    (hKLow : ∀ q : PositiveLevel
        ⌊((analyticLowerSourceScale M : ℝ) ^ rho) ^ 2⌋₊, q.val ∣ K)
    (hKMid : ∀ q : PositiveLevel
        ⌊((analyticMiddleSourceScale M : ℝ) ^ rho) ^ 2⌋₊, q.val ∣ K)
    (hKHigh : ∀ q : PositiveLevel
        ⌊((analyticUpperSourceScale M : ℝ) ^ rho) ^ 2⌋₊, q.val ∣ K)
    (hCentered : ThreeScaleCenteredCorrectionSubthreshold M rho) :
    nonGoldbachTargets M ⊆
      threePrincipalBadUnion M rho hLow hMid hHigh hrho hrhoUpper := by
  intro N hN
  have hData := Finset.mem_filter.mp hN
  have hTarget : N ∈ evenTargetBlock M := hData.1
  have hSmall := hCentered N hTarget
  have hForce := evenTargetBlock_not_goldbach_forces_large_error_at_three_scale
    M N rho hM hTarget hrho hrhoUpper hLow hMid hHigh
      hKLow hKMid hKHigh hData.2
  rcases hForce with (hLP | hLC) | (hMP | hMC) | (hUP | hUC)
  · have hLPmem : N ∈ principalBadTargets M (analyticLowerSourceScale M) rho
        (actual_scale_admission rho hrho hrhoUpper
          (analyticLowerSourceScale M) hLow).2.1 :=
      Finset.mem_filter.mpr ⟨hTarget, hLP⟩
    exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl hLPmem)))
  · exact False.elim ((not_le_of_gt hSmall.1) hLC)
  · have hMPmem : N ∈ principalBadTargets M (analyticMiddleSourceScale M) rho
        (actual_scale_admission rho hrho hrhoUpper
          (analyticMiddleSourceScale M) hMid).2.1 :=
      Finset.mem_filter.mpr ⟨hTarget, hMP⟩
    exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr hMPmem)))
  · exact False.elim ((not_le_of_gt hSmall.2.1) hMC)
  · have hUPmem : N ∈ principalBadTargets M (analyticUpperSourceScale M) rho
        (actual_scale_admission rho hrho hrhoUpper
          (analyticUpperSourceScale M) hHigh).2.1 :=
      Finset.mem_filter.mpr ⟨hTarget, hUP⟩
    exact Finset.mem_union.mpr (Or.inr hUPmem)
  · exact False.elim ((not_le_of_gt hSmall.2.2) hUC)

/-- Finite cardinality consequence of the contracted three-channel union. -/
theorem nonGoldbachTargets_card_le_three_principal_sum
    {K : ℕ} [NeZero K]
    (M : ℕ) (rho : ℝ) (hM : 128 ≤ M)
    (hrho : 0 < rho) (hrhoUpper : rho ≤ (1 : ℝ) / 10000)
    (hLow : blockThreshold rho ≤ analyticLowerSourceScale M)
    (hMid : blockThreshold rho ≤ analyticMiddleSourceScale M)
    (hHigh : blockThreshold rho ≤ analyticUpperSourceScale M)
    (hKLow : ∀ q : PositiveLevel
        ⌊((analyticLowerSourceScale M : ℝ) ^ rho) ^ 2⌋₊, q.val ∣ K)
    (hKMid : ∀ q : PositiveLevel
        ⌊((analyticMiddleSourceScale M : ℝ) ^ rho) ^ 2⌋₊, q.val ∣ K)
    (hKHigh : ∀ q : PositiveLevel
        ⌊((analyticUpperSourceScale M : ℝ) ^ rho) ^ 2⌋₊, q.val ∣ K)
    (hCentered : ThreeScaleCenteredCorrectionSubthreshold M rho) :
    (nonGoldbachTargets M).card ≤
      (principalBadTargets M (analyticLowerSourceScale M) rho
        (actual_scale_admission rho hrho hrhoUpper
          (analyticLowerSourceScale M) hLow).2.1).card +
      (principalBadTargets M (analyticMiddleSourceScale M) rho
        (actual_scale_admission rho hrho hrhoUpper
          (analyticMiddleSourceScale M) hMid).2.1).card +
      (principalBadTargets M (analyticUpperSourceScale M) rho
        (actual_scale_admission rho hrho hrhoUpper
          (analyticUpperSourceScale M) hHigh).2.1).card := by
  have hSubset := nonGoldbachTargets_subset_threePrincipalBadUnion
    M rho hM hrho hrhoUpper hLow hMid hHigh hKLow hKMid hKHigh hCentered
  have hCard := Finset.card_le_card hSubset
  have h12 := Finset.card_union_le
    (principalBadTargets M (analyticLowerSourceScale M) rho
      (actual_scale_admission rho hrho hrhoUpper
        (analyticLowerSourceScale M) hLow).2.1)
    (principalBadTargets M (analyticMiddleSourceScale M) rho
      (actual_scale_admission rho hrho hrhoUpper
        (analyticMiddleSourceScale M) hMid).2.1)
  have h123 := Finset.card_union_le
    (principalBadTargets M (analyticLowerSourceScale M) rho
      (actual_scale_admission rho hrho hrhoUpper
        (analyticLowerSourceScale M) hLow).2.1 ∪
     principalBadTargets M (analyticMiddleSourceScale M) rho
      (actual_scale_admission rho hrho hrhoUpper
        (analyticMiddleSourceScale M) hMid).2.1)
    (principalBadTargets M (analyticUpperSourceScale M) rho
      (actual_scale_admission rho hrho hrhoUpper
        (analyticUpperSourceScale M) hHigh).2.1)
  dsimp only [threePrincipalBadUnion] at hCard
  omega

end GoldbachCircleMethodCenteredCorrectionSourceBudgetInterfaceV18248
