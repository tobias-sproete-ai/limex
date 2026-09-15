import GoldbachCircleMethodThreeScaleTwoErrorForcingV18245

/-!
# Goldbach V1.8.246: six-channel exception decomposition

The endpoint-safe three-scale forcing theorem is converted into a finite
six-set exception decomposition.  Principal and centered channels stay
separate at every scale.
-/

open scoped Classical

set_option autoImplicit false

namespace GoldbachCircleMethodSixChannelExceptionDecompositionV18246

open GoldbachCircleMethodResidualScaleAdmissionV18196
open GoldbachCircleMethodActualResidualLargeValueTransferV18224
open GoldbachCircleMethodTwoScaleEvenBlockDefectReserveV1833
open GoldbachCircleMethodFourChannelExceptionDecompositionV18239
open GoldbachCircleMethodThreeScaleCenteredContractCoverV18242
open GoldbachCircleMethodThreeScaleTwoErrorForcingV18245
open GoldbachCircleMethodFiniteResiduePrefixV1866
open GoldbachCircleMethodBoundedConductorReindexV18117

/-- Explicit union of all six endpoint-safe error channels. -/
noncomputable def sixChannelBadUnion
    (M : ℕ) (rho : ℝ)
    (hR2Low : 2 ≤ (analyticLowerSourceScale M : ℝ)^rho)
    (hR2Middle : 2 ≤ (analyticMiddleSourceScale M : ℝ)^rho)
    (hR2Upper : 2 ≤ (analyticUpperSourceScale M : ℝ)^rho) : Finset ℕ :=
  ((((principalBadTargets M (analyticLowerSourceScale M) rho hR2Low ∪
        correctionBadTargets M (analyticLowerSourceScale M) rho) ∪
      principalBadTargets M (analyticMiddleSourceScale M) rho hR2Middle) ∪
    correctionBadTargets M (analyticMiddleSourceScale M) rho) ∪
    principalBadTargets M (analyticUpperSourceScale M) rho hR2Upper) ∪
  correctionBadTargets M (analyticUpperSourceScale M) rho

/-- Every hypothetical non-Goldbach target belongs to the explicit union of
six large-value sets. -/
theorem nonGoldbachTargets_subset_sixChannelBadUnion
    {K : ℕ} [NeZero K]
    (M : ℕ) (rho : ℝ) (hM : 128 ≤ M)
    (hrho : 0 < rho) (hrhoUpper : rho ≤ (1 : ℝ) / 10000)
    (hLow : blockThreshold rho ≤ analyticLowerSourceScale M)
    (hMiddle : blockThreshold rho ≤ analyticMiddleSourceScale M)
    (hUpper : blockThreshold rho ≤ analyticUpperSourceScale M)
    (hKLow : ∀ q : PositiveLevel
        ⌊((analyticLowerSourceScale M : ℝ) ^ rho) ^ 2⌋₊, q.val ∣ K)
    (hKMiddle : ∀ q : PositiveLevel
        ⌊((analyticMiddleSourceScale M : ℝ) ^ rho) ^ 2⌋₊, q.val ∣ K)
    (hKUpper : ∀ q : PositiveLevel
        ⌊((analyticUpperSourceScale M : ℝ) ^ rho) ^ 2⌋₊, q.val ∣ K) :
    nonGoldbachTargets M ⊆
      sixChannelBadUnion M rho
        (actual_scale_admission rho hrho hrhoUpper
          (analyticLowerSourceScale M) hLow).2.1
        (actual_scale_admission rho hrho hrhoUpper
          (analyticMiddleSourceScale M) hMiddle).2.1
        (actual_scale_admission rho hrho hrhoUpper
          (analyticUpperSourceScale M) hUpper).2.1 := by
  intro N hN
  have hData := (mem_nonGoldbachTargets_iff M N).mp hN
  have hForce :=
    evenTargetBlock_not_goldbach_forces_large_error_at_three_scale
      (K := K) M N rho hM hData.1 hrho hrhoUpper
      hLow hMiddle hUpper hKLow hKMiddle hKUpper hData.2
  simp only [sixChannelBadUnion, Finset.mem_union, ScaleErrorLarge] at hForce ⊢
  rcases hForce with (hLP | hLC) | (hMP | hMC) | (hUP | hUC)
  · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl
      (Finset.mem_filter.mpr ⟨hData.1, hLP⟩)))))
  · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr
      (Finset.mem_filter.mpr ⟨hData.1, hLC⟩)))))
  · exact Or.inl (Or.inl (Or.inl (Or.inr
      (Finset.mem_filter.mpr ⟨hData.1, hMP⟩))))
  · exact Or.inl (Or.inl (Or.inr
      (Finset.mem_filter.mpr ⟨hData.1, hMC⟩)))
  · exact Or.inl (Or.inr
      (Finset.mem_filter.mpr ⟨hData.1, hUP⟩))
  · exact Or.inr
      (Finset.mem_filter.mpr ⟨hData.1, hUC⟩)

/-- Cardinality bound retaining all six component counts. -/
theorem nonGoldbachTargets_card_le_six_channel_sum
    {K : ℕ} [NeZero K]
    (M : ℕ) (rho : ℝ) (hM : 128 ≤ M)
    (hrho : 0 < rho) (hrhoUpper : rho ≤ (1 : ℝ) / 10000)
    (hLow : blockThreshold rho ≤ analyticLowerSourceScale M)
    (hMiddle : blockThreshold rho ≤ analyticMiddleSourceScale M)
    (hUpper : blockThreshold rho ≤ analyticUpperSourceScale M)
    (hKLow : ∀ q : PositiveLevel
        ⌊((analyticLowerSourceScale M : ℝ) ^ rho) ^ 2⌋₊, q.val ∣ K)
    (hKMiddle : ∀ q : PositiveLevel
        ⌊((analyticMiddleSourceScale M : ℝ) ^ rho) ^ 2⌋₊, q.val ∣ K)
    (hKUpper : ∀ q : PositiveLevel
        ⌊((analyticUpperSourceScale M : ℝ) ^ rho) ^ 2⌋₊, q.val ∣ K) :
    (nonGoldbachTargets M).card ≤
      (principalBadTargets M (analyticLowerSourceScale M) rho
        (actual_scale_admission rho hrho hrhoUpper
          (analyticLowerSourceScale M) hLow).2.1).card +
      (correctionBadTargets M (analyticLowerSourceScale M) rho).card +
      (principalBadTargets M (analyticMiddleSourceScale M) rho
        (actual_scale_admission rho hrho hrhoUpper
          (analyticMiddleSourceScale M) hMiddle).2.1).card +
      (correctionBadTargets M (analyticMiddleSourceScale M) rho).card +
      (principalBadTargets M (analyticUpperSourceScale M) rho
        (actual_scale_admission rho hrho hrhoUpper
          (analyticUpperSourceScale M) hUpper).2.1).card +
      (correctionBadTargets M (analyticUpperSourceScale M) rho).card := by
  let LP := principalBadTargets M (analyticLowerSourceScale M) rho
    (actual_scale_admission rho hrho hrhoUpper
      (analyticLowerSourceScale M) hLow).2.1
  let LC := correctionBadTargets M (analyticLowerSourceScale M) rho
  let MP := principalBadTargets M (analyticMiddleSourceScale M) rho
    (actual_scale_admission rho hrho hrhoUpper
      (analyticMiddleSourceScale M) hMiddle).2.1
  let MC := correctionBadTargets M (analyticMiddleSourceScale M) rho
  let UP := principalBadTargets M (analyticUpperSourceScale M) rho
    (actual_scale_admission rho hrho hrhoUpper
      (analyticUpperSourceScale M) hUpper).2.1
  let UC := correctionBadTargets M (analyticUpperSourceScale M) rho
  have hSubset := nonGoldbachTargets_subset_sixChannelBadUnion
    (K := K) M rho hM hrho hrhoUpper hLow hMiddle hUpper
    hKLow hKMiddle hKUpper
  have h0 : (nonGoldbachTargets M).card ≤
      (((((LP ∪ LC) ∪ MP) ∪ MC) ∪ UP) ∪ UC).card := by
    apply Finset.card_le_card
    simpa [sixChannelBadUnion, LP, LC, MP, MC, UP, UC] using hSubset
  have h1 := Finset.card_union_le LP LC
  have h2 := Finset.card_union_le (LP ∪ LC) MP
  have h3 := Finset.card_union_le ((LP ∪ LC) ∪ MP) MC
  have h4 := Finset.card_union_le (((LP ∪ LC) ∪ MP) ∪ MC) UP
  have h5 := Finset.card_union_le ((((LP ∪ LC) ∪ MP) ∪ MC) ∪ UP) UC
  dsimp [LP, LC, MP, MC, UP, UC] at h0 h1 h2 h3 h4 h5 ⊢
  omega

end GoldbachCircleMethodSixChannelExceptionDecompositionV18246

