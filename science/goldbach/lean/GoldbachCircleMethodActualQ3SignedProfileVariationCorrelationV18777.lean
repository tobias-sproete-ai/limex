import GoldbachCircleMethodActualQ3CanonicalProfileAbsorptionGapEventualSignV18776

/-!
# V1.8.777: real signed q=3 profile-variation correlation

The exact Abel remainder from V1.8.774 is reduced from a complex expression
to a real signed correlation.  Every factor is proved real on the literal
finite source: the project Sinc variation, the q=3 constant prefix, and the
centered residue-selector profile.

This removes the remaining complex-phase ambiguity.  It does not prove the
eventual sign of the signed correlation, nor construct an unbounded negative
sequence for the literal actual-source reserve.  The global status remains
`proof_status = NO_PROOF`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

open scoped BigOperators Classical ArithmeticFunction.vonMangoldt

namespace GoldbachCircleMethodActualQ3SignedProfileVariationCorrelationV18777

open GoldbachCircleMethodOddChannelEventualAbsorptionV18658
open GoldbachCircleMethodFullDenominatorFourClassPartitionV18688
open GoldbachCircleMethodOddOddFourierBesselBridgeV18668
open GoldbachCircleMethodActualCenteredQ3ResidueObstructionV18730
open GoldbachCircleMethodExactLambdaPairSourceMeanSplitV18716
open GoldbachCircleMethodActualLambdaPairSourceMeanV710AdapterV18717
open GoldbachCircleMethodActualOddLambdaQ3ResidueDiscrepancyV18752
open GoldbachCircleMethodActualQ3PrefixLocalDensityExtractionV18753
open GoldbachCircleMethodActualQ3WeightedFiberPullbackV18742
open GoldbachCircleMethodActualQ3ResidueSelectorMainProfileAbsorptionV18774
open GoldbachCircleMethodActualModelQ3PreLoweringRecombinationV18769
open GoldbachCircleMethodActualModelQ3CompositeReserveFloorDecisionV18770
open GoldbachCircleMethodActualQ3CanonicalProfileCeilingReserveDominanceDecisionV18775
open GoldbachCircleMethodActualQ3CanonicalProfileAbsorptionGapEventualSignV18776

/-- The literal project Sinc variation is real. -/
theorem selectedPairSourceCoordinateSincVariation_im_eq_zero
    (M : Nat) (q : PairedOddBase (oddProjectRadius M)) (n t : Nat) :
    (selectedPairSourceCoordinateSincVariation M q n t).im = 0 := by
  simp [selectedPairSourceCoordinateSincVariation,
    selectedPairSourceCoordinateSincWeight]

/-- The denominator-three transform of the constant sequence is real. -/
theorem q3ConstantPrefix_im_eq_zero (n k : Nat) :
    (q3ConstantPrefix n k).im = 0 := by
  change Complex.imCLM (q3ConstantPrefix n k) = 0
  unfold q3ConstantPrefix q3EvenStepTransform
  simp_rw [unitCharacterSum_three_eq_if_zero]
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro i hi
  split <;> norm_num

/-- Every literal q=3 residue mass is real. -/
theorem oddLambdaQ3ResidueMass_im_eq_zero
    (M B : Nat) (r : ZMod 3) :
    (oddLambdaQ3ResidueMass M B r).im = 0 := by
  change Complex.imCLM (oddLambdaQ3ResidueMass M B r) = 0
  unfold oddLambdaQ3ResidueMass
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro i hi
  split <;> norm_num

/-- The exact unit-class mean is real. -/
theorem oddLambdaQ3UnitMean_im_eq_zero (M B : Nat) :
    (oddLambdaQ3UnitMean M B).im = 0 := by
  simp [oddLambdaQ3UnitMean, Complex.add_im,
    oddLambdaQ3ResidueMass_im_eq_zero]

/-- The target-residue pair profile has no imaginary component. -/
theorem actualQ3TargetResiduePairProfile_im_eq_zero (M n k : Nat) :
    (actualQ3TargetResiduePairProfile M n k).im = 0 := by
  change Complex.imCLM (actualQ3TargetResiduePairProfile M n k) = 0
  unfold actualQ3TargetResiduePairProfile
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro a ha
  unfold actualQ3TargetResidueIndicator
  by_cases h : ((((a : Int) - 2 * (n : Int) : Int) : ZMod 3)) = 0
  · rw [if_pos h]
    simp [Complex.mul_im, Complex.sub_im,
      oddLambdaQ3ResidueMass_im_eq_zero,
      oddLambdaQ3UnitMean_im_eq_zero]
  · rw [if_neg h]
    simp

/-- The unselected total pair profile has no imaginary component. -/
theorem actualQ3TotalPairProfile_im_eq_zero (M k : Nat) :
    (actualQ3TotalPairProfile M k).im = 0 := by
  change Complex.imCLM (actualQ3TotalPairProfile M k) = 0
  unfold actualQ3TotalPairProfile
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro a ha
  simp [Complex.mul_im, Complex.sub_im,
    oddLambdaQ3ResidueMass_im_eq_zero,
    oddLambdaQ3UnitMean_im_eq_zero]

/-- The exact centered selector profile is pointwise real. -/
theorem actualQ3CenteredResidueSelectorPairProfile_im_eq_zero
    (M n k : Nat) :
    (actualQ3CenteredResidueSelectorPairProfile M n k).im = 0 := by
  simp [actualQ3CenteredResidueSelectorPairProfile,
    Complex.sub_im, Complex.mul_im,
    actualQ3TargetResiduePairProfile_im_eq_zero,
    actualQ3TotalPairProfile_im_eq_zero,
    q3ConstantPrefix_im_eq_zero]

/-- Real coordinate of the exact project Sinc variation. -/
noncomputable def actualQ3SignedSincVariation
    (M : Nat) (q : PairedOddBase (oddProjectRadius M))
    (n t : Nat) : Real :=
  (selectedPairSourceCoordinateSincVariation M q n t).re

/-- Real coordinate of the exact centered q=3 residue-selector profile. -/
noncomputable def actualQ3CenteredResidueSelectorRealProfile
    (M n k : Nat) : Real :=
  (actualQ3CenteredResidueSelectorPairProfile M n k).re

/-- Exact signed real correlation discarded by the norm-majorant route. -/
noncomputable def actualQ3SignedProfileVariationCorrelation
    (M : Nat) (q : PairedOddBase (oddProjectRadius M))
    (n : Nat) : Real :=
  ∑ t ∈ Finset.range M,
    actualQ3SignedSincVariation M q n t *
      actualQ3CenteredResidueSelectorRealProfile M n (t + 1)

/-- The real part of the literal Abel remainder is exactly the negative of
the signed real profile-variation correlation. -/
theorem actualQ3LocalDensityTriangularRemainder_re_eq_neg_signedCorrelation
    (M : Nat) (q : PairedOddBase (oddProjectRadius M)) (n : Nat) :
    (actualQ3LocalDensityTriangularRemainder M q n).re =
      -actualQ3SignedProfileVariationCorrelation M q n := by
  have h :=
    actualQ3LocalDensityTriangularRemainder_eq_centeredProfileAbel M q n
  have hre := congrArg (fun z : Complex => Complex.reCLM z) h
  unfold actualQ3SignedProfileVariationCorrelation
    actualQ3SignedSincVariation actualQ3CenteredResidueSelectorRealProfile
  simpa only [map_neg, map_sum, Complex.reCLM_apply, Complex.mul_re,
    selectedPairSourceCoordinateSincVariation_im_eq_zero,
    actualQ3CenteredResidueSelectorPairProfile_im_eq_zero,
    zero_mul, sub_zero] using hre

/-- Exact reserve identity with the sign-sensitive correlation retained. -/
theorem actualModelQ3CompositeReserve_eq_base_sub_signedCorrelation
    (M R n : Nat) (P : Real)
    (q : PairedOddBase (oddProjectRadius M)) :
    actualModelQ3PreLoweringCompositeReserve M R n P q =
      actualQ3ResidueSelectorBaseReserve M R n P q -
        actualQ3SignedProfileVariationCorrelation M q n := by
  rw [actualModelQ3PreLoweringCompositeReserve_eq_literal_source,
    actualQ3LocalDensityTriangularRemainder_re_eq_neg_signedCorrelation]
  unfold actualQ3ResidueSelectorBaseReserve
  ring

/-- The exact signed loss never exceeds the canonical norm debit on the
admissible target block.  This is a comparison, not an eventual sign proof. -/
theorem actualQ3SignedProfileVariationCorrelation_le_canonicalDebit
    {M n : Nat} (hM : 0 < M)
    (q : PairedOddBase (oddProjectRadius M)) (hn : n ≤ M) :
    actualQ3SignedProfileVariationCorrelation M q n ≤
      actualQ3CanonicalCenteredProfileDebit M n q := by
  have hSlack :=
    actualQ3CanonicalProfileAbsorptionSlack_nonneg hM q hn
  unfold actualQ3CanonicalProfileAbsorptionSlack at hSlack
  rw [actualQ3LocalDensityTriangularRemainder_re_eq_neg_signedCorrelation]
    at hSlack
  linarith

end GoldbachCircleMethodActualQ3SignedProfileVariationCorrelationV18777
