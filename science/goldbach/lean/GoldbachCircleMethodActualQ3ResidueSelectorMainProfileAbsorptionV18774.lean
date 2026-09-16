import GoldbachCircleMethodActualQ3SincAbelWeightedPairCorrelationDecisionV18773

/-!
# V1.8.774: actual q=3 residue-selector main profile and Sinc absorption

The exact `2`/`-1` selector from V1.8.773 is decomposed as three times the
target-residue indicator minus the total profile.  This produces a literal
target-residue main profile on the unchanged odd-von-Mangoldt carrier.

The module then transports a uniform ceiling for the centered profile through
the already proved sharp total variation of the project Sinc weight.  The
result is a source-bound lower estimate for the complete V1.8.770 composite
reserve.

The profile ceiling and the required base-reserve dominance are not proved
for the actual source.  No unbounded actual negative sequence is constructed.
The requested gate therefore remains fail-closed and
`proof_status = NO_PROOF`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

open scoped BigOperators Classical ArithmeticFunction.vonMangoldt

namespace GoldbachCircleMethodActualQ3ResidueSelectorMainProfileAbsorptionV18774

open GoldbachCircleMethodTwoScaleEvenBlockDefectReserveV1833
open GoldbachCircleMethodDiscreteArcModelReserveV1855
open GoldbachCircleMethodOddChannelEventualAbsorptionV18658
open GoldbachCircleMethodFullDenominatorFourClassPartitionV18688
open GoldbachCircleMethodOddOddFourierBesselBridgeV18668
open GoldbachCircleMethodExactLambdaPairSourceMeanSplitV18716
open GoldbachCircleMethodActualLambdaPairSourceMeanV710AdapterV18717
open GoldbachCircleMethodSharpSourceSincVariationV18721
open GoldbachCircleMethodActualOddLambdaQ3ResidueDiscrepancyV18752
open GoldbachCircleMethodActualQ3PrefixLocalDensityExtractionV18753
open GoldbachCircleMethodActualQ3WeightedFiberPullbackV18742
open GoldbachCircleMethodActualQ3SplitPrefixBudgetV18735
open GoldbachCircleMethodActualQ3PairResidueSignedTriangularGateV18748
open GoldbachCircleMethodActualModelQ3PreLoweringRecombinationV18769
open GoldbachCircleMethodActualModelQ3CompositeReserveFloorDecisionV18770
open GoldbachCircleMethodActualQ3WeightedPairConvolutionTransferV18772
open GoldbachCircleMethodActualQ3SincAbelWeightedPairCorrelationDecisionV18773

/-- Indicator of the target residue selected by the q=3 Ramanujan phase. -/
def actualQ3TargetResidueIndicator (n a : Nat) : Complex :=
  if ((((a : Int) - 2 * (n : Int) : Int) : ZMod 3)) = 0
  then 1 else 0

/-- Real-valued q=3 selector in the exact V1.8.773 sign convention. -/
def actualQ3ResidueSelector (n a : Nat) : Complex :=
  if ((((a : Int) - 2 * (n : Int) : Int) : ZMod 3)) = 0
  then 2 else -1

/-- The selector is exactly `3 * targetIndicator - 1`. -/
theorem actualQ3ResidueSelector_eq_three_mul_indicator_sub_one
    (n a : Nat) :
    actualQ3ResidueSelector n a =
      3 * actualQ3TargetResidueIndicator n a - 1 := by
  unfold actualQ3ResidueSelector actualQ3TargetResidueIndicator
  by_cases h : ((((a : Int) - 2 * (n : Int) : Int) : ZMod 3)) = 0
  · rw [if_pos h, if_pos h]
    norm_num
  · rw [if_neg h, if_neg h]
    norm_num

/-- Target-residue component of the literal local-density pair profile. -/
noncomputable def actualQ3TargetResiduePairProfile
    (M n k : Nat) : Complex :=
  ∑ a ∈ oddCarrier M,
    ((ArithmeticFunction.vonMangoldt a : Complex) *
      (oddLambdaQ3ResidueMass M (2 * k - a) (0 : ZMod 3) -
        oddLambdaQ3UnitMean M (2 * k - a))) *
      actualQ3TargetResidueIndicator n a

/-- Total component of the same profile before the q=3 selector is applied. -/
noncomputable def actualQ3TotalPairProfile
    (M k : Nat) : Complex :=
  ∑ a ∈ oddCarrier M,
    (ArithmeticFunction.vonMangoldt a : Complex) *
      (oddLambdaQ3ResidueMass M (2 * k - a) (0 : ZMod 3) -
        oddLambdaQ3UnitMean M (2 * k - a))

/-- Exact main-profile extraction: the actual weighted convolution is three
times its target-residue profile minus its total profile. -/
theorem actualQ3WeightedPairLocalDensityConvolution_eq_three_target_sub_total
    (M n k : Nat) :
    actualQ3WeightedPairLocalDensityConvolution M n k =
      3 * actualQ3TargetResiduePairProfile M n k -
        actualQ3TotalPairProfile M k := by
  rw [actualQ3WeightedPairLocalDensityConvolution_eq_residueSelector]
  unfold actualQ3TargetResiduePairProfile actualQ3TotalPairProfile
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a _ha
  change
    ((ArithmeticFunction.vonMangoldt a : Complex) *
      (oddLambdaQ3ResidueMass M (2 * k - a) (0 : ZMod 3) -
        oddLambdaQ3UnitMean M (2 * k - a))) *
        actualQ3ResidueSelector n a = _
  rw [actualQ3ResidueSelector_eq_three_mul_indicator_sub_one]
  ring

/-- Profile remaining inside the Sinc variation after the exact project mean
channel has been removed. -/
noncomputable def actualQ3CenteredResidueSelectorPairProfile
    (M n k : Nat) : Complex :=
  3 * actualQ3TargetResiduePairProfile M n k -
    actualQ3TotalPairProfile M k -
    (actualLambdaPairSourceMean M : Complex) * q3ConstantPrefix n k

theorem weightedPairConvolution_sub_mean_eq_centeredResidueSelectorProfile
    (M n k : Nat) :
    actualQ3WeightedPairLocalDensityConvolution M n k -
        (actualLambdaPairSourceMean M : Complex) * q3ConstantPrefix n k =
      actualQ3CenteredResidueSelectorPairProfile M n k := by
  rw [actualQ3WeightedPairLocalDensityConvolution_eq_three_target_sub_total]
  rfl

/-- Exact Abel representation after the target/total main-profile split. -/
theorem actualQ3LocalDensityTriangularRemainder_eq_centeredProfileAbel
    (M : Nat) (q : PairedOddBase (oddProjectRadius M)) (n : Nat) :
    actualQ3LocalDensityTriangularRemainder M q n =
      -∑ t ∈ Finset.range M,
        selectedPairSourceCoordinateSincVariation M q n t *
          actualQ3CenteredResidueSelectorPairProfile M n (t + 1) := by
  rw [actualQ3LocalDensityTriangularRemainder_eq_weightedPairConvolutionAbel]
  simp_rw [weightedPairConvolution_sub_mean_eq_centeredResidueSelectorProfile]

/-- Actual-source ceiling required to turn the exact main-profile split into
a quantitative Sinc-variation estimate.  No inhabitant is supplied here. -/
def ActualQ3CenteredResidueSelectorProfileCeiling
    (M n : Nat) (D : Real) : Prop :=
  0 ≤ D ∧ ∀ k : Nat, k ≤ M →
    ‖actualQ3CenteredResidueSelectorPairProfile M n k‖ ≤ D

/-- Sharp conditional absorption through the already proved project Sinc
variation.  The only open input is the actual centered-profile ceiling. -/
theorem actualQ3LocalDensityTriangularRemainder_norm_le_of_profileCeiling
    {M n : Nat} {D : Real}
    (hM : 0 < M)
    (q : PairedOddBase (oddProjectRadius M))
    (hn : n ≤ M)
    (hProfile : ActualQ3CenteredResidueSelectorProfileCeiling M n D) :
    ‖actualQ3LocalDensityTriangularRemainder M q n‖ ≤
      actualQ3VariationScale M q * D := by
  rw [actualQ3LocalDensityTriangularRemainder_eq_centeredProfileAbel]
  rw [norm_neg]
  have hVar := sum_selectedPairSourceCoordinateSincVariation_norm_le_harmonic
    M hM q n hn
  calc
    ‖∑ t ∈ Finset.range M,
        selectedPairSourceCoordinateSincVariation M q n t *
          actualQ3CenteredResidueSelectorPairProfile M n (t + 1)‖ ≤
        ∑ t ∈ Finset.range M,
          ‖selectedPairSourceCoordinateSincVariation M q n t *
            actualQ3CenteredResidueSelectorPairProfile M n (t + 1)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ t ∈ Finset.range M,
          ‖selectedPairSourceCoordinateSincVariation M q n t‖ * D := by
      apply Finset.sum_le_sum
      intro t ht
      rw [norm_mul]
      apply mul_le_mul_of_nonneg_left
      · exact hProfile.2 (t + 1) (by
          have ht' := Finset.mem_range.mp ht
          omega)
      · exact norm_nonneg _
    _ = (∑ t ∈ Finset.range M,
          ‖selectedPairSourceCoordinateSincVariation M q n t‖) * D := by
      rw [Finset.sum_mul]
    _ ≤ actualQ3VariationScale M q * D := by
      exact mul_le_mul_of_nonneg_right hVar hProfile.1

/-- The exact base retained before paying the Sinc-variation debit. -/
noncomputable def actualQ3ResidueSelectorBaseReserve
    (M R n : Nat) (P : Real)
    (q : PairedOddBase (oddProjectRadius M)) : Real :=
  discreteArcMainModel M (2 * n) R P +
    (3 * selectedPairSourceCoordinateSincWeight M q n M *
      actualQ3PairResidueDefect M n).re

/-- Conditional lower bound for the complete actual composite reserve. -/
theorem baseReserve_sub_profileDebit_le_actualCompositeReserve
    {M R n : Nat} {P D : Real}
    (hM : 0 < M)
    (q : PairedOddBase (oddProjectRadius M))
    (hn : n ≤ M)
    (hProfile : ActualQ3CenteredResidueSelectorProfileCeiling M n D) :
    actualQ3ResidueSelectorBaseReserve M R n P q -
        actualQ3VariationScale M q * D ≤
      actualModelQ3PreLoweringCompositeReserve M R n P q := by
  have hRemainder :=
    actualQ3LocalDensityTriangularRemainder_norm_le_of_profileCeiling
      hM q hn hProfile
  have hAbsRe :
      |(actualQ3LocalDensityTriangularRemainder M q n).re| ≤
        ‖actualQ3LocalDensityTriangularRemainder M q n‖ :=
    Complex.abs_re_le_norm _
  have hLower :
      -(actualQ3VariationScale M q * D) ≤
        (actualQ3LocalDensityTriangularRemainder M q n).re := by
    have hNegAbs :
        -|(actualQ3LocalDensityTriangularRemainder M q n).re| ≤
          (actualQ3LocalDensityTriangularRemainder M q n).re :=
      neg_abs_le _
    linarith
  rw [actualModelQ3PreLoweringCompositeReserve_eq_literal_source]
  unfold actualQ3ResidueSelectorBaseReserve
  linarith

/-- If the literal base reserve dominates the rigorously transported profile
debit plus a requested floor, the complete actual composite has that floor. -/
theorem requestedFloor_le_actualCompositeReserve_of_profileAbsorption
    {M R n : Nat} {P D floor : Real}
    (hM : 0 < M)
    (q : PairedOddBase (oddProjectRadius M))
    (hn : n ≤ M)
    (hProfile : ActualQ3CenteredResidueSelectorProfileCeiling M n D)
    (hAbsorb : floor + actualQ3VariationScale M q * D ≤
      actualQ3ResidueSelectorBaseReserve M R n P q) :
    floor ≤ actualModelQ3PreLoweringCompositeReserve M R n P q := by
  have hLower := baseReserve_sub_profileDebit_le_actualCompositeReserve
    (R := R) (P := P) hM q hn hProfile
  linarith

end GoldbachCircleMethodActualQ3ResidueSelectorMainProfileAbsorptionV18774
