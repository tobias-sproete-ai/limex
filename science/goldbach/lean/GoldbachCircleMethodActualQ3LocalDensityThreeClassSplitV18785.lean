import GoldbachCircleMethodActualQ3SincVariationEnergyBoundV18784
import GoldbachCircleMethodActualQ3SincAbelWeightedPairCorrelationDecisionV18773

/-!
# V1.8.785: exact q=3 local-density three-class split

The arithmetic profile left by V1.8.784 still mixes two qualitatively
different objects: the exceptional zero residue class modulo three and the
complete odd-von-Mangoldt prefix.  This module separates them by the exact
finite identity

`mass₀ - (mass₁ + mass₂) / 2 = (3 * mass₀ - total) / 2`.

The identity is transported through the unchanged outer q=3 selector.  Thus
the weighted pair profile is now an explicit difference of a zero-class
convolution and a total-prefix convolution.  No estimate, positivity claim,
prime number theorem, or Goldbach conclusion is inserted.
`proof_status = NO_PROOF`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

open scoped BigOperators Classical ArithmeticFunction.vonMangoldt

namespace GoldbachCircleMethodActualQ3LocalDensityThreeClassSplitV18785

open GoldbachCircleMethodOddChannelEventualAbsorptionV18658
open GoldbachCircleMethodFullDenominatorFourClassPartitionV18688
open GoldbachCircleMethodOddOddSignedFiberAdapterV18665
open GoldbachCircleMethodOddOddFourierBesselBridgeV18668
open GoldbachCircleMethodExactLambdaPairSourceMeanSplitV18716
open GoldbachCircleMethodActualLambdaPairSourceMeanV710AdapterV18717
open GoldbachCircleMethodActualOddLambdaQ3ResidueDiscrepancyV18752
open GoldbachCircleMethodActualQ3PrefixLocalDensityExtractionV18753
open GoldbachCircleMethodActualQ3WeightedFiberPullbackV18742
open GoldbachCircleMethodActualQ3WeightedPairConvolutionTransferV18772
open GoldbachCircleMethodActualQ3SincAbelWeightedPairCorrelationDecisionV18773
open GoldbachCircleMethodActualQ3ResidueSelectorMainProfileAbsorptionV18774

/-- Exact three-class algebra at every literal odd-Lambda prefix. -/
theorem oddLambdaQ3_zero_sub_unitMean_eq_three_zero_sub_total_div_two
    (M B : Nat) :
    oddLambdaQ3ResidueMass M B (0 : ZMod 3) -
        oddLambdaQ3UnitMean M B =
      (3 * oddLambdaQ3ResidueMass M B (0 : ZMod 3) -
        oddLambdaPrefixMass M B) / 2 := by
  have hsum := sum_oddLambdaQ3ResidueMass_eq_total M B
  have huniv : (Finset.univ : Finset (ZMod 3)) = {0, 1, 2} := by decide
  rw [huniv] at hsum
  have h01 : (0 : ZMod 3) ∉ ({1, 2} : Finset (ZMod 3)) := by decide
  have h12 : (1 : ZMod 3) ∉ ({2} : Finset (ZMod 3)) := by decide
  rw [Finset.sum_insert h01, Finset.sum_insert h12,
    Finset.sum_singleton] at hsum
  unfold oddLambdaQ3UnitMean
  rw [← hsum]
  ring

/-- Outer-selector convolution of the exceptional zero residue class. -/
noncomputable def actualQ3ZeroClassSelectorConvolution
    (M n k : Nat) : Complex :=
  ∑ a ∈ oddCarrier M,
    ((ArithmeticFunction.vonMangoldt a : Complex) *
      oddLambdaQ3ResidueMass M (2 * k - a) (0 : ZMod 3)) *
        actualQ3ResidueSelector n a

/-- Outer-selector convolution of the complete odd-Lambda prefix. -/
noncomputable def actualQ3TotalPrefixSelectorConvolution
    (M n k : Nat) : Complex :=
  ∑ a ∈ oddCarrier M,
    ((ArithmeticFunction.vonMangoldt a : Complex) *
      oddLambdaPrefixMass M (2 * k - a)) *
        actualQ3ResidueSelector n a

/-- The actual weighted local-density profile is exactly half of three times
the zero-class channel minus the total-prefix channel. -/
theorem actualQ3WeightedPairLocalDensityConvolution_eq_three_zero_sub_total_div_two
    (M n k : Nat) :
    actualQ3WeightedPairLocalDensityConvolution M n k =
      (3 * actualQ3ZeroClassSelectorConvolution M n k -
        actualQ3TotalPrefixSelectorConvolution M n k) / 2 := by
  rw [actualQ3WeightedPairLocalDensityConvolution_eq_residueSelector]
  unfold actualQ3ZeroClassSelectorConvolution
    actualQ3TotalPrefixSelectorConvolution
    actualQ3ResidueSelector
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro a _ha
  rw [oddLambdaQ3_zero_sub_unitMean_eq_three_zero_sub_total_div_two]
  split <;> ring

/-- Exact centered profile after the three-class split.  This is the
arithmetic object whose signed Sinc correlation remains to be controlled. -/
theorem actualQ3CenteredResidueSelectorPairProfile_eq_threeClassSplit
    (M n k : Nat) :
    actualQ3CenteredResidueSelectorPairProfile M n k =
      (3 * actualQ3ZeroClassSelectorConvolution M n k -
        actualQ3TotalPrefixSelectorConvolution M n k) / 2 -
      (actualLambdaPairSourceMean M : Complex) * q3ConstantPrefix n k := by
  rw [← weightedPairConvolution_sub_mean_eq_centeredResidueSelectorProfile]
  rw [actualQ3WeightedPairLocalDensityConvolution_eq_three_zero_sub_total_div_two]

end GoldbachCircleMethodActualQ3LocalDensityThreeClassSplitV18785
