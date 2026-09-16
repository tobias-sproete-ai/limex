import GoldbachCircleMethodActualQ3ZeroClassConvolutionBoundV18788
import GoldbachCircleMethodActualQ3SignedProfileVariationCorrelationV18777

/-!
# V1.8.789: final signed split of the actual q=3 correlation

The centered profile is split into the now-controlled three-power channel and
one remaining signed full-prefix/mean channel.  The exact reserve is then
rewritten as the base reserve minus these two correlations.

This is a reduction, not a proof of the sign of the remaining channel and not
a Goldbach proof.  `proof_status = NO_PROOF`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

open scoped BigOperators Classical

namespace GoldbachCircleMethodActualQ3FinalSignedChannelSplitV18789

open GoldbachCircleMethodOddChannelEventualAbsorptionV18658
open GoldbachCircleMethodFullDenominatorFourClassPartitionV18688
open GoldbachCircleMethodExactLambdaPairSourceMeanSplitV18716
open GoldbachCircleMethodActualQ3WeightedFiberPullbackV18742
open GoldbachCircleMethodActualQ3ResidueSelectorMainProfileAbsorptionV18774
open GoldbachCircleMethodActualModelQ3PreLoweringRecombinationV18769
open GoldbachCircleMethodActualModelQ3CompositeReserveFloorDecisionV18770
open GoldbachCircleMethodActualQ3SignedProfileVariationCorrelationV18777
open GoldbachCircleMethodActualQ3LocalDensityThreeClassSplitV18785

/-- The only profile channel still not controlled by the three-power bound:
the signed total odd-Lambda prefix together with the fixed project mean. -/
noncomputable def actualQ3FullPrefixMeanResidualProfile
    (M n k : Nat) : Complex :=
  -(actualQ3TotalPrefixSelectorConvolution M n k) / 2 -
    (actualLambdaPairSourceMean M : Complex) * q3ConstantPrefix n k

/-- Exact pointwise split of the centered q=3 profile. -/
theorem actualQ3CenteredProfile_eq_zeroClass_add_fullPrefixMean
    (M n k : Nat) :
    actualQ3CenteredResidueSelectorPairProfile M n k =
      (3 / 2 : Complex) * actualQ3ZeroClassSelectorConvolution M n k +
        actualQ3FullPrefixMeanResidualProfile M n k := by
  rw [actualQ3CenteredResidueSelectorPairProfile_eq_threeClassSplit]
  unfold actualQ3FullPrefixMeanResidualProfile
  ring

/-- Signed Sinc correlation carried only by the exceptional three-power
channel. -/
noncomputable def actualQ3ZeroClassSignedCorrelation
    (M : Nat) (q : PairedOddBase (oddProjectRadius M))
    (n : Nat) : Real :=
  ∑ t ∈ Finset.range M,
    actualQ3SignedSincVariation M q n t *
      (actualQ3ZeroClassSelectorConvolution M n (t + 1)).re

/-- Signed Sinc correlation of the remaining total-prefix/mean channel. -/
noncomputable def actualQ3FullPrefixMeanSignedCorrelation
    (M : Nat) (q : PairedOddBase (oddProjectRadius M))
    (n : Nat) : Real :=
  ∑ t ∈ Finset.range M,
    actualQ3SignedSincVariation M q n t *
      (actualQ3FullPrefixMeanResidualProfile M n (t + 1)).re

/-- Exact decomposition of the literal real profile correlation. -/
theorem actualQ3SignedProfileVariationCorrelation_eq_finalSplit
    (M : Nat) (q : PairedOddBase (oddProjectRadius M))
    (n : Nat) :
    actualQ3SignedProfileVariationCorrelation M q n =
      (3 / 2 : Real) * actualQ3ZeroClassSignedCorrelation M q n +
        actualQ3FullPrefixMeanSignedCorrelation M q n := by
  unfold actualQ3SignedProfileVariationCorrelation
    actualQ3ZeroClassSignedCorrelation
    actualQ3FullPrefixMeanSignedCorrelation
    actualQ3CenteredResidueSelectorRealProfile
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t _ht
  rw [actualQ3CenteredProfile_eq_zeroClass_add_fullPrefixMean]
  simp only [Complex.add_re, Complex.mul_re]
  norm_num
  ring

/-- Final exact reserve formula after the exceptional three-power channel has
been isolated.  Only the sign-sensitive full-prefix/mean correlation remains
arithmetically uncontrolled. -/
theorem actualModelQ3CompositeReserve_eq_finalSignedSplit
    (M R n : Nat) (P : Real)
    (q : PairedOddBase (oddProjectRadius M)) :
    actualModelQ3PreLoweringCompositeReserve M R n P q =
      actualQ3ResidueSelectorBaseReserve M R n P q -
        (3 / 2 : Real) * actualQ3ZeroClassSignedCorrelation M q n -
        actualQ3FullPrefixMeanSignedCorrelation M q n := by
  rw [actualModelQ3CompositeReserve_eq_base_sub_signedCorrelation]
  rw [actualQ3SignedProfileVariationCorrelation_eq_finalSplit]
  ring

end GoldbachCircleMethodActualQ3FinalSignedChannelSplitV18789
