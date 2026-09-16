import GoldbachCircleMethodActualQ3OddPrefixExactPsiSplitV18791

/-!
# V1.8.792: exact psi-fluctuation split of the final q=3 channel

V1.8.791 identifies the incomplete odd mass exactly.  This module transports
that identity through the literal q=3 selector convolution.  The remaining
profile is separated into three explicit pieces:

* a linear cutoff/mean profile;
* the genuine prime-number-theorem fluctuation `psi(U) - U`;
* the finite powers-of-two correction.

No sign or size estimate for the first two pieces is asserted.  In
particular, the exact decomposition is not a Goldbach proof.
`proof_status = NO_PROOF`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

open scoped BigOperators Classical ArithmeticFunction.vonMangoldt

namespace GoldbachCircleMethodActualQ3PsiFluctuationChannelSplitV18792

open GoldbachCircleMethodOddChannelEventualAbsorptionV18658
open GoldbachCircleMethodFullDenominatorFourClassPartitionV18688
open GoldbachCircleMethodOddOddFourierBesselBridgeV18668
open GoldbachCircleMethodExactLambdaPairSourceMeanSplitV18716
open GoldbachCircleMethodActualQ3WeightedFiberPullbackV18742
open GoldbachCircleMethodActualOddLambdaQ3ResidueDiscrepancyV18752
open GoldbachCircleMethodActualQ3ResidueSelectorMainProfileAbsorptionV18774
open GoldbachCircleMethodActualQ3SignedProfileVariationCorrelationV18777
open GoldbachCircleMethodActualQ3LocalDensityThreeClassSplitV18785
open GoldbachCircleMethodActualQ3FinalSignedChannelSplitV18789
open GoldbachCircleMethodActualQ3OddPrefixExactPsiSplitV18791

/-- Linear main mass at the effective prefix endpoint. -/
noncomputable def actualQ3LinearPrefixMass (M B : Nat) : Complex :=
  (actualQ3PrefixCutoff M B : Real)

/-- Exact Chebyshev fluctuation at the same endpoint. -/
noncomputable def actualQ3PsiFluctuationMass (M B : Nat) : Complex :=
  (Chebyshev.psi (actualQ3PrefixCutoff M B : Real) -
    actualQ3PrefixCutoff M B : Real)

/-- Exact powers-of-two correction removed by odd support. -/
noncomputable def actualQ3TwoPowerPrefixMass (M B : Nat) : Complex :=
  (Nat.log 2 (actualQ3PrefixCutoff M B) * Real.log 2 : Real)

theorem oddLambdaPrefixMass_eq_linear_add_psiFluctuation_sub_twoPower
    (M B : Nat) :
    oddLambdaPrefixMass M B =
      actualQ3LinearPrefixMass M B +
        actualQ3PsiFluctuationMass M B -
          actualQ3TwoPowerPrefixMass M B := by
  rw [oddLambdaPrefixMass_eq_psi_sub_twoPowers]
  unfold actualQ3LinearPrefixMass actualQ3PsiFluctuationMass
    actualQ3TwoPowerPrefixMass
  push_cast
  ring

/-- Selector convolutions of the three exact prefix channels. -/
noncomputable def actualQ3LinearPrefixSelectorConvolution
    (M n k : Nat) : Complex :=
  ∑ a ∈ oddCarrier M,
    ((ArithmeticFunction.vonMangoldt a : Complex) *
      actualQ3LinearPrefixMass M (2 * k - a)) *
        actualQ3ResidueSelector n a

noncomputable def actualQ3PsiFluctuationSelectorConvolution
    (M n k : Nat) : Complex :=
  ∑ a ∈ oddCarrier M,
    ((ArithmeticFunction.vonMangoldt a : Complex) *
      actualQ3PsiFluctuationMass M (2 * k - a)) *
        actualQ3ResidueSelector n a

noncomputable def actualQ3TwoPowerSelectorConvolution
    (M n k : Nat) : Complex :=
  ∑ a ∈ oddCarrier M,
    ((ArithmeticFunction.vonMangoldt a : Complex) *
      actualQ3TwoPowerPrefixMass M (2 * k - a)) *
        actualQ3ResidueSelector n a

/-- Exact convolution-level transport of the Chebyshev split. -/
theorem actualQ3TotalPrefixSelectorConvolution_eq_psiSplit
    (M n k : Nat) :
    actualQ3TotalPrefixSelectorConvolution M n k =
      actualQ3LinearPrefixSelectorConvolution M n k +
        actualQ3PsiFluctuationSelectorConvolution M n k -
          actualQ3TwoPowerSelectorConvolution M n k := by
  unfold actualQ3TotalPrefixSelectorConvolution
    actualQ3LinearPrefixSelectorConvolution
    actualQ3PsiFluctuationSelectorConvolution
    actualQ3TwoPowerSelectorConvolution
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a _ha
  rw [oddLambdaPrefixMass_eq_linear_add_psiFluctuation_sub_twoPower]
  ring

/-- Main linear-cutoff channel coupled to the exact project mean. -/
noncomputable def actualQ3LinearPrefixMeanResidualProfile
    (M n k : Nat) : Complex :=
  -(actualQ3LinearPrefixSelectorConvolution M n k) / 2 -
    (actualLambdaPairSourceMean M : Complex) * q3ConstantPrefix n k

/-- Exact pointwise normal form of the final residual profile. -/
theorem actualQ3FullPrefixMeanResidualProfile_eq_psiSplit
    (M n k : Nat) :
    actualQ3FullPrefixMeanResidualProfile M n k =
      actualQ3LinearPrefixMeanResidualProfile M n k -
        actualQ3PsiFluctuationSelectorConvolution M n k / 2 +
          actualQ3TwoPowerSelectorConvolution M n k / 2 := by
  unfold actualQ3FullPrefixMeanResidualProfile
    actualQ3LinearPrefixMeanResidualProfile
  rw [actualQ3TotalPrefixSelectorConvolution_eq_psiSplit]
  ring

/-- The three corresponding signed Sinc correlations. -/
noncomputable def actualQ3LinearPrefixMeanSignedCorrelation
    (M : Nat) (q : PairedOddBase (oddProjectRadius M))
    (n : Nat) : Real :=
  ∑ t ∈ Finset.range M,
    actualQ3SignedSincVariation M q n t *
      (actualQ3LinearPrefixMeanResidualProfile M n (t + 1)).re

noncomputable def actualQ3PsiFluctuationSignedCorrelation
    (M : Nat) (q : PairedOddBase (oddProjectRadius M))
    (n : Nat) : Real :=
  ∑ t ∈ Finset.range M,
    actualQ3SignedSincVariation M q n t *
      (actualQ3PsiFluctuationSelectorConvolution M n (t + 1)).re

noncomputable def actualQ3TwoPowerSignedCorrelation
    (M : Nat) (q : PairedOddBase (oddProjectRadius M))
    (n : Nat) : Real :=
  ∑ t ∈ Finset.range M,
    actualQ3SignedSincVariation M q n t *
      (actualQ3TwoPowerSelectorConvolution M n (t + 1)).re

/-- Exact correlation-level normal form. -/
theorem actualQ3FullPrefixMeanSignedCorrelation_eq_psiSplit
    (M : Nat) (q : PairedOddBase (oddProjectRadius M))
    (n : Nat) :
    actualQ3FullPrefixMeanSignedCorrelation M q n =
      actualQ3LinearPrefixMeanSignedCorrelation M q n -
        actualQ3PsiFluctuationSignedCorrelation M q n / 2 +
          actualQ3TwoPowerSignedCorrelation M q n / 2 := by
  unfold actualQ3FullPrefixMeanSignedCorrelation
    actualQ3LinearPrefixMeanSignedCorrelation
    actualQ3PsiFluctuationSignedCorrelation
    actualQ3TwoPowerSignedCorrelation
  rw [Finset.sum_div, Finset.sum_div,
    ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t _ht
  rw [actualQ3FullPrefixMeanResidualProfile_eq_psiSplit]
  simp only [Complex.add_re, Complex.sub_re, Complex.div_re]
  norm_num
  ring

end GoldbachCircleMethodActualQ3PsiFluctuationChannelSplitV18792
