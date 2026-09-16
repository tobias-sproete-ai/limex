import GoldbachCircleMethodActualQ3PsiFluctuationChannelSplitV18792

/-!
# V1.8.793: discharged powers-of-two correction and reduced final q=3 gate

The powers-of-two channel exposed by V1.8.792 is bounded by the same literal
Sinc-variation argument that discharged the powers-of-three channel.  Both
prime-power corrections are therefore explicit.  The remaining gate is one
combined signed correlation containing only the linear cutoff/mean profile
and the genuine Chebyshev fluctuation.

No inhabitant for that final gate is supplied.  `proof_status = NO_PROOF`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

open scoped BigOperators Classical ArithmeticFunction.vonMangoldt

namespace GoldbachCircleMethodActualQ3TwoPowerCorrectionFinalGateV18793

open GoldbachCircleMethodOddChannelEventualAbsorptionV18658
open GoldbachCircleMethodFullDenominatorFourClassPartitionV18688
open GoldbachCircleMethodSharpSourceSincVariationV18721
open GoldbachCircleMethodOddOddFourierBesselBridgeV18668
open GoldbachCircleMethodActualLambdaPairSourceMeanChebyshevBoundV18719
open GoldbachCircleMethodActualLambdaPairSourceMeanV710AdapterV18717
open GoldbachCircleMethodActualQ3SplitPrefixBudgetV18735
open GoldbachCircleMethodActualQ3ResidueSelectorMainProfileAbsorptionV18774
open GoldbachCircleMethodActualQ3SignedProfileVariationCorrelationV18777
open GoldbachCircleMethodActualModelQ3PreLoweringRecombinationV18769
open GoldbachCircleMethodActualQ3ZeroClassConvolutionBoundV18788
open GoldbachCircleMethodActualQ3ThreePowerDebitFinalGateV18790
open GoldbachCircleMethodActualQ3OddPrefixExactPsiSplitV18791
open GoldbachCircleMethodActualQ3PsiFluctuationChannelSplitV18792
open GoldbachCircleMethodChebyshevEnergyBudgetV1889

theorem norm_actualQ3TwoPowerPrefixMass_le_ambient_log
    (M B : Nat) :
    ‖actualQ3TwoPowerPrefixMass M B‖ ≤
      Nat.log 2 M * Real.log 2 := by
  unfold actualQ3TwoPowerPrefixMass
  have hnonneg : 0 ≤
      (Nat.log 2 (actualQ3PrefixCutoff M B) : Real) * Real.log 2 :=
    mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by norm_num))
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnonneg]
  have hcountNat :
      Nat.log 2 (actualQ3PrefixCutoff M B) ≤ Nat.log 2 M := by
    apply Nat.log_mono_right
    unfold actualQ3PrefixCutoff
    exact min_le_left _ _
  have hcount :
      (Nat.log 2 (actualQ3PrefixCutoff M B) : Real) ≤ Nat.log 2 M := by
    exact_mod_cast hcountNat
  exact mul_le_mul_of_nonneg_right hcount
    (Real.log_nonneg (by norm_num))

theorem norm_actualQ3TwoPowerSelectorConvolution_le_oddLambdaSum_log
    (M n k : Nat) :
    ‖actualQ3TwoPowerSelectorConvolution M n k‖ ≤
      2 * oddLambdaSum M * (Nat.log 2 M * Real.log 2) := by
  unfold actualQ3TwoPowerSelectorConvolution
  calc
    ‖∑ a ∈ oddCarrier M,
        ((ArithmeticFunction.vonMangoldt a : Complex) *
          actualQ3TwoPowerPrefixMass M (2 * k - a)) *
          actualQ3ResidueSelector n a‖ ≤
      ∑ a ∈ oddCarrier M,
        ‖((ArithmeticFunction.vonMangoldt a : Complex) *
          actualQ3TwoPowerPrefixMass M (2 * k - a)) *
          actualQ3ResidueSelector n a‖ := norm_sum_le _ _
    _ ≤ ∑ a ∈ oddCarrier M,
        ArithmeticFunction.vonMangoldt a *
          (Nat.log 2 M * Real.log 2) * 2 := by
      apply Finset.sum_le_sum
      intro a _ha
      rw [norm_mul, norm_mul]
      have hLam : ‖(ArithmeticFunction.vonMangoldt a : Complex)‖ =
          ArithmeticFunction.vonMangoldt a := by
        rw [Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
      rw [hLam]
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left
          (norm_actualQ3TwoPowerPrefixMass_le_ambient_log
            M (2 * k - a))
          ArithmeticFunction.vonMangoldt_nonneg)
        (norm_actualQ3ResidueSelector_le_two n a)
        (norm_nonneg _)
        (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
          (mul_nonneg (Nat.cast_nonneg _)
            (Real.log_nonneg (by norm_num))))
    _ = 2 * oddLambdaSum M * (Nat.log 2 M * Real.log 2) := by
      unfold oddLambdaSum
      rw [← Finset.sum_mul, ← Finset.sum_mul]
      ring

theorem norm_actualQ3TwoPowerSelectorConvolution_le_chebyshev
    (M n k : Nat) :
    ‖actualQ3TwoPowerSelectorConvolution M n k‖ ≤
      2 * chebyshevConstant * M * (Nat.log 2 M * Real.log 2) := by
  have hsum := oddLambdaSum_le_chebyshev_linear M
  have hfactor : 0 ≤ Nat.log 2 M * Real.log 2 :=
    mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by norm_num))
  calc
    ‖actualQ3TwoPowerSelectorConvolution M n k‖ ≤
        2 * oddLambdaSum M * (Nat.log 2 M * Real.log 2) :=
      norm_actualQ3TwoPowerSelectorConvolution_le_oddLambdaSum_log M n k
    _ ≤ 2 * (chebyshevConstant * M) *
        (Nat.log 2 M * Real.log 2) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hsum (by norm_num)) hfactor
    _ = 2 * chebyshevConstant * M *
        (Nat.log 2 M * Real.log 2) := by ring

noncomputable def actualQ3TwoPowerProfileCeiling (M : Nat) : Real :=
  2 * chebyshevConstant * M * (Nat.log 2 M * Real.log 2)

noncomputable def actualQ3TwoPowerCorrelationDebit
    (M : Nat) (q : PairedOddBase (oddProjectRadius M)) : Real :=
  actualQ3VariationScale M q * actualQ3TwoPowerProfileCeiling M

theorem actualQ3TwoPowerProfileCeiling_nonneg (M : Nat) :
    0 ≤ actualQ3TwoPowerProfileCeiling M := by
  unfold actualQ3TwoPowerProfileCeiling
  have hC : 0 ≤ chebyshevConstant := chebyshevConstant_pos.le
  positivity

theorem abs_actualQ3TwoPowerSignedCorrelation_le
    {M n : Nat} (hM : 0 < M)
    (q : PairedOddBase (oddProjectRadius M))
    (hn : n ≤ M) :
    |actualQ3TwoPowerSignedCorrelation M q n| ≤
      actualQ3TwoPowerCorrelationDebit M q := by
  have hVar :=
    sum_selectedPairSourceCoordinateSincVariation_norm_le_harmonic
      M hM q n hn
  have hCeiling := actualQ3TwoPowerProfileCeiling_nonneg M
  unfold actualQ3TwoPowerSignedCorrelation
    actualQ3TwoPowerCorrelationDebit
  calc
    |∑ t ∈ Finset.range M,
        actualQ3SignedSincVariation M q n t *
          (actualQ3TwoPowerSelectorConvolution M n (t + 1)).re| ≤
      ∑ t ∈ Finset.range M,
        |actualQ3SignedSincVariation M q n t *
          (actualQ3TwoPowerSelectorConvolution M n (t + 1)).re| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ t ∈ Finset.range M,
        ‖selectedPairSourceCoordinateSincVariation M q n t‖ *
          actualQ3TwoPowerProfileCeiling M := by
      apply Finset.sum_le_sum
      intro t _ht
      rw [abs_mul]
      have hw : |actualQ3SignedSincVariation M q n t| ≤
          ‖selectedPairSourceCoordinateSincVariation M q n t‖ := by
        unfold actualQ3SignedSincVariation
        exact Complex.abs_re_le_norm _
      have hzRe :
          |(actualQ3TwoPowerSelectorConvolution M n (t + 1)).re| ≤
            ‖actualQ3TwoPowerSelectorConvolution M n (t + 1)‖ :=
        Complex.abs_re_le_norm _
      have hzNorm :
          ‖actualQ3TwoPowerSelectorConvolution M n (t + 1)‖ ≤
            actualQ3TwoPowerProfileCeiling M := by
        unfold actualQ3TwoPowerProfileCeiling
        exact norm_actualQ3TwoPowerSelectorConvolution_le_chebyshev
          M n (t + 1)
      exact mul_le_mul hw (hzRe.trans hzNorm)
        (abs_nonneg _) (norm_nonneg _)
    _ = (∑ t ∈ Finset.range M,
        ‖selectedPairSourceCoordinateSincVariation M q n t‖) *
          actualQ3TwoPowerProfileCeiling M := by
      rw [Finset.sum_mul]
    _ ≤ actualQ3VariationScale M q *
          actualQ3TwoPowerProfileCeiling M := by
      exact mul_le_mul_of_nonneg_right hVar hCeiling

/-- The one remaining signed arithmetic channel after both prime-power
corrections are discharged. -/
noncomputable def actualQ3PNTResidualSignedCorrelation
    (M : Nat) (q : PairedOddBase (oddProjectRadius M))
    (n : Nat) : Real :=
  actualQ3LinearPrefixMeanSignedCorrelation M q n -
    actualQ3PsiFluctuationSignedCorrelation M q n / 2

theorem finalPNTResidualLowerBound_le_actualCompositeReserve
    {M R n : Nat} {P : Real}
    (hM : 0 < M)
    (q : PairedOddBase (oddProjectRadius M))
    (hn : n ≤ M) :
    actualQ3ResidueSelectorBaseReserve M R n P q -
        (3 / 2 : Real) * actualQ3ThreePowerCorrelationDebit M q -
        actualQ3PNTResidualSignedCorrelation M q n -
        actualQ3TwoPowerCorrelationDebit M q / 2 ≤
      actualModelQ3PreLoweringCompositeReserve M R n P q := by
  have hTwoAbs := abs_actualQ3TwoPowerSignedCorrelation_le hM q hn
  have hTwoUpper : actualQ3TwoPowerSignedCorrelation M q n ≤
      actualQ3TwoPowerCorrelationDebit M q :=
    (le_abs_self _).trans hTwoAbs
  have hBase := finalSignedLowerBound_le_actualCompositeReserve
    (M := M) (R := R) (n := n) (P := P) hM q hn
  rw [actualQ3FullPrefixMeanSignedCorrelation_eq_psiSplit] at hBase
  unfold actualQ3PNTResidualSignedCorrelation
  linarith

theorem actualModelQ3CompositeReserve_pos_of_pntResidualGate
    {M R n : Nat} {P : Real}
    (hM : 0 < M)
    (q : PairedOddBase (oddProjectRadius M))
    (hn : n ≤ M)
    (hGate :
      (3 / 2 : Real) * actualQ3ThreePowerCorrelationDebit M q +
          actualQ3PNTResidualSignedCorrelation M q n +
          actualQ3TwoPowerCorrelationDebit M q / 2 <
        actualQ3ResidueSelectorBaseReserve M R n P q) :
    0 < actualModelQ3PreLoweringCompositeReserve M R n P q := by
  have hLower := finalPNTResidualLowerBound_le_actualCompositeReserve
    (M := M) (R := R) (n := n) (P := P) hM q hn
  linarith

end GoldbachCircleMethodActualQ3TwoPowerCorrectionFinalGateV18793
