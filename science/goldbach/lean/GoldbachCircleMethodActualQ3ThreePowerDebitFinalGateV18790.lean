import GoldbachCircleMethodActualQ3FinalSignedChannelSplitV18789

/-!
# V1.8.790: discharged three-power debit and final q=3 gate

The exceptional three-power correlation from V1.8.789 is bounded using the
sharp project Sinc variation and the explicit Chebyshev/logarithmic ceiling
proved in V1.8.788.  This leaves one and only one q=3 arithmetic obligation:
an upper bound for the signed full-prefix/mean correlation on the literal
source.

The module supplies the exact conditional positivity theorem but no inhabitant
for that final arithmetic inequality.  `proof_status = NO_PROOF`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

open scoped BigOperators Classical

namespace GoldbachCircleMethodActualQ3ThreePowerDebitFinalGateV18790

open GoldbachCircleMethodOddChannelEventualAbsorptionV18658
open GoldbachCircleMethodFullDenominatorFourClassPartitionV18688
open GoldbachCircleMethodSharpSourceSincVariationV18721
open GoldbachCircleMethodActualLambdaPairSourceMeanV710AdapterV18717
open GoldbachCircleMethodActualQ3SplitPrefixBudgetV18735
open GoldbachCircleMethodActualQ3SignedProfileVariationCorrelationV18777
open GoldbachCircleMethodActualQ3LocalDensityThreeClassSplitV18785
open GoldbachCircleMethodActualQ3ZeroClassConvolutionBoundV18788
open GoldbachCircleMethodActualQ3FinalSignedChannelSplitV18789
open GoldbachCircleMethodActualModelQ3PreLoweringRecombinationV18769
open GoldbachCircleMethodActualQ3ResidueSelectorMainProfileAbsorptionV18774
open GoldbachCircleMethodChebyshevEnergyBudgetV1889

/-- Explicit uniform bound for the zero-class selector profile. -/
noncomputable def actualQ3ThreePowerProfileCeiling (M : Nat) : Real :=
  2 * chebyshevConstant * M * (Nat.log 3 M * Real.log 3)

/-- The corresponding signed-correlation debit after the sharp project Sinc
variation has been applied. -/
noncomputable def actualQ3ThreePowerCorrelationDebit
    (M : Nat) (q : PairedOddBase (oddProjectRadius M)) : Real :=
  actualQ3VariationScale M q * actualQ3ThreePowerProfileCeiling M

theorem actualQ3ThreePowerProfileCeiling_nonneg (M : Nat) :
    0 ≤ actualQ3ThreePowerProfileCeiling M := by
  unfold actualQ3ThreePowerProfileCeiling
  have hC : 0 ≤ chebyshevConstant := chebyshevConstant_pos.le
  positivity

/-- Absolute ceiling for the complete signed three-power correlation. -/
theorem abs_actualQ3ZeroClassSignedCorrelation_le
    {M n : Nat} (hM : 0 < M)
    (q : PairedOddBase (oddProjectRadius M))
    (hn : n ≤ M) :
    |actualQ3ZeroClassSignedCorrelation M q n| ≤
      actualQ3ThreePowerCorrelationDebit M q := by
  have hVar :=
    sum_selectedPairSourceCoordinateSincVariation_norm_le_harmonic
      M hM q n hn
  have hCeiling := actualQ3ThreePowerProfileCeiling_nonneg M
  unfold actualQ3ZeroClassSignedCorrelation
  unfold actualQ3ThreePowerCorrelationDebit
  calc
    |∑ t ∈ Finset.range M,
        actualQ3SignedSincVariation M q n t *
          (actualQ3ZeroClassSelectorConvolution M n (t + 1)).re| ≤
      ∑ t ∈ Finset.range M,
        |actualQ3SignedSincVariation M q n t *
          (actualQ3ZeroClassSelectorConvolution M n (t + 1)).re| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ t ∈ Finset.range M,
        ‖selectedPairSourceCoordinateSincVariation M q n t‖ *
          actualQ3ThreePowerProfileCeiling M := by
      apply Finset.sum_le_sum
      intro t _ht
      rw [abs_mul]
      have hw : |actualQ3SignedSincVariation M q n t| ≤
          ‖selectedPairSourceCoordinateSincVariation M q n t‖ := by
        unfold actualQ3SignedSincVariation
        exact Complex.abs_re_le_norm _
      have hzRe :
          |(actualQ3ZeroClassSelectorConvolution M n (t + 1)).re| ≤
            ‖actualQ3ZeroClassSelectorConvolution M n (t + 1)‖ :=
        Complex.abs_re_le_norm _
      have hzNorm :
          ‖actualQ3ZeroClassSelectorConvolution M n (t + 1)‖ ≤
            actualQ3ThreePowerProfileCeiling M := by
        unfold actualQ3ThreePowerProfileCeiling
        exact norm_actualQ3ZeroClassSelectorConvolution_le_chebyshev
          M n (t + 1)
      exact mul_le_mul hw (hzRe.trans hzNorm) (abs_nonneg _) (norm_nonneg _)
    _ = (∑ t ∈ Finset.range M,
        ‖selectedPairSourceCoordinateSincVariation M q n t‖) *
          actualQ3ThreePowerProfileCeiling M := by
      rw [Finset.sum_mul]
    _ ≤ actualQ3VariationScale M q *
          actualQ3ThreePowerProfileCeiling M := by
      exact mul_le_mul_of_nonneg_right hVar hCeiling

/-- Exact final lower bound after the completely discharged three-power
channel.  No norm is imposed on the remaining sign-sensitive channel. -/
theorem finalSignedLowerBound_le_actualCompositeReserve
    {M R n : Nat} {P : Real}
    (hM : 0 < M)
    (q : PairedOddBase (oddProjectRadius M))
    (hn : n ≤ M) :
    actualQ3ResidueSelectorBaseReserve M R n P q -
        (3 / 2 : Real) * actualQ3ThreePowerCorrelationDebit M q -
        actualQ3FullPrefixMeanSignedCorrelation M q n ≤
      actualModelQ3PreLoweringCompositeReserve M R n P q := by
  have hAbs := abs_actualQ3ZeroClassSignedCorrelation_le hM q hn
  have hUpper : actualQ3ZeroClassSignedCorrelation M q n ≤
      actualQ3ThreePowerCorrelationDebit M q :=
    (le_abs_self _).trans hAbs
  rw [actualModelQ3CompositeReserve_eq_finalSignedSplit]
  linarith

/-- Final q=3 positivity criterion: the signed full-prefix/mean correlation,
together with the now-explicit three-power debit, must stay below the literal
base reserve. -/
theorem actualModelQ3CompositeReserve_pos_of_finalSignedGate
    {M R n : Nat} {P : Real}
    (hM : 0 < M)
    (q : PairedOddBase (oddProjectRadius M))
    (hn : n ≤ M)
    (hGate :
      (3 / 2 : Real) * actualQ3ThreePowerCorrelationDebit M q +
          actualQ3FullPrefixMeanSignedCorrelation M q n <
        actualQ3ResidueSelectorBaseReserve M R n P q) :
    0 < actualModelQ3PreLoweringCompositeReserve M R n P q := by
  have hLower := finalSignedLowerBound_le_actualCompositeReserve
    (M := M) (R := R) (n := n) (P := P) hM q hn
  linarith

end GoldbachCircleMethodActualQ3ThreePowerDebitFinalGateV18790
