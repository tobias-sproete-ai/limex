import GoldbachCircleMethodActualQ3SourceBudgetScaleAuditV18738

/-!
# V1.8.739: actual q=3 local-density extraction and signed reserve composition

V1.8.738 shows that treating the complete denominator-three contribution as
an absolute error pays a quadratic source-size envelope and cannot establish
the required absorption.  This append-only successor does not repeat that
loss.  It extracts the exact endpoint term of the actual q=3 Abel identity as
a signed local-density main term and leaves only the variation sum plus the
already isolated scalar-prefix correction in the absolute remainder budget.

The extracted term is definitionally bound to the genuine centered
von-Mangoldt pair source.  It is not a free model parameter.  Its real part is
added with its actual sign to a supplied upstream reserve, and the positivity
criterion charges only the fluctuation remainder.

No sign or lower bound for the extracted local-density term is proved.  No
nontrivial prefix-distribution estimate, minor-arc absorption, exceptional-set
bound, or Goldbach conclusion is asserted.  `proof_status = NO_PROOF`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

open scoped BigOperators Classical

namespace GoldbachCircleMethodActualQ3LocalDensitySignedReserveV18739

open GoldbachCircleMethodTwoScaleEvenBlockDefectReserveV1833
open GoldbachCircleMethodOddOddSignedFiberAdapterV18665
open GoldbachCircleMethodOddChannelEventualAbsorptionV18658
open GoldbachCircleMethodFullDenominatorFourClassPartitionV18688
open GoldbachCircleMethodActualDemodulatedOneFiberRelativeConvolutionV18710
open GoldbachCircleMethodActualLambdaPairSourceMeanV710AdapterV18717
open GoldbachCircleMethodSharpSourceSincVariationV18721
open GoldbachCircleMethodSelectedPairLocalPeriodAbelAdapterV18691
open GoldbachCircleMethodActualMixedChannelRamanujanFactorizationV18727
open GoldbachCircleMethodActualQ3AbelProgressionSubstitutionV18734
open GoldbachCircleMethodActualQ3SplitPrefixBudgetV18735

/-- The complete-prefix endpoint of the actual q=3 Abel formula, retained with
its literal complex sign.  This is the local-density main term; it is not an
independently selectable approximation. -/
noncomputable def actualQ3LocalDensityMainTerm
    (M : Nat)
    (q : PairedOddBase (oddProjectRadius M))
    (n : Nat) : Complex :=
  3 * selectedPairSourceCoordinateSincWeight M q n M *
    actualQ3ProgressionDefectPrefix M (n : ZMod 3) M.succ

/-- The progression component left after removing the exact complete-prefix
endpoint from the q=3 Abel functional. -/
noncomputable def actualQ3ProgressionVariationRemainder
    (M : Nat)
    (q : PairedOddBase (oddProjectRadius M))
    (n : Nat) : Complex :=
  ∑ a ∈ Finset.range M,
    selectedPairSourceCoordinateSincVariation M q n a *
      actualQ3ProgressionDefectPrefix M (n : ZMod 3) (a + 1)

/-- The full q=3 fluctuation remainder.  It contains no copy of the extracted
endpoint main term. -/
noncomputable def actualQ3SignedFluctuationRemainder
    (M : Nat)
    (q : PairedOddBase (oddProjectRadius M))
    (n : Nat) : Complex :=
  -(3 * actualQ3ProgressionVariationRemainder M q n) +
    actualCenteredScalarPrefixAbelCorrection M q n

/-- Exact source-bound extraction of the q=3 local-density endpoint from the
negative-orientation centered unit aggregate. -/
theorem selectedPairNegativeCenteredUnitAggregate_q3_eq_localDensity_add_fluctuation
    (M : Nat)
    (q : PairedOddBase (oddProjectRadius M))
    (n : Nat)
    (hTarget : 2 * n ∈ evenTargetBlock M)
    (hq : q.val.val = 3) :
    selectedPairNegativeCenteredUnitAggregate M q n =
      actualQ3LocalDensityMainTerm M q n +
        actualQ3SignedFluctuationRemainder M q n := by
  rw [selectedPairNegativeCenteredUnitAggregate_q3_eq_defectAbel_add_scalarCorrection
    M q n hTarget hq]
  unfold actualQ3ProgressionDefectAbelFunctional
    actualQ3LocalDensityMainTerm actualQ3SignedFluctuationRemainder
    actualQ3ProgressionVariationRemainder
  ring

/-- The independently retained positive orientation has the same exact signed
local-density extraction after the V1.8.734 sign bridge. -/
theorem selectedPairPositiveCenteredUnitAggregate_q3_eq_localDensity_add_fluctuation
    (M : Nat)
    (q : PairedOddBase (oddProjectRadius M))
    (n : Nat)
    (hTarget : 2 * n ∈ evenTargetBlock M)
    (hq : q.val.val = 3) :
    selectedPairPositiveCenteredUnitAggregate M q n =
      actualQ3LocalDensityMainTerm M q n +
        actualQ3SignedFluctuationRemainder M q n := by
  rw [selectedPairPositiveCenteredUnitAggregate_q3_eq_defectAbel_add_scalarCorrection
    M q n hTarget hq]
  unfold actualQ3ProgressionDefectAbelFunctional
    actualQ3LocalDensityMainTerm actualQ3SignedFluctuationRemainder
    actualQ3ProgressionVariationRemainder
  ring

/-- The reduced absolute budget after the complete q=3 endpoint has been
removed from the error side. -/
noncomputable def actualQ3FluctuationBudget
    (M : Nat) (D S : Real)
    (q : PairedOddBase (oddProjectRadius M)) : Real :=
  3 * actualQ3VariationScale M q * D +
    actualQ3VariationScale M q * S

/-- Exact accounting identity: relative to the previous split budget, signed
local-density extraction removes precisely the endpoint tax and nothing else. -/
theorem actualQ3SplitUnitBudget_eq_fluctuationBudget_add_endpointTax
    (M : Nat) (D S : Real)
    (q : PairedOddBase (oddProjectRadius M)) :
    actualQ3SplitUnitBudget M D S q =
      actualQ3FluctuationBudget M D S q +
        3 * actualQ3EndpointScale M q * D := by
  unfold actualQ3SplitUnitBudget actualQ3FluctuationBudget
  ring

/-- For a nonnegative defect envelope, the new remainder budget is never
larger than the previous absolute split budget. -/
theorem actualQ3FluctuationBudget_le_splitUnitBudget
    (M : Nat) (D S : Real)
    (q : PairedOddBase (oddProjectRadius M))
    (hD : 0 ≤ D) :
    actualQ3FluctuationBudget M D S q ≤
      actualQ3SplitUnitBudget M D S q := by
  rw [actualQ3SplitUnitBudget_eq_fluctuationBudget_add_endpointTax]
  have hEndpoint : 0 ≤ actualQ3EndpointScale M q := by
    unfold actualQ3EndpointScale
    positivity
  have hTax : 0 ≤ 3 * actualQ3EndpointScale M q * D := by positivity
  linarith

/-- Only the sinc-variation scale is charged to the progression remainder;
the endpoint scale no longer appears in this bound. -/
theorem actualQ3ProgressionVariationRemainder_norm_le
    {M : Nat} {D S : Real} (hM : 0 < M)
    (q : PairedOddBase (oddProjectRadius M))
    (n : Nat) (hn : n ≤ M)
    (henv : ActualQ3SplitPrefixEnvelope M q n D S) :
    ‖actualQ3ProgressionVariationRemainder M q n‖ ≤
      actualQ3VariationScale M q * D := by
  have hVar := sum_selectedPairSourceCoordinateSincVariation_norm_le_harmonic
    M hM q n hn
  unfold actualQ3ProgressionVariationRemainder
  calc
    _ ≤ ∑ a ∈ Finset.range M,
        ‖selectedPairSourceCoordinateSincVariation M q n a *
          actualQ3ProgressionDefectPrefix M (n : ZMod 3) (a + 1)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ a ∈ Finset.range M,
        ‖selectedPairSourceCoordinateSincVariation M q n a‖ * D := by
      apply Finset.sum_le_sum
      intro a ha
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left
        (henv.defect_bound (a + 1) (by
          have ha' := Finset.mem_range.mp ha
          omega)) (norm_nonneg _)
    _ = (∑ a ∈ Finset.range M,
        ‖selectedPairSourceCoordinateSincVariation M q n a‖) * D := by
      rw [Finset.sum_mul]
    _ ≤ actualQ3VariationScale M q * D :=
      mul_le_mul_of_nonneg_right hVar henv.defect_nonneg

/-- Norm bound for the exact fluctuation remainder after signed local-density
extraction. -/
theorem actualQ3SignedFluctuationRemainder_norm_le
    {M : Nat} {D S : Real} (hM : 0 < M)
    (q : PairedOddBase (oddProjectRadius M))
    (n : Nat) (hn : n ≤ M)
    (henv : ActualQ3SplitPrefixEnvelope M q n D S) :
    ‖actualQ3SignedFluctuationRemainder M q n‖ ≤
      actualQ3FluctuationBudget M D S q := by
  have hProgression := actualQ3ProgressionVariationRemainder_norm_le
    hM q n hn henv
  have hScalar := actualCenteredScalarPrefixAbelCorrection_norm_le
    hM q n hn henv
  unfold actualQ3SignedFluctuationRemainder actualQ3FluctuationBudget
  calc
    _ ≤ ‖-(3 * actualQ3ProgressionVariationRemainder M q n)‖ +
        ‖actualCenteredScalarPrefixAbelCorrection M q n‖ := norm_add_le _ _
    _ = 3 * ‖actualQ3ProgressionVariationRemainder M q n‖ +
        ‖actualCenteredScalarPrefixAbelCorrection M q n‖ := by simp
    _ ≤ 3 * (actualQ3VariationScale M q * D) +
        actualQ3VariationScale M q * S := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left hProgression (by norm_num)) hScalar
    _ = 3 * actualQ3VariationScale M q * D +
        actualQ3VariationScale M q * S := by ring

/-- The actual q=3 endpoint is combined with an upstream real reserve without
taking its absolute value. -/
noncomputable def actualQ3SignedReserve
    (baseReserve : Real)
    (M : Nat)
    (q : PairedOddBase (oddProjectRadius M))
    (n : Nat) : Real :=
  baseReserve + (actualQ3LocalDensityMainTerm M q n).re

/-- Exact signed composition for the negative orientation. -/
theorem baseReserve_add_negativeAggregate_re_eq_signedReserve_add_fluctuation_re
    (baseReserve : Real)
    (M : Nat)
    (q : PairedOddBase (oddProjectRadius M))
    (n : Nat)
    (hTarget : 2 * n ∈ evenTargetBlock M)
    (hq : q.val.val = 3) :
    baseReserve + (selectedPairNegativeCenteredUnitAggregate M q n).re =
      actualQ3SignedReserve baseReserve M q n +
        (actualQ3SignedFluctuationRemainder M q n).re := by
  rw [selectedPairNegativeCenteredUnitAggregate_q3_eq_localDensity_add_fluctuation
    M q n hTarget hq]
  unfold actualQ3SignedReserve
  simp only [Complex.add_re]
  ring

/-- The same signed composition for the positive orientation. -/
theorem baseReserve_add_positiveAggregate_re_eq_signedReserve_add_fluctuation_re
    (baseReserve : Real)
    (M : Nat)
    (q : PairedOddBase (oddProjectRadius M))
    (n : Nat)
    (hTarget : 2 * n ∈ evenTargetBlock M)
    (hq : q.val.val = 3) :
    baseReserve + (selectedPairPositiveCenteredUnitAggregate M q n).re =
      actualQ3SignedReserve baseReserve M q n +
        (actualQ3SignedFluctuationRemainder M q n).re := by
  rw [selectedPairPositiveCenteredUnitAggregate_q3_eq_localDensity_add_fluctuation
    M q n hTarget hq]
  unfold actualQ3SignedReserve
  simp only [Complex.add_re]
  ring

/-- Conditional positivity after exact signed reserve composition.  The
condition charges only the fluctuation budget; no absolute-value tax is paid
on the local-density endpoint. -/
theorem baseReserve_add_negativeAggregate_re_pos_of_fluctuation_lt_signedReserve
    {M : Nat} {D S baseReserve : Real} (hM : 0 < M)
    (q : PairedOddBase (oddProjectRadius M))
    (n : Nat) (hTarget : 2 * n ∈ evenTargetBlock M)
    (hq : q.val.val = 3)
    (henv : ActualQ3SplitPrefixEnvelope M q n D S)
    (hBudget : actualQ3FluctuationBudget M D S q <
      actualQ3SignedReserve baseReserve M q n) :
    0 < baseReserve +
      (selectedPairNegativeCenteredUnitAggregate M q n).re := by
  have hn : n ≤ M := by
    have hUpper := ((mem_evenTargetBlock_iff M (2 * n)).mp hTarget).2.1
    omega
  have hNorm := actualQ3SignedFluctuationRemainder_norm_le
    hM q n hn henv
  have hAbs :
      |(actualQ3SignedFluctuationRemainder M q n).re| ≤
        ‖actualQ3SignedFluctuationRemainder M q n‖ :=
    Complex.abs_re_le_norm _
  have hLower :
      -actualQ3FluctuationBudget M D S q ≤
        (actualQ3SignedFluctuationRemainder M q n).re := by
    have hNegNorm :
        -‖actualQ3SignedFluctuationRemainder M q n‖ ≤
          (actualQ3SignedFluctuationRemainder M q n).re :=
      neg_le_of_abs_le hAbs
    linarith
  rw [baseReserve_add_negativeAggregate_re_eq_signedReserve_add_fluctuation_re
    baseReserve M q n hTarget hq]
  linarith

end GoldbachCircleMethodActualQ3LocalDensitySignedReserveV18739
