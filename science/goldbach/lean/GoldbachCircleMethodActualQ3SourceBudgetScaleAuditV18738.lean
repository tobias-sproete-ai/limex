import GoldbachCircleMethodActualQ3SourceBoundDefectEnvelopeV18737
import GoldbachCircleMethodActualLambdaPairSourceMeanChebyshevBoundV18719

/-!
# V1.8.738: source-only scale audit for the actual q=3 defect budget

V1.8.737 constructs an unconditional, source-bound envelope for every actual
denominator-three progression-defect prefix.  This append-only module audits
the size obtainable from positivity and the already proved Chebyshev ceiling
alone.

The full absolute class mass is bounded by twice the total Lambda-pair mass,
and hence by an explicit quadratic Chebyshev envelope.  This is a genuine,
inhabited finite estimate, but it is deliberately classified as coarse: after
the project sinc variation is restored, it does not by itself establish the
nontrivial absorption required downstream.  A sharper distribution estimate
for the actual mod-three Lambda-pair prefixes remains open.

No minor-arc absorption, exceptional-set estimate, or Goldbach conclusion is
proved.  `proof_status = NO_PROOF`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

open scoped BigOperators Classical

namespace GoldbachCircleMethodActualQ3SourceBudgetScaleAuditV18738

open GoldbachCircleMethodOddOddSignedFiberAdapterV18665
open GoldbachCircleMethodChebyshevEnergyBudgetV1889
open GoldbachCircleMethodExactLambdaPairSourceMeanSplitV18716
open GoldbachCircleMethodActualLambdaPairSourceMeanChebyshevBoundV18719
open GoldbachCircleMethodActualQ3SplitPrefixBudgetV18735
open GoldbachCircleMethodActualCenteredSourcePrefixComplementBudgetV18736
open GoldbachCircleMethodActualQ3SourceBoundDefectEnvelopeV18737
open GoldbachCircleMethodActualLambdaPairSourceMeanV710AdapterV18717
open GoldbachCircleMethodOddChannelEventualAbsorptionV18658
open GoldbachCircleMethodFullDenominatorFourClassPartitionV18688

/-- The actual Lambda-pair source is pointwise nonnegative. -/
theorem actualLambdaPairSource_nonneg (M a : Nat) :
    0 <= actualLambdaPairSource M a := by
  unfold actualLambdaPairSource
  exact oddOddPairFiberMass_nonneg M (2 * a)

/-- The fixed arithmetic mean is nonnegative, proved directly from its exact
square-mass identity. -/
theorem actualLambdaPairSourceMean_nonneg_local (M : Nat) :
    0 <= actualLambdaPairSourceMean M := by
  unfold actualLambdaPairSourceMean
  rw [sum_actualLambdaPairSource_eq_oddLambdaSum_sq]
  positivity

/-- Centering costs at most the source value plus its fixed nonnegative mean. -/
theorem centeredActualLambdaPairSource_norm_le_source_add_mean
    (M a : Nat) :
    ‖(centeredActualLambdaPairSource M a : Complex)‖ <=
      actualLambdaPairSource M a + actualLambdaPairSourceMean M := by
  rw [Complex.norm_real, Real.norm_eq_abs]
  unfold centeredActualLambdaPairSource
  calc
    |actualLambdaPairSource M a - actualLambdaPairSourceMean M| <=
        |actualLambdaPairSource M a| + |actualLambdaPairSourceMean M| :=
      abs_sub _ _
    _ = actualLambdaPairSource M a + actualLambdaPairSourceMean M := by
      rw [abs_of_nonneg (actualLambdaPairSource_nonneg M a),
        abs_of_nonneg (actualLambdaPairSourceMean_nonneg_local M)]

/-- Summing one residue class cannot cost more than twice the total source
mass.  The equality on the right uses the exact arithmetic mean denominator,
not an asymptotic replacement. -/
theorem actualQ3CenteredClassAbsoluteMassBudget_le_two_mul_totalSource
    (M : Nat) (r : ZMod 3) :
    actualQ3CenteredClassAbsoluteMassBudget M r <=
      2 * (∑ a ∈ Finset.range M.succ, actualLambdaPairSource M a) := by
  unfold actualQ3CenteredClassAbsoluteMassBudget
  calc
    (∑ s ∈ Finset.range M.succ,
        if (s : ZMod 3) = r then
          ‖(centeredActualLambdaPairSource M s : Complex)‖ else 0) <=
      ∑ s ∈ Finset.range M.succ,
        (actualLambdaPairSource M s + actualLambdaPairSourceMean M) := by
      apply Finset.sum_le_sum
      intro s _hs
      by_cases h : (s : ZMod 3) = r
      · simp only [h, if_true]
        exact centeredActualLambdaPairSource_norm_le_source_add_mean M s
      · simp only [h, if_false]
        exact add_nonneg (actualLambdaPairSource_nonneg M s)
          (actualLambdaPairSourceMean_nonneg_local M)
    _ = (∑ s ∈ Finset.range M.succ, actualLambdaPairSource M s) +
        (M.succ : Real) * actualLambdaPairSourceMean M := by
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range]
      simp [nsmul_eq_mul]
    _ = 2 * (∑ s ∈ Finset.range M.succ, actualLambdaPairSource M s) := by
      unfold actualLambdaPairSourceMean
      have hsucc : (M.succ : Real) ≠ 0 := by positivity
      field_simp
      ring

/-- The source-only class envelope obtained from Mathlib's Chebyshev theorem
is quadratic in the project scale. -/
theorem actualQ3CenteredClassAbsoluteMassBudget_le_chebyshevQuadratic
    (M : Nat) (r : ZMod 3) :
    actualQ3CenteredClassAbsoluteMassBudget M r <=
      2 * chebyshevConstant ^ 2 * (M : Real) ^ 2 := by
  have hodd := oddLambdaSum_le_chebyshev_linear M
  have hodd0 := oddLambdaSum_nonneg M
  have hright0 : 0 <= chebyshevConstant * (M : Real) :=
    mul_nonneg chebyshevConstant_pos.le (Nat.cast_nonneg M)
  have hsq : (oddLambdaSum M) ^ 2 <=
      (chebyshevConstant * (M : Real)) ^ 2 := by
    nlinarith
  calc
    actualQ3CenteredClassAbsoluteMassBudget M r <=
        2 * (∑ a ∈ Finset.range M.succ, actualLambdaPairSource M a) :=
      actualQ3CenteredClassAbsoluteMassBudget_le_two_mul_totalSource M r
    _ = 2 * (oddLambdaSum M) ^ 2 := by
      rw [sum_actualLambdaPairSource_eq_oddLambdaSum_sq]
    _ <= 2 * (chebyshevConstant * (M : Real)) ^ 2 := by
      exact mul_le_mul_of_nonneg_left hsq (by norm_num)
    _ = 2 * chebyshevConstant ^ 2 * (M : Real) ^ 2 := by ring

/-- The literal source-bound q=3 budget is therefore bounded by the same
V1.8.736 functional with the explicit quadratic envelope substituted.  This
is only a coarse source-size ceiling, not an absorption theorem. -/
theorem actualQ3FullySourceBoundUnitBudget_le_chebyshevQuadraticSubstitution
    (M : Nat)
    (q : PairedOddBase (oddProjectRadius M))
    (n : Nat) :
    actualQ3FullySourceBoundUnitBudget M q n <=
      actualQ3ComplementResolvedUnitBudget M
        (2 * chebyshevConstant ^ 2 * (M : Real) ^ 2) q n := by
  unfold actualQ3FullySourceBoundUnitBudget actualQ3ComplementResolvedUnitBudget
  have hD := actualQ3CenteredClassAbsoluteMassBudget_le_chebyshevQuadratic
    M (n : ZMod 3)
  have hEnd : 0 <= actualQ3EndpointScale M q := by
    unfold actualQ3EndpointScale
    exact div_nonneg (by positivity) (by positivity)
  have hVar : 0 <= actualQ3VariationScale M q := by
    unfold actualQ3VariationScale
    have hHq : (0 : Rat) <= harmonic M := by
      unfold harmonic
      exact Finset.sum_nonneg fun _ _ => by positivity
    have hH : 0 <= (harmonic M : Real) := by exact_mod_cast hHq
    exact mul_nonneg (div_nonneg (by positivity) (by positivity)) hH
  have hscale : 0 <= 3 *
      (actualQ3EndpointScale M q + actualQ3VariationScale M q) := by
    positivity
  have hfirst :
      3 * ((actualQ3EndpointScale M q + actualQ3VariationScale M q) *
        actualQ3CenteredClassAbsoluteMassBudget M (n : ZMod 3)) <=
      3 * ((actualQ3EndpointScale M q + actualQ3VariationScale M q) *
        (2 * chebyshevConstant ^ 2 * (M : Real) ^ 2)) := by
    nlinarith
  simpa only [add_comm] using
    (add_le_add_right hfirst
      (∑ a ∈ Finset.range M,
        ‖selectedPairSourceCoordinateSincVariation M q n a‖ *
          actualCenteredSourceTwoSidedMassBudget M (a + 1)))

end GoldbachCircleMethodActualQ3SourceBudgetScaleAuditV18738
