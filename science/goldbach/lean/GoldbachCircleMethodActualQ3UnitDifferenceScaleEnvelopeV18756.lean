import GoldbachCircleMethodActualQ3PrefixLocalDensitySignedReserveV18755
import GoldbachCircleMethodSharpSourceSincVariationV18721

/-!
# V1.8.756: actual q=3 unit-difference scale envelope

This append-only module combines the exact unit-class discrepancy gate of
V1.8.755 with two already kernel-checked source bounds: Mathlib's explicit
Chebyshev linear ceiling for the odd von Mangoldt mass, and the sharp harmonic
total-variation ceiling for the actual sinc weight.

The result is an explicit finite envelope.  It does not inhabit the remaining
residue-one versus residue-two discrepancy bound and does not prove a lower
bound for the signed local-density reserve.  No asymptotic absorption,
exceptional-set estimate, or Goldbach conclusion is proved.
`proof_status = NO_PROOF`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

open scoped BigOperators Classical ArithmeticFunction.vonMangoldt

namespace GoldbachCircleMethodActualQ3UnitDifferenceScaleEnvelopeV18756

open GoldbachCircleMethodTwoScaleEvenBlockDefectReserveV1833
open GoldbachCircleMethodOddChannelEventualAbsorptionV18658
open GoldbachCircleMethodFullDenominatorFourClassPartitionV18688
open GoldbachCircleMethodOddOddSignedFiberAdapterV18665
open GoldbachCircleMethodOddOddFourierBesselBridgeV18668
open GoldbachCircleMethodActualLambdaPairSourceMeanV710AdapterV18717
open GoldbachCircleMethodActualLambdaPairSourceMeanChebyshevBoundV18719
open GoldbachCircleMethodChebyshevEnergyBudgetV1889
open GoldbachCircleMethodSharpSourceSincVariationV18721
open GoldbachCircleMethodActualMixedChannelRamanujanFactorizationV18727
open GoldbachCircleMethodActualQ3PairResidueSignedTriangularGateV18748
open GoldbachCircleMethodActualQ3PrefixLocalDensityExtractionV18753
open GoldbachCircleMethodActualQ3UnitClassDifferenceV18754
open GoldbachCircleMethodActualQ3PrefixLocalDensitySignedReserveV18755

/-- Explicit residual envelope after substituting the sharp sinc variation
and the Chebyshev linear source-mass ceiling. -/
noncomputable def actualQ3UnitDifferenceScaleEnvelope
    (M : Nat)
    (q : PairedOddBase (oddProjectRadius M))
    (D : Real) : Real :=
  ((12 * (oddProjectWidth M : Real) /
      ((q.val.val : Real) * (M : Real))) *
        (1 + Real.log (M : Real))) *
    (2 * (chebyshevConstant * (M : Real)) * D)

theorem actualQ3UnitDifferenceScaleEnvelope_nonneg
    (M : Nat) (hM : 0 < M)
    (q : PairedOddBase (oddProjectRadius M))
    (D : Real) (hD : 0 ≤ D) :
    0 ≤ actualQ3UnitDifferenceScaleEnvelope M q D := by
  unfold actualQ3UnitDifferenceScaleEnvelope
  have hlog : 0 ≤ 1 + Real.log (M : Real) := by
    have hM1 : (1 : Real) ≤ (M : Real) := by exact_mod_cast hM
    have := Real.log_nonneg hM1
    linarith
  have hScale0 : 0 ≤
      (12 * (oddProjectWidth M : Real) /
        ((q.val.val : Real) * (M : Real))) *
          (1 + Real.log (M : Real)) := by
    positivity
  have hChebyshev0 : 0 ≤ chebyshevConstant :=
    chebyshevConstant_pos.le
  have hInner0 : 0 ≤ 2 * (chebyshevConstant * (M : Real)) * D := by
    exact mul_nonneg
      (mul_nonneg (by norm_num)
        (mul_nonneg hChebyshev0 (Nat.cast_nonneg M))) hD
  exact mul_nonneg hScale0 hInner0

/-- Exact source residual bounded by the explicit finite scale envelope. -/
theorem actualQ3UnitBalanceTriangularRemainder_norm_le_scaleEnvelope
    (M : Nat) (hM : 0 < M)
    (q : PairedOddBase (oddProjectRadius M))
    (n : Nat) (hn : n ≤ M)
    (D : Real)
    (hD : ActualOddLambdaQ3UnitClassDifferenceCeiling M D) :
    ‖actualQ3UnitBalanceTriangularRemainder M q n‖ ≤
      actualQ3UnitDifferenceScaleEnvelope M q D := by
  have hRaw :=
    actualQ3UnitBalanceTriangularRemainder_norm_le_of_unitClassDifference
      M q n D hD
  have hVar := sum_selectedPairSourceCoordinateSincVariation_norm_le_log
    M hM q n hn
  have hOdd := oddLambdaSum_le_chebyshev_linear M
  have hInner :
      2 * oddLambdaSum M * D ≤
        2 * (chebyshevConstant * (M : Real)) * D := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hOdd (by norm_num)) hD.1
  have hVar0 : 0 ≤
      ∑ a ∈ Finset.range M,
        ‖selectedPairSourceCoordinateSincVariation M q n a‖ := by
    positivity
  have hScale0 : 0 ≤
      (12 * (oddProjectWidth M : Real) /
        ((q.val.val : Real) * (M : Real))) *
          (1 + Real.log (M : Real)) := by
    have hM1 : (1 : Real) ≤ (M : Real) := by exact_mod_cast hM
    have hlog : 0 ≤ 1 + Real.log (M : Real) := by
      have := Real.log_nonneg hM1
      linarith
    positivity
  have hInner0 : 0 ≤ 2 * oddLambdaSum M * D := by
    exact mul_nonneg
      (mul_nonneg (by norm_num) (oddLambdaSum_nonneg M)) hD.1
  exact hRaw.trans <| by
    unfold actualQ3UnitDifferenceScaleEnvelope
    exact mul_le_mul hVar hInner
      hInner0 hScale0

theorem actualQ3UnitBalanceSignDebit_le_scaleEnvelope
    (M : Nat) (hM : 0 < M)
    (q : PairedOddBase (oddProjectRadius M))
    (n : Nat) (hn : n ≤ M)
    (D : Real)
    (hD : ActualOddLambdaQ3UnitClassDifferenceCeiling M D) :
    actualQ3UnitBalanceSignDebit M q n ≤
      actualQ3UnitDifferenceScaleEnvelope M q D := by
  exact (actualQ3UnitBalanceSignDebit_le_norm M q n).trans
    (actualQ3UnitBalanceTriangularRemainder_norm_le_scaleEnvelope
      M hM q n hn D hD)

/-- Fully composed q=3 conditional gate with the available kernelized scale
bounds substituted.  The only open inequalities are the actual fixed-modulus
unit-class discrepancy and the signed prefix-local-density reserve floor. -/
theorem projectReserve_add_negativeAggregate_re_pos_of_scaleEnvelope
    (M : Nat) (hM : 0 < M)
    (q : PairedOddBase (oddProjectRadius M))
    (n : Nat)
    (hTarget : 2 * n ∈ evenTargetBlock M)
    (hq : q.val.val = 3)
    (D : Real)
    (hD : ActualOddLambdaQ3UnitClassDifferenceCeiling M D)
    (hAbsorb : actualQ3UnitDifferenceScaleEnvelope M q D <
      actualQ3PrefixLocalDensityProjectReserve M q n) :
    0 < (M : Real) / 14 +
      (selectedPairNegativeCenteredUnitAggregate M q n).re := by
  have hn : n ≤ M := by
    have hUpper := ((mem_evenTargetBlock_iff M (2 * n)).mp hTarget).2.1
    omega
  apply projectReserve_add_negativeAggregate_re_pos_of_unitBalanceSignDebit_lt_prefixLocalDensityReserve
    M q n hTarget hq
  exact lt_of_le_of_lt
    (actualQ3UnitBalanceSignDebit_le_scaleEnvelope M hM q n hn D hD)
    hAbsorb

end GoldbachCircleMethodActualQ3UnitDifferenceScaleEnvelopeV18756
