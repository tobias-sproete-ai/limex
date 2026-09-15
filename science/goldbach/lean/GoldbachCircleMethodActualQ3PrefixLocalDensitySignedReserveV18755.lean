import GoldbachCircleMethodActualQ3UnitClassDifferenceV18754

/-!
# V1.8.755: actual q=3 prefix-local-density signed reserve

V1.8.754 identifies the post-extraction q=3 error as the literal difference
between the two prime-compatible von Mangoldt residue masses.  This
append-only successor performs the missing signed composition: the entire
finite-prefix local-density Abel contribution is added to the project reserve,
and only the adverse real part of the true unit-class balance residual is
charged as a debit.

The updated reserve is not asserted positive, and the residue-one versus
residue-two discrepancy ceiling is not inhabited.  The final theorem is a
conditional implication with both obligations visible in its antecedent.  No
exceptional-set estimate or Goldbach conclusion is proved.
`proof_status = NO_PROOF`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

open scoped BigOperators Classical ArithmeticFunction.vonMangoldt

namespace GoldbachCircleMethodActualQ3PrefixLocalDensitySignedReserveV18755

open GoldbachCircleMethodTwoScaleEvenBlockDefectReserveV1833
open GoldbachCircleMethodOddChannelEventualAbsorptionV18658
open GoldbachCircleMethodFullDenominatorFourClassPartitionV18688
open GoldbachCircleMethodOddOddSignedFiberAdapterV18665
open GoldbachCircleMethodOddOddFourierBesselBridgeV18668
open GoldbachCircleMethodActualLambdaPairSourceMeanV710AdapterV18717
open GoldbachCircleMethodActualLambdaPairSourceMeanChebyshevBoundV18719
open GoldbachCircleMethodActualMixedChannelRamanujanFactorizationV18727
open GoldbachCircleMethodActualQ3PairResidueSignedTriangularGateV18748
open GoldbachCircleMethodActualQ3TriangularPairCarrierPullbackV18750
open GoldbachCircleMethodActualQ3PrefixLocalDensityExtractionV18753
open GoldbachCircleMethodActualQ3UnitClassDifferenceV18754

/-- Signed project reserve after the complete q=3 endpoint and the exact
finite-prefix local-density Abel term have both been retained. -/
noncomputable def actualQ3PrefixLocalDensityProjectReserve
    (M : Nat)
    (q : PairedOddBase (oddProjectRadius M))
    (n : Nat) : Real :=
  actualQ3PairResidueProjectReserve M q n +
    (actualQ3LocalDensityTriangularRemainder M q n).re

/-- Only the adverse real part of the post-extraction unit-class residual. -/
noncomputable def actualQ3UnitBalanceSignDebit
    (M : Nat)
    (q : PairedOddBase (oddProjectRadius M))
    (n : Nat) : Real :=
  max 0 (-(actualQ3UnitBalanceTriangularRemainder M q n).re)

theorem actualQ3UnitBalanceSignDebit_nonneg
    (M : Nat)
    (q : PairedOddBase (oddProjectRadius M))
    (n : Nat) :
    0 ≤ actualQ3UnitBalanceSignDebit M q n := by
  unfold actualQ3UnitBalanceSignDebit
  exact le_max_left _ _

theorem unitBalanceRemainder_re_add_signDebit_nonneg
    (M : Nat)
    (q : PairedOddBase (oddProjectRadius M))
    (n : Nat) :
    0 ≤ (actualQ3UnitBalanceTriangularRemainder M q n).re +
      actualQ3UnitBalanceSignDebit M q n := by
  unfold actualQ3UnitBalanceSignDebit
  have h := le_max_right 0
    (-(actualQ3UnitBalanceTriangularRemainder M q n).re)
  linarith

/-- Exact signed recombination after prefix-local-density extraction. -/
theorem projectReserve_add_negativeAggregate_re_eq_prefixLocalDensityReserve_add_unitBalance_re
    (M : Nat)
    (q : PairedOddBase (oddProjectRadius M))
    (n : Nat)
    (hTarget : 2 * n ∈ evenTargetBlock M)
    (hq : q.val.val = 3) :
    (M : Real) / 14 +
        (selectedPairNegativeCenteredUnitAggregate M q n).re =
      actualQ3PrefixLocalDensityProjectReserve M q n +
        (actualQ3UnitBalanceTriangularRemainder M q n).re := by
  rw [projectReserve_add_negativeAggregate_re_eq_pairResidueReserve_add_triangular_re
    M q n hTarget hq]
  rw [actualQ3TriangularPrefixRemainder_eq_localDensity_add_unitBalance
    M q n hq]
  unfold actualQ3PrefixLocalDensityProjectReserve
  rw [Complex.add_re]
  ring

/-- Sign-sensitive sufficient criterion after the correct local-density
composition. -/
theorem projectReserve_add_negativeAggregate_re_pos_of_unitBalanceSignDebit_lt_prefixLocalDensityReserve
    (M : Nat)
    (q : PairedOddBase (oddProjectRadius M))
    (n : Nat)
    (hTarget : 2 * n ∈ evenTargetBlock M)
    (hq : q.val.val = 3)
    (hDebit : actualQ3UnitBalanceSignDebit M q n <
      actualQ3PrefixLocalDensityProjectReserve M q n) :
    0 < (M : Real) / 14 +
      (selectedPairNegativeCenteredUnitAggregate M q n).re := by
  have hNonneg := unitBalanceRemainder_re_add_signDebit_nonneg M q n
  rw [projectReserve_add_negativeAggregate_re_eq_prefixLocalDensityReserve_add_unitBalance_re
    M q n hTarget hq]
  linarith

theorem actualQ3UnitBalanceSignDebit_le_norm
    (M : Nat)
    (q : PairedOddBase (oddProjectRadius M))
    (n : Nat) :
    actualQ3UnitBalanceSignDebit M q n ≤
      ‖actualQ3UnitBalanceTriangularRemainder M q n‖ := by
  unfold actualQ3UnitBalanceSignDebit
  apply max_le
  · exact norm_nonneg _
  · have hAbs :
        |(actualQ3UnitBalanceTriangularRemainder M q n).re| ≤
          ‖actualQ3UnitBalanceTriangularRemainder M q n‖ :=
      Complex.abs_re_le_norm _
    exact (neg_le_abs _).trans hAbs

/-- Final source-specific q=3 gate.  The only analytic ceiling is the actual
finite-prefix difference of the two unit residue classes; the local-density
piece remains signed inside the reserve. -/
theorem projectReserve_add_negativeAggregate_re_pos_of_unitClassDifferenceCeiling
    (M : Nat)
    (q : PairedOddBase (oddProjectRadius M))
    (n : Nat)
    (hTarget : 2 * n ∈ evenTargetBlock M)
    (hq : q.val.val = 3)
    (D : Real)
    (hD : ActualOddLambdaQ3UnitClassDifferenceCeiling M D)
    (hAbsorb :
      (∑ a ∈ Finset.range M,
          ‖selectedPairSourceCoordinateSincVariation M q n a‖) *
          (2 * oddLambdaSum M * D) <
        actualQ3PrefixLocalDensityProjectReserve M q n) :
    0 < (M : Real) / 14 +
      (selectedPairNegativeCenteredUnitAggregate M q n).re := by
  apply projectReserve_add_negativeAggregate_re_pos_of_unitBalanceSignDebit_lt_prefixLocalDensityReserve
    M q n hTarget hq
  have hDebit := actualQ3UnitBalanceSignDebit_le_norm M q n
  have hNorm :=
    actualQ3UnitBalanceTriangularRemainder_norm_le_of_unitClassDifference
      M q n D hD
  exact lt_of_le_of_lt (hDebit.trans hNorm) hAbsorb

end GoldbachCircleMethodActualQ3PrefixLocalDensitySignedReserveV18755
