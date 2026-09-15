import GoldbachCircleMethodActualQ3PrefixLocalDensityExtractionV18753

/-!
# V1.8.754: actual q=3 unit-class difference

V1.8.753 extracts the large q=3 local-density bias before any cancellation
claim.  This append-only successor closes the remaining finite algebra.  For
either nonzero q=3 frequency, the local-density mode is exactly the zero-class
mass minus the common unit-class mean.  The post-extraction L1 residual is
exactly the norm of the difference between the literal residue-one and
residue-two von Mangoldt prefix masses.

Thus the surviving number-theoretic obligation is not three-class
equidistribution.  It is the explicit finite discrepancy between the two
prime-compatible progressions modulo three.  No bound for that discrepancy is
asserted or inhabited.  No absorption, exceptional-set, or Goldbach theorem is
proved.  `proof_status = NO_PROOF`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

open scoped BigOperators Classical ArithmeticFunction.vonMangoldt

namespace GoldbachCircleMethodActualQ3UnitClassDifferenceV18754

open GoldbachCircleMethodTwoScaleEvenBlockDefectReserveV1833
open GoldbachCircleMethodOddChannelEventualAbsorptionV18658
open GoldbachCircleMethodFullDenominatorFourClassPartitionV18688
open GoldbachCircleMethodOddOddSignedFiberAdapterV18665
open GoldbachCircleMethodOddOddFourierBesselBridgeV18668
open GoldbachCircleMethodActualCenteredRamanujanPrefixAbelV18728
open GoldbachCircleMethodActualLambdaPairSourceMeanV710AdapterV18717
open GoldbachCircleMethodActualLambdaPairSourceMeanChebyshevBoundV18719
open GoldbachCircleMethodActualOddLambdaQ3ResidueDiscrepancyV18752
open GoldbachCircleMethodActualQ3PrefixLocalDensityExtractionV18753

/-- The two nonzero q=3 phases sum to minus one at every unit frequency. -/
theorem q3_two_unit_residue_phases_eq_neg_one
    (xi : ZMod 3) (hxi : IsUnit xi) :
    ZMod.stdAddChar ((1 : ZMod 3) * xi) +
        ZMod.stdAddChar ((2 : ZMod 3) * xi) = -1 := by
  have hzero := sum_q3_additive_phase_eq_zero xi hxi
  have huniv : (Finset.univ : Finset (ZMod 3)) = {0, 1, 2} := by decide
  rw [huniv] at hzero
  have h01 : (0 : ZMod 3) ∉ ({1, 2} : Finset (ZMod 3)) := by decide
  have h12 : (1 : ZMod 3) ∉ ({2} : Finset (ZMod 3)) := by decide
  rw [Finset.sum_insert h01, Finset.sum_insert h12,
    Finset.sum_singleton] at hzero
  have hchar0 : ZMod.stdAddChar (0 : ZMod 3) = 1 := by simp
  rw [zero_mul, hchar0] at hzero
  linear_combination hzero

/-- Closed form of the extracted local-density mode. -/
theorem oddLambdaQ3LocalDensityMode_eq_zeroMass_sub_unitMean
    (M B : Nat) (xi : ZMod 3) (hxi : IsUnit xi) :
    oddLambdaQ3LocalDensityMode M B xi =
      oddLambdaQ3ResidueMass M B (0 : ZMod 3) -
        oddLambdaQ3UnitMean M B := by
  unfold oddLambdaQ3LocalDensityMode
  have huniv : (Finset.univ : Finset (ZMod 3)) = {0, 1, 2} := by decide
  rw [huniv]
  have h01 : (0 : ZMod 3) ∉ ({1, 2} : Finset (ZMod 3)) := by decide
  have h12 : (1 : ZMod 3) ∉ ({2} : Finset (ZMod 3)) := by decide
  rw [Finset.sum_insert h01, Finset.sum_insert h12,
    Finset.sum_singleton]
  rw [localDensityReferenceMass_zero]
  rw [localDensityReferenceMass_unit M B (1 : ZMod 3) (by decide)]
  rw [localDensityReferenceMass_unit M B (2 : ZMod 3) (by decide)]
  have hchar0 : ZMod.stdAddChar (0 : ZMod 3) = 1 := by simp
  rw [zero_mul, hchar0, mul_one]
  rw [← mul_add, q3_two_unit_residue_phases_eq_neg_one xi hxi]
  ring

/-- Elementary two-point centering identity in the complex norm. -/
theorem two_point_centered_l1_eq_norm_sub (z₁ z₂ : Complex) :
    ‖z₁ - (z₁ + z₂) / 2‖ + ‖z₂ - (z₁ + z₂) / 2‖ =
      ‖z₁ - z₂‖ := by
  have h₁ : z₁ - (z₁ + z₂) / 2 = (z₁ - z₂) / 2 := by ring
  have h₂ : z₂ - (z₁ + z₂) / 2 = -(z₁ - z₂) / 2 := by ring
  rw [h₁, h₂, norm_div, norm_div, norm_neg]
  norm_num

/-- Exact collapse of the post-extraction L1 budget to one literal
unit-class difference. -/
theorem oddLambdaQ3UnitBalanceL1_eq_unitClassDifference
    (M B : Nat) :
    oddLambdaQ3UnitBalanceL1 M B =
      ‖oddLambdaQ3ResidueMass M B (1 : ZMod 3) -
        oddLambdaQ3ResidueMass M B (2 : ZMod 3)‖ := by
  unfold oddLambdaQ3UnitBalanceL1
  have huniv : (Finset.univ : Finset (ZMod 3)) = {0, 1, 2} := by decide
  rw [huniv]
  have h01 : (0 : ZMod 3) ∉ ({1, 2} : Finset (ZMod 3)) := by decide
  have h12 : (1 : ZMod 3) ∉ ({2} : Finset (ZMod 3)) := by decide
  rw [Finset.sum_insert h01, Finset.sum_insert h12,
    Finset.sum_singleton]
  rw [localDensityReferenceMass_zero]
  rw [localDensityReferenceMass_unit M B (1 : ZMod 3) (by decide)]
  rw [localDensityReferenceMass_unit M B (2 : ZMod 3) (by decide)]
  simp only [sub_self, norm_zero, zero_add]
  exact two_point_centered_l1_eq_norm_sub _ _

/-- Exact post-extraction arithmetic contract: a uniform finite-prefix bound
only for the difference of the two prime-compatible residue masses. -/
def ActualOddLambdaQ3UnitClassDifferenceCeiling
    (M : Nat) (D : Real) : Prop :=
  0 ≤ D ∧ ∀ B : Nat,
    ‖oddLambdaQ3ResidueMass M B (1 : ZMod 3) -
      oddLambdaQ3ResidueMass M B (2 : ZMod 3)‖ ≤ D

theorem unitClassDifferenceCeiling_iff_unitBalanceCeiling
    (M : Nat) (D : Real) :
    ActualOddLambdaQ3UnitClassDifferenceCeiling M D ↔
      ActualOddLambdaQ3UnitBalanceCeiling M D := by
  constructor
  · intro hD
    refine ⟨hD.1, ?_⟩
    intro B
    rw [oddLambdaQ3UnitBalanceL1_eq_unitClassDifference]
    exact hD.2 B
  · intro hD
    refine ⟨hD.1, ?_⟩
    intro B
    rw [← oddLambdaQ3UnitBalanceL1_eq_unitClassDifference]
    exact hD.2 B

/-- The q=3 Abel residual bound expressed solely through the actual
residue-one versus residue-two Lambda-prefix discrepancy. -/
theorem actualQ3UnitBalanceTriangularRemainder_norm_le_of_unitClassDifference
    (M : Nat)
    (q : PairedOddBase (oddProjectRadius M))
    (n : Nat)
    (D : Real)
    (hD : ActualOddLambdaQ3UnitClassDifferenceCeiling M D) :
    ‖actualQ3UnitBalanceTriangularRemainder M q n‖ ≤
      (∑ a ∈ Finset.range M,
          ‖selectedPairSourceCoordinateSincVariation M q n a‖) *
        (2 * oddLambdaSum M * D) := by
  exact actualQ3UnitBalanceTriangularRemainder_norm_le
    M q n D ((unitClassDifferenceCeiling_iff_unitBalanceCeiling M D).mp hD)

end GoldbachCircleMethodActualQ3UnitClassDifferenceV18754
