import GoldbachCircleMethodActualQ3TriangularOneDimensionalModeReductionV18751
import GoldbachCircleMethodFiniteRamanujanEnergyV18131

/-!
# V1.8.752: actual odd-Lambda q=3 residue discrepancy

V1.8.751 reduces the triangular q=3 debit to one-dimensional incomplete
odd-von-Mangoldt modes.  This append-only successor removes the remaining
complex-phase opacity: every such mode is exactly the Fourier transform of
the three literal residue masses modulo three, and its norm is bounded by
their finite L1 deviation from the exact three-class mean.

The residue discrepancy ceiling is deliberately left as an open proposition.
No distribution theorem for primes in arithmetic progressions is imported,
and no Chebyshev size bound is misreported as cancellation.  No absorption,
exceptional-set, or Goldbach theorem is proved.  `proof_status = NO_PROOF`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

open scoped BigOperators Classical ArithmeticFunction.vonMangoldt

namespace GoldbachCircleMethodActualOddLambdaQ3ResidueDiscrepancyV18752

open GoldbachCircleMethodTwoScaleEvenBlockDefectReserveV1833
open GoldbachCircleMethodOddChannelEventualAbsorptionV18658
open GoldbachCircleMethodFullDenominatorFourClassPartitionV18688
open GoldbachCircleMethodOddOddSignedFiberAdapterV18665
open GoldbachCircleMethodOddOddFourierBesselBridgeV18668
open GoldbachCircleMethodActualLambdaPairSourceMeanChebyshevBoundV18719
open GoldbachCircleMethodExactLambdaPairSourceMeanSplitV18716
open GoldbachCircleMethodActualLambdaPairSourceMeanV710AdapterV18717
open GoldbachCircleMethodActualMixedChannelRamanujanFactorizationV18727
open GoldbachCircleMethodActualQ3PairResidueSignedTriangularGateV18748
open GoldbachCircleMethodActualQ3TriangularOneDimensionalModeReductionV18751
open GoldbachCircleMethodFiniteRamanujanEnergyV18131

/-- Literal odd-von-Mangoldt mass below `B` in one residue class modulo three,
retaining the fixed ambient carrier cutoff `M`. -/
noncomputable def oddLambdaQ3ResidueMass
    (M B : Nat) (r : ZMod 3) : Complex :=
  ∑ a ∈ oddCarrier M,
    if a < B ∧ (a : ZMod 3) = r then
      (ArithmeticFunction.vonMangoldt a : Complex)
    else 0

/-- Total odd-von-Mangoldt mass on the same incomplete carrier. -/
noncomputable def oddLambdaPrefixMass (M B : Nat) : Complex :=
  ∑ a ∈ oddCarrier M,
    if a < B then (ArithmeticFunction.vonMangoldt a : Complex) else 0

/-- Exact three-class mean of the incomplete odd-Lambda mass. -/
noncomputable def oddLambdaQ3ResidueMean (M B : Nat) : Complex :=
  oddLambdaPrefixMass M B / 3

/-- Finite L1 discrepancy of the three residue masses from their exact mean. -/
noncomputable def oddLambdaQ3ResidueL1Discrepancy
    (M B : Nat) : Real :=
  ∑ r : ZMod 3,
    ‖oddLambdaQ3ResidueMass M B r - oddLambdaQ3ResidueMean M B‖

/-- Exact partition of the one-dimensional q=3 mode by residue class. -/
theorem oddLambdaQ3Prefix_eq_residue_transform
    (M B : Nat) (xi : ZMod 3) :
    oddLambdaQ3Prefix M B xi =
      ∑ r : ZMod 3,
        oddLambdaQ3ResidueMass M B r *
          ZMod.stdAddChar (r * xi) := by
  unfold oddLambdaQ3Prefix oddLambdaQ3ResidueMass
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  by_cases hB : a < B
  · simp [hB]
  · simp [hB]

/-- The three residue masses sum exactly to the incomplete total mass. -/
theorem sum_oddLambdaQ3ResidueMass_eq_total
    (M B : Nat) :
    (∑ r : ZMod 3, oddLambdaQ3ResidueMass M B r) =
      oddLambdaPrefixMass M B := by
  unfold oddLambdaQ3ResidueMass oddLambdaPrefixMass
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  by_cases hB : a < B
  · simp [hB]
  · simp [hB]

/-- Every nonzero q=3 additive character has zero mass on the complete
three-point residue group. -/
theorem sum_q3_additive_phase_eq_zero
    (xi : ZMod 3) (hxi : IsUnit xi) :
    (∑ r : ZMod 3, ZMod.stdAddChar (r * xi)) = 0 := by
  have hne : xi ≠ 0 := IsUnit.ne_zero hxi
  have h := standard_character_orthogonality 3 xi
  rw [if_neg hne] at h
  simpa only [mul_comm] using h

/-- Exact centered residue representation of either nonzero one-dimensional
mode. -/
theorem oddLambdaQ3Prefix_eq_centered_residue_transform
    (M B : Nat) (xi : ZMod 3) (hxi : IsUnit xi) :
    oddLambdaQ3Prefix M B xi =
      ∑ r : ZMod 3,
        (oddLambdaQ3ResidueMass M B r -
            oddLambdaQ3ResidueMean M B) *
          ZMod.stdAddChar (r * xi) := by
  rw [oddLambdaQ3Prefix_eq_residue_transform]
  have hzero := sum_q3_additive_phase_eq_zero xi hxi
  calc
    (∑ r : ZMod 3,
        oddLambdaQ3ResidueMass M B r * ZMod.stdAddChar (r * xi)) =
      ∑ r : ZMod 3,
        ((oddLambdaQ3ResidueMass M B r - oddLambdaQ3ResidueMean M B) +
            oddLambdaQ3ResidueMean M B) *
          ZMod.stdAddChar (r * xi) := by
        apply Finset.sum_congr rfl
        intro r _hr
        ring
    _ = (∑ r : ZMod 3,
          (oddLambdaQ3ResidueMass M B r - oddLambdaQ3ResidueMean M B) *
            ZMod.stdAddChar (r * xi)) +
        oddLambdaQ3ResidueMean M B *
          (∑ r : ZMod 3, ZMod.stdAddChar (r * xi)) := by
        simp_rw [add_mul]
        rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ = ∑ r : ZMod 3,
          (oddLambdaQ3ResidueMass M B r - oddLambdaQ3ResidueMean M B) *
            ZMod.stdAddChar (r * xi) := by
        rw [hzero, mul_zero, add_zero]

theorem oddLambdaQ3ResidueL1Discrepancy_nonneg
    (M B : Nat) :
    0 ≤ oddLambdaQ3ResidueL1Discrepancy M B := by
  unfold oddLambdaQ3ResidueL1Discrepancy
  positivity

/-- The complex mode is controlled by a literal real residue-discrepancy
quantity; no analytic estimate is hidden in this transfer. -/
theorem oddLambdaQ3Prefix_norm_le_residueL1
    (M B : Nat) (xi : ZMod 3) (hxi : IsUnit xi) :
    ‖oddLambdaQ3Prefix M B xi‖ ≤
      oddLambdaQ3ResidueL1Discrepancy M B := by
  rw [oddLambdaQ3Prefix_eq_centered_residue_transform M B xi hxi]
  unfold oddLambdaQ3ResidueL1Discrepancy
  calc
    _ ≤ ∑ r : ZMod 3,
        ‖(oddLambdaQ3ResidueMass M B r - oddLambdaQ3ResidueMean M B) *
          ZMod.stdAddChar (r * xi)‖ := norm_sum_le _ _
    _ = ∑ r : ZMod 3,
        ‖oddLambdaQ3ResidueMass M B r - oddLambdaQ3ResidueMean M B‖ := by
      apply Finset.sum_congr rfl
      intro r _hr
      rw [norm_mul]
      have hchar : ‖ZMod.stdAddChar (r * xi)‖ = 1 := by simp
      rw [hchar, mul_one]

/-- The exact remaining number-theoretic contract, expressed without complex
phases: every finite three-class residue discrepancy must lie below `D`. -/
def ActualOddLambdaQ3ResidueL1Ceiling (M : Nat) (D : Real) : Prop :=
  0 ≤ D ∧
    ∀ B : Nat, oddLambdaQ3ResidueL1Discrepancy M B ≤ D

/-- A residue discrepancy ceiling inhabits the one-dimensional mode contract
of V1.8.751. -/
theorem residueL1Ceiling_implies_prefixCeiling
    (M : Nat) (D : Real)
    (hD : ActualOddLambdaQ3ResidueL1Ceiling M D) :
    ActualOddLambdaQ3PrefixCeiling M D := by
  refine ⟨hD.1, ?_⟩
  intro B xi hxi
  exact (oddLambdaQ3Prefix_norm_le_residueL1 M B xi hxi).trans (hD.2 B)

/-- Final transfer to the signed project reserve.  The unresolved premise is
now a concrete finite residue-discrepancy ceiling for the actual source. -/
theorem projectReserve_add_negativeAggregate_re_pos_of_residueL1Ceiling
    (M : Nat)
    (q : PairedOddBase (oddProjectRadius M))
    (n : Nat)
    (hTarget : 2 * n ∈ evenTargetBlock M)
    (hq : q.val.val = 3)
    (D : Real)
    (hD : ActualOddLambdaQ3ResidueL1Ceiling M D)
    (hAbsorb :
      (∑ a ∈ Finset.range M,
          ‖selectedPairSourceCoordinateSincVariation M q n a‖) *
          (2 * oddLambdaSum M * D +
            4 * actualLambdaPairSourceMean M) <
        actualQ3PairResidueProjectReserve M q n) :
    0 < (M : Real) / 14 +
      (selectedPairNegativeCenteredUnitAggregate M q n).re := by
  exact projectReserve_add_negativeAggregate_re_pos_of_oneDimensionalPrefixCeiling
    M q n hTarget hq D (residueL1Ceiling_implies_prefixCeiling M D hD) hAbsorb

end GoldbachCircleMethodActualOddLambdaQ3ResidueDiscrepancyV18752
