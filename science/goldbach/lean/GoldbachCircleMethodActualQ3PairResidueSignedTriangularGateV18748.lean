import GoldbachCircleMethodQ3SpectralSmallnessNegativeWitnessV18747

/-!
# V1.8.748: actual q=3 pair-residue reserve and signed triangular-prefix gate

V1.8.747 proves that positivity and finite support alone cannot force the two
nonzero q=3 Fourier modes to be small.  This append-only successor therefore
does not try to recover an absolute spectral estimate.  Instead it performs
two exact source-bound operations:

* the complete q=3 progression defect is pulled back to the literal odd--odd
  von-Mangoldt pair carrier, so its sign is an explicit residue-mass balance;
* the remaining Abel term is retained with its real sign as a triangular
  prefix remainder, and only its negative part is charged to the reserve.

The final theorem is a strictly sign-sensitive sufficient criterion.  The
criterion itself is not proved for the actual source.  No distribution
estimate, asymptotic absorption, exceptional-set theorem, or Goldbach
conclusion is asserted.  `proof_status = NO_PROOF`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

open scoped BigOperators Classical

namespace GoldbachCircleMethodActualQ3PairResidueSignedTriangularGateV18748

open GoldbachCircleMethodTwoScaleEvenBlockDefectReserveV1833
open GoldbachCircleMethodActualOneSidedKernelLeakageV18648
open GoldbachCircleMethodOddOddSignedFiberAdapterV18665
open GoldbachCircleMethodOddChannelEventualAbsorptionV18658
open GoldbachCircleMethodFullDenominatorFourClassPartitionV18688
open GoldbachCircleMethodActualLambdaPairSourceMeanChebyshevBoundV18719
open GoldbachCircleMethodExactLambdaPairSourceMeanSplitV18716
open GoldbachCircleMethodActualLambdaPairSourceMeanV710AdapterV18717
open GoldbachCircleMethodActualCenteredQ3ResidueObstructionV18730
open GoldbachCircleMethodActualCenteredQ3MassRecombinationV18731
open GoldbachCircleMethodActualQ3ProgressionDefectV18732
open GoldbachCircleMethodActualQ3AbelProgressionSubstitutionV18734
open GoldbachCircleMethodActualCenteredRamanujanPrefixAbelV18728
open GoldbachCircleMethodActualMixedChannelRamanujanFactorizationV18727
open GoldbachCircleMethodActualQ3LocalDensitySignedReserveV18739
open GoldbachCircleMethodActualQ3SignPrefixFluctuationProjectReserveV18740
open GoldbachCircleMethodActualQ3WeightedFiberPullbackV18742

/-- Literal Lambda-pair mass whose half-sum lies in the target class modulo
three.  The carrier and weight are the actual V1.8.719 objects. -/
noncomputable def actualQ3PairResidueMass (M n : Nat) : Complex :=
  ∑ ab ∈ actualOddOddPairCarrier M,
    (lambdaPairWeight ab : Complex) *
      (if sameResidueThree (oddOddHalfSum ab) n then 1 else 0)

/-- The full source-coordinate class mass is exactly the literal pair-carrier
mass.  This is a finite adequacy round trip, not an approximation. -/
theorem actualQ3ClassMassPrefix_full_eq_pairResidueMass
    (M n : Nat) :
    actualQ3ClassMassPrefix M (n : ZMod 3) M.succ =
      actualQ3PairResidueMass M n := by
  have hpull := actualLambdaPairWeightedFiberSum_eq_pairPullback M
    (fun s => if sameResidueThree s n then (1 : Complex) else 0)
  calc
    actualQ3ClassMassPrefix M (n : ZMod 3) M.succ =
        actualLambdaPairWeightedFiberSum M
          (fun s => if sameResidueThree s n then (1 : Complex) else 0) := by
      unfold actualQ3ClassMassPrefix q3ClassMass
        actualLambdaPairWeightedFiberSum sameResidueThree
      apply Finset.sum_congr rfl
      intro s _hs
      by_cases h : (s : ZMod 3) = (n : ZMod 3)
      · simp [h]
      · simp [h]
    _ = ∑ ab ∈ actualOddOddPairCarrier M,
        (lambdaPairWeight ab : Complex) *
          (if sameResidueThree (oddOddHalfSum ab) n then 1 else 0) := hpull
    _ = actualQ3PairResidueMass M n := rfl

/-- The actual complete q=3 progression defect, now written solely as a
literal pair-residue mass minus the fixed finite-mean correction. -/
noncomputable def actualQ3PairResidueDefect (M n : Nat) : Complex :=
  actualQ3PairResidueMass M n -
    (actualLambdaPairSourceMean M : Complex) *
      q3ClassIndicatorMass (n : ZMod 3) M.succ

theorem actualQ3ProgressionDefectPrefix_full_eq_pairResidueDefect
    (M n : Nat) :
    actualQ3ProgressionDefectPrefix M (n : ZMod 3) M.succ =
      actualQ3PairResidueDefect M n := by
  unfold actualQ3ProgressionDefectPrefix actualQ3PairResidueDefect
  rw [actualQ3ClassMassPrefix_full_eq_pairResidueMass]

/-- Exact pair-residue normal form of the signed local-density endpoint. -/
theorem actualQ3LocalDensityMainTerm_eq_pairResidueDefect
    (M : Nat)
    (q : PairedOddBase (oddProjectRadius M))
    (n : Nat) :
    actualQ3LocalDensityMainTerm M q n =
      3 * selectedPairSourceCoordinateSincWeight M q n M *
        actualQ3PairResidueDefect M n := by
  unfold actualQ3LocalDensityMainTerm
  rw [actualQ3ProgressionDefectPrefix_full_eq_pairResidueDefect]

/-- The Abel endpoint is exactly the local-density term when q=3. -/
theorem actualQ3LocalDensityMainTerm_eq_terminal_centeredPrefix
    (M : Nat)
    (q : PairedOddBase (oddProjectRadius M))
    (n : Nat)
    (hq : q.val.val = 3) :
    actualQ3LocalDensityMainTerm M q n =
      selectedPairSourceCoordinateSincWeight M q n M *
        actualCenteredRamanujanPrefix M q n M.succ := by
  have hPrefix :
      actualCenteredRamanujanPrefix M q n M.succ =
        3 * actualQ3ProgressionDefectPrefix M (n : ZMod 3) M.succ := by
    rw [actualCenteredRamanujanPrefix_q3_eq_three_mul_defect_sub_scalarPrefix
      M q n M.succ hq, actualCenteredSourcePrefix_full_eq_zero]
    ring
  unfold actualQ3LocalDensityMainTerm
  rw [hPrefix]
  ring

/-- Exact signed Abel remainder after the complete q=3 endpoint.  This is the
triangular prefix term itself, not a norm envelope. -/
noncomputable def actualQ3TriangularPrefixRemainder
    (M : Nat)
    (q : PairedOddBase (oddProjectRadius M))
    (n : Nat) : Complex :=
  -(∑ a ∈ Finset.range M,
      selectedPairSourceCoordinateSincVariation M q n a *
        actualCenteredRamanujanPrefix M q n (a + 1))

/-- The new triangular remainder is definitionally the complete fluctuation
term isolated in V1.8.739. -/
theorem actualQ3TriangularPrefixRemainder_eq_signedFluctuation
    (M : Nat)
    (q : PairedOddBase (oddProjectRadius M))
    (n : Nat)
    (hTarget : 2 * n ∈ evenTargetBlock M)
    (hq : q.val.val = 3) :
    actualQ3TriangularPrefixRemainder M q n =
      actualQ3SignedFluctuationRemainder M q n := by
  have hAbel :=
    selectedPairNegativeCenteredUnitAggregate_eq_endpoint_sub_actualCenteredRamanujanPrefixes
      M q n hTarget
  have hSplit :=
    selectedPairNegativeCenteredUnitAggregate_q3_eq_localDensity_add_fluctuation
      M q n hTarget hq
  have hEndpoint :=
    actualQ3LocalDensityMainTerm_eq_terminal_centeredPrefix M q n hq
  unfold actualQ3TriangularPrefixRemainder
  rw [hEndpoint] at hSplit
  linear_combination hSplit - hAbel

/-- Only the adverse real part of the exact triangular prefix is charged. -/
noncomputable def actualQ3TriangularPrefixSignDebit
    (M : Nat)
    (q : PairedOddBase (oddProjectRadius M))
    (n : Nat) : Real :=
  max 0 (-(actualQ3TriangularPrefixRemainder M q n).re)

theorem actualQ3TriangularPrefixSignDebit_nonneg
    (M : Nat)
    (q : PairedOddBase (oddProjectRadius M))
    (n : Nat) :
    0 ≤ actualQ3TriangularPrefixSignDebit M q n := by
  unfold actualQ3TriangularPrefixSignDebit
  exact le_max_left _ _

theorem triangularPrefix_re_add_signDebit_nonneg
    (M : Nat)
    (q : PairedOddBase (oddProjectRadius M))
    (n : Nat) :
    0 ≤ (actualQ3TriangularPrefixRemainder M q n).re +
      actualQ3TriangularPrefixSignDebit M q n := by
  unfold actualQ3TriangularPrefixSignDebit
  have h := le_max_right 0 (-(actualQ3TriangularPrefixRemainder M q n).re)
  linarith

/-- The exact project reserve after signed recombination of the base reserve
with the literal pair-residue endpoint. -/
noncomputable def actualQ3PairResidueProjectReserve
    (M : Nat)
    (q : PairedOddBase (oddProjectRadius M))
    (n : Nat) : Real :=
  (M : Real) / 14 +
    (3 * selectedPairSourceCoordinateSincWeight M q n M *
      actualQ3PairResidueDefect M n).re

theorem actualQ3PairResidueProjectReserve_eq_projectSignedReserve
    (M : Nat)
    (q : PairedOddBase (oddProjectRadius M))
    (n : Nat) :
    actualQ3PairResidueProjectReserve M q n =
      actualQ3ProjectSignedReserve M q n := by
  unfold actualQ3PairResidueProjectReserve actualQ3ProjectSignedReserve
  rw [actualQ3LocalDensityMainTerm_eq_pairResidueDefect]

/-- Exact source-bound signed recombination.  The only remaining adverse
quantity is the real triangular-prefix remainder. -/
theorem projectReserve_add_negativeAggregate_re_eq_pairResidueReserve_add_triangular_re
    (M : Nat)
    (q : PairedOddBase (oddProjectRadius M))
    (n : Nat)
    (hTarget : 2 * n ∈ evenTargetBlock M)
    (hq : q.val.val = 3) :
    (M : Real) / 14 +
        (selectedPairNegativeCenteredUnitAggregate M q n).re =
      actualQ3PairResidueProjectReserve M q n +
        (actualQ3TriangularPrefixRemainder M q n).re := by
  rw [actualQ3PairResidueProjectReserve_eq_projectSignedReserve]
  rw [actualQ3TriangularPrefixRemainder_eq_signedFluctuation M q n hTarget hq]
  exact projectReserve_add_negativeAggregate_re_eq_signedReserve_add_fluctuation_re
    M q n hTarget hq

/-- Sign-sensitive sufficient gate.  Unlike the earlier norm criterion, a
positive triangular fluctuation costs exactly zero. -/
theorem projectReserve_add_negativeAggregate_re_pos_of_triangularSignDebit_lt_pairResidueReserve
    (M : Nat)
    (q : PairedOddBase (oddProjectRadius M))
    (n : Nat)
    (hTarget : 2 * n ∈ evenTargetBlock M)
    (hq : q.val.val = 3)
    (hDebit : actualQ3TriangularPrefixSignDebit M q n <
      actualQ3PairResidueProjectReserve M q n) :
    0 < (M : Real) / 14 +
      (selectedPairNegativeCenteredUnitAggregate M q n).re := by
  have hNonneg := triangularPrefix_re_add_signDebit_nonneg M q n
  rw [projectReserve_add_negativeAggregate_re_eq_pairResidueReserve_add_triangular_re
    M q n hTarget hq]
  linarith

/-- The exact sign debit is never larger than the absolute norm budget of the
same triangular term.  This records the strict methodological improvement
without claiming that either side is small. -/
theorem actualQ3TriangularPrefixSignDebit_le_norm
    (M : Nat)
    (q : PairedOddBase (oddProjectRadius M))
    (n : Nat) :
    actualQ3TriangularPrefixSignDebit M q n ≤
      ‖actualQ3TriangularPrefixRemainder M q n‖ := by
  unfold actualQ3TriangularPrefixSignDebit
  apply max_le
  · exact norm_nonneg _
  · have hAbs :
        |(actualQ3TriangularPrefixRemainder M q n).re| ≤
          ‖actualQ3TriangularPrefixRemainder M q n‖ :=
      Complex.abs_re_le_norm _
    exact (neg_le_abs _).trans hAbs

end GoldbachCircleMethodActualQ3PairResidueSignedTriangularGateV18748
