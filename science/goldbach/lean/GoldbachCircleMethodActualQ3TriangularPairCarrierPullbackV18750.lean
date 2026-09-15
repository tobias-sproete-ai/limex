import GoldbachCircleMethodQ3TriangularPrefixNegativeWitnessV18749

/-!
# V1.8.750: actual q=3 triangular-prefix pair-carrier pullback

V1.8.749 shows that endpoint cancellation alone cannot control an incomplete
q=3 Abel prefix.  This append-only module therefore binds every such prefix
back to the literal odd--odd von-Mangoldt pair box.  The cutoff is the exact
triangle `oddOddHalfSum ab < k`; it is neither enlarged to a rectangle nor
replaced by a caller-selected source.

The resulting identity exposes the only admissible next analytic object: a
fixed-modulus signed Lambda-pair sum on a triangular region.  No estimate for
that object is asserted.  No minor-arc, exceptional-set, or Goldbach theorem
is proved.  `proof_status = NO_PROOF`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

open scoped BigOperators Classical

namespace GoldbachCircleMethodActualQ3TriangularPairCarrierPullbackV18750

open GoldbachCircleMethodTwoScaleEvenBlockDefectReserveV1833
open GoldbachCircleMethodActualOneSidedKernelLeakageV18648
open GoldbachCircleMethodOddChannelEventualAbsorptionV18658
open GoldbachCircleMethodFullDenominatorFourClassPartitionV18688
open GoldbachCircleMethodFiniteResiduePrefixV1866
open GoldbachCircleMethodActualLambdaPairSourceMeanChebyshevBoundV18719
open GoldbachCircleMethodExactLambdaPairSourceMeanSplitV18716
open GoldbachCircleMethodActualLambdaPairSourceMeanV710AdapterV18717
open GoldbachCircleMethodActualCenteredQ3ResidueObstructionV18730
open GoldbachCircleMethodActualQ3ProgressionDefectV18732
open GoldbachCircleMethodActualQ3AbelProgressionSubstitutionV18734
open GoldbachCircleMethodActualCenteredRamanujanPrefixAbelV18728
open GoldbachCircleMethodActualMixedChannelRamanujanFactorizationV18727
open GoldbachCircleMethodActualQ3WeightedFiberPullbackV18742
open GoldbachCircleMethodActualQ3PairResidueSignedTriangularGateV18748

/-- The exact source-coordinate q=3 phase used by the actual prefix. -/
noncomputable def actualQ3SourcePhase (n s : Nat) : Complex :=
  @unitCharacterSum 3 ⟨by norm_num⟩
    (((2 * ((s : Int) - (n : Int)) : Int) : ZMod 3))

/-- Literal raw q=3 pair transform on the exact triangular half-sum cutoff. -/
noncomputable def actualQ3RawTriangularPairPrefix
    (M n k : Nat) : Complex :=
  ∑ ab ∈ actualOddOddPairCarrier M,
    if oddOddHalfSum ab < k then
      (lambdaPairWeight ab : Complex) *
        @unitCharacterSum 3 ⟨by norm_num⟩
          (((((ab.1 + ab.2 : Nat) : Int) - 2 * (n : Int) : Int) : ZMod 3))
    else 0

/-- Exact pullback of every admissible raw source prefix to the literal
triangular Lambda-pair carrier. -/
theorem actualQ3RawSourcePrefix_eq_triangularPairPrefix
    (M n k : Nat) (hk : k ≤ M.succ) :
    actualQ3RawSourcePrefix M n k =
      actualQ3RawTriangularPairPrefix M n k := by
  have hRange :
      (Finset.range M.succ).filter (fun s => s < k) = Finset.range k := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  have hExtend :
      (∑ s ∈ Finset.range k,
          (actualLambdaPairSource M s : Complex) * actualQ3SourcePhase n s) =
        ∑ s ∈ Finset.range M.succ,
          (actualLambdaPairSource M s : Complex) *
            (if s < k then actualQ3SourcePhase n s else 0) := by
    rw [← hRange]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro s _hs
    by_cases hsk : s < k <;> simp [hsk]
  have hPull := actualLambdaPairWeightedFiberSum_eq_pairPullback M
    (fun s => if s < k then actualQ3SourcePhase n s else 0)
  unfold actualQ3RawSourcePrefix
  change (∑ s ∈ Finset.range k,
      (actualLambdaPairSource M s : Complex) * actualQ3SourcePhase n s) = _
  rw [hExtend]
  change actualLambdaPairWeightedFiberSum M
      (fun s => if s < k then actualQ3SourcePhase n s else 0) = _
  rw [hPull]
  unfold actualQ3RawTriangularPairPrefix
  apply Finset.sum_congr rfl
  intro ab hab
  by_cases htri : oddOddHalfSum ab < k
  · simp only [htri, if_true]
    unfold actualQ3SourcePhase
    rw [q3HalfSumPhase_eq_pairSumPhase M n ab hab]
  · simp [htri]

/-- Exact centered triangular pair prefix, including the literal finite-mean
correction. -/
noncomputable def actualQ3CenteredTriangularPairPrefix
    (M n k : Nat) : Complex :=
  actualQ3RawTriangularPairPrefix M n k -
    (actualLambdaPairSourceMean M : Complex) * q3ConstantPrefix n k

theorem actualCenteredRamanujanPrefix_q3_eq_centeredTriangularPairPrefix
    (M : Nat)
    (q : PairedOddBase (oddProjectRadius M))
    (n k : Nat)
    (hq : q.val.val = 3)
    (hk : k ≤ M.succ) :
    actualCenteredRamanujanPrefix M q n k =
      actualQ3CenteredTriangularPairPrefix M n k := by
  rw [actualCenteredRamanujanPrefix_q3_eq_raw_sub_meanConstant M q n k hq]
  rw [actualQ3RawSourcePrefix_eq_triangularPairPrefix M n k hk]
  rfl

/-- Exact pair-carrier form of the complete signed triangular Abel remainder.
Every prefix cutoff remains visible. -/
theorem actualQ3TriangularPrefixRemainder_eq_pairPrefixes
    (M : Nat)
    (q : PairedOddBase (oddProjectRadius M))
    (n : Nat)
    (hq : q.val.val = 3) :
    actualQ3TriangularPrefixRemainder M q n =
      -(∑ a ∈ Finset.range M,
          selectedPairSourceCoordinateSincVariation M q n a *
            actualQ3CenteredTriangularPairPrefix M n (a + 1)) := by
  unfold actualQ3TriangularPrefixRemainder
  apply congrArg Neg.neg
  apply Finset.sum_congr rfl
  intro a ha
  have hk : a + 1 ≤ M.succ := by
    have ha' := Finset.mem_range.mp ha
    omega
  rw [actualCenteredRamanujanPrefix_q3_eq_centeredTriangularPairPrefix
    M q n (a + 1) hq hk]

/-- The sign-sensitive project gate can now be stated entirely on the actual
pair carrier.  The premise remains an open arithmetic inequality. -/
theorem projectReserve_add_negativeAggregate_re_pos_of_pairPrefixDebit
    (M : Nat)
    (q : PairedOddBase (oddProjectRadius M))
    (n : Nat)
    (hTarget : 2 * n ∈ evenTargetBlock M)
    (hq : q.val.val = 3)
    (hDebit :
      max 0
          (-(-(∑ a ∈ Finset.range M,
              selectedPairSourceCoordinateSincVariation M q n a *
                actualQ3CenteredTriangularPairPrefix M n (a + 1))).re) <
        actualQ3PairResidueProjectReserve M q n) :
    0 < (M : Real) / 14 +
      (selectedPairNegativeCenteredUnitAggregate M q n).re := by
  apply projectReserve_add_negativeAggregate_re_pos_of_triangularSignDebit_lt_pairResidueReserve
    M q n hTarget hq
  unfold actualQ3TriangularPrefixSignDebit
  rw [actualQ3TriangularPrefixRemainder_eq_pairPrefixes M q n hq]
  exact hDebit

end GoldbachCircleMethodActualQ3TriangularPairCarrierPullbackV18750
