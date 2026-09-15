import GoldbachCircleMethodActualQ3ProjectDebitAbsorptionOrNegativeWitnessV18741

/-!
# V1.8.742: weighted pullback of the actual q=3 endpoint to the Lambda-pair box

V1.8.741 proves that global centering plus an absolute-mass envelope cannot
establish the project-debit inequality.  This append-only successor leaves that
closed negative branch and returns to the definitionally fixed arithmetic
source.

An arbitrary complex weight on the half-target fibers is pulled back exactly
to the literal odd--odd Lambda-pair box.  The result is then specialized to the
denominator-three Ramanujan weight.  Finally, the exact centered q=3 endpoint
is split into the raw signed pair transform and the literal constant-channel
prefix.  No triangle inequality is used in these identities.

This module does not estimate either signed term.  No prime-distribution,
minor-arc, exceptional-set, or Goldbach conclusion is proved.
`proof_status = NO_PROOF`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

open scoped BigOperators Classical ArithmeticFunction.vonMangoldt

namespace GoldbachCircleMethodActualQ3WeightedFiberPullbackV18742

open GoldbachCircleMethodOddOddSignedFiberAdapterV18665
open GoldbachCircleMethodActualOneSidedKernelLeakageV18648
open GoldbachCircleMethodFiniteResiduePrefixV1866
open GoldbachCircleMethodActualLambdaPairSourceMeanChebyshevBoundV18719
open GoldbachCircleMethodExactLambdaPairSourceMeanSplitV18716
open GoldbachCircleMethodActualCenteredQ3ResidueObstructionV18730
open GoldbachCircleMethodActualCenteredRamanujanPrefixAbelV18728
open GoldbachCircleMethodActualQ3AbelProgressionSubstitutionV18734
open GoldbachCircleMethodActualQ3LocalDensitySignedReserveV18739
open GoldbachCircleMethodActualQ3ProjectDebitAbsorptionOrNegativeWitnessV18741
open GoldbachCircleMethodActualLambdaPairSourceMeanV710AdapterV18717
open GoldbachCircleMethodOddChannelEventualAbsorptionV18658
open GoldbachCircleMethodFullDenominatorFourClassPartitionV18688

/-- The actual Lambda-pair fibers against an arbitrary retained complex
weight.  The source is fixed; only the test weight is supplied. -/
noncomputable def actualLambdaPairWeightedFiberSum
    (M : Nat) (g : Nat -> Complex) : Complex :=
  ∑ a ∈ Finset.range M.succ, (actualLambdaPairSource M a : Complex) * g a

/-- Exact weighted fiber pullback to the literal odd--odd pair box.  This is
the weighted analogue of the unweighted source-mass identity in V1.8.719. -/
theorem actualLambdaPairWeightedFiberSum_eq_pairPullback
    (M : Nat) (g : Nat -> Complex) :
    actualLambdaPairWeightedFiberSum M g =
      ∑ ab ∈ actualOddOddPairCarrier M,
        (lambdaPairWeight ab : Complex) * g (oddOddHalfSum ab) := by
  classical
  have hpartition :
      (∑ a ∈ Finset.range M.succ,
          ∑ ab ∈ actualOddOddPairCarrier M with oddOddHalfSum ab = a,
            (lambdaPairWeight ab : Complex) * g (oddOddHalfSum ab)) =
        ∑ ab ∈ actualOddOddPairCarrier M,
          (lambdaPairWeight ab : Complex) * g (oddOddHalfSum ab) :=
    Finset.sum_fiberwise_of_maps_to
      (fun ab hab => oddOddHalfSum_mem_range M ab hab)
      (fun ab => (lambdaPairWeight ab : Complex) * g (oddOddHalfSum ab))
  unfold actualLambdaPairWeightedFiberSum
  rw [← hpartition]
  apply Finset.sum_congr rfl
  intro a _ha
  unfold actualLambdaPairSource
  change
    ((∑ ab ∈
        (((Finset.range M.succ).product (Finset.range M.succ)).filter
          (fun ab => Odd ab.1 ∧ Odd ab.2)) with
        ab.1 + ab.2 = 2 * a, lambdaPairWeight ab : Real) : Complex) * g a =
      ∑ ab ∈ actualOddOddPairCarrier M with oddOddHalfSum ab = a,
        (lambdaPairWeight ab : Complex) * g (oddOddHalfSum ab)
  push_cast
  rw [Finset.sum_mul]
  apply Finset.sum_congr
  · ext ab
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨⟨habBox, habOdd⟩, hsum⟩
      have habPublic : ab ∈ actualOddOddPairCarrier M := by
        rcases Finset.mem_product.mp habBox with ⟨ha, hb⟩
        exact Finset.mem_product.mpr
          ⟨Finset.mem_filter.mpr ⟨ha, habOdd.1⟩,
            Finset.mem_filter.mpr ⟨hb, habOdd.2⟩⟩
      exact ⟨habPublic,
        (oddOddHalfSum_eq_iff_sum_eq_two_mul M a ab habPublic).2 hsum⟩
    · rintro ⟨habPublic, hhalf⟩
      rcases Finset.mem_product.mp habPublic with ⟨ha, hb⟩
      rcases Finset.mem_filter.mp ha with ⟨haRange, haOdd⟩
      rcases Finset.mem_filter.mp hb with ⟨hbRange, hbOdd⟩
      exact ⟨⟨Finset.mem_product.mpr ⟨haRange, hbRange⟩,
          ⟨haOdd, hbOdd⟩⟩,
        (oddOddHalfSum_eq_iff_sum_eq_two_mul M a ab habPublic).1 hhalf⟩
  · intro ab hab
    have hhalf : oddOddHalfSum ab = a := (Finset.mem_filter.mp hab).2
    rw [hhalf]

/-- Raw, uncentered denominator-three transform of the genuine half-target
source. -/
noncomputable def actualQ3RawSourceTransform (M n : Nat) : Complex :=
  actualLambdaPairWeightedFiberSum M (fun s =>
    @unitCharacterSum 3 ⟨by norm_num⟩
      (((2 * ((s : Int) - (n : Int)) : Int) : ZMod 3)))

/-- The same raw transform written on the literal odd--odd Lambda-pair box. -/
noncomputable def actualQ3RawPairTransform (M n : Nat) : Complex :=
  ∑ ab ∈ actualOddOddPairCarrier M,
    (lambdaPairWeight ab : Complex) *
      @unitCharacterSum 3 ⟨by norm_num⟩
        (((((ab.1 + ab.2 : Nat) : Int) - 2 * (n : Int) : Int) : ZMod 3))

/-- On every actual odd--odd pair, the half-target q=3 phase is exactly the
pair-sum q=3 phase. -/
theorem q3HalfSumPhase_eq_pairSumPhase
    (M n : Nat) (ab : Nat × Nat)
    (hab : ab ∈ actualOddOddPairCarrier M) :
    (((2 * ((oddOddHalfSum ab : Int) - (n : Int)) : Int) : ZMod 3)) =
      (((((ab.1 + ab.2 : Nat) : Int) - 2 * (n : Int) : Int) : ZMod 3)) := by
  have hsumNat : ab.1 + ab.2 = 2 * oddOddHalfSum ab :=
    (oddOddHalfSum_eq_iff_sum_eq_two_mul
      M (oddOddHalfSum ab) ab hab).1 rfl
  have hsumInt :
      ((ab.1 + ab.2 : Nat) : Int) = 2 * (oddOddHalfSum ab : Int) := by
    exact_mod_cast hsumNat
  rw [hsumInt]
  push_cast
  ring

/-- Exact source-bound pair-box representation of the raw q=3 endpoint. -/
theorem actualQ3RawSourceTransform_eq_pairTransform (M n : Nat) :
    actualQ3RawSourceTransform M n = actualQ3RawPairTransform M n := by
  unfold actualQ3RawSourceTransform actualQ3RawPairTransform
  rw [actualLambdaPairWeightedFiberSum_eq_pairPullback]
  apply Finset.sum_congr rfl
  intro ab hab
  rw [q3HalfSumPhase_eq_pairSumPhase M n ab hab]

/-- Literal q=3 prefix of the constant sequence.  It remains explicit here;
the next gate may exploit its complete-period cancellation. -/
noncomputable def q3ConstantPrefix (n k : Nat) : Complex :=
  q3EvenStepTransform (fun _ => 1) n k

/-- Raw q=3 transform on an arbitrary source-coordinate prefix. -/
noncomputable def actualQ3RawSourcePrefix (M n k : Nat) : Complex :=
  ∑ s ∈ Finset.range k, (actualLambdaPairSource M s : Complex) *
    @unitCharacterSum 3 ⟨by norm_num⟩
      (((2 * ((s : Int) - (n : Int)) : Int) : ZMod 3))

/-- Exact centering split of the actual q=3 prefix into a raw arithmetic
transform and its constant-channel correction. -/
theorem actualCenteredRamanujanPrefix_q3_eq_raw_sub_meanConstant
    (M : Nat)
    (q : PairedOddBase (oddProjectRadius M))
    (n k : Nat)
    (hq : q.val.val = 3) :
    actualCenteredRamanujanPrefix M q n k =
      actualQ3RawSourcePrefix M n k -
      (actualLambdaPairSourceMean M : Complex) * q3ConstantPrefix n k := by
  rw [actualCenteredRamanujanPrefix_eq_q3EvenStepTransform_prefix M q n k hq]
  unfold q3ConstantPrefix q3EvenStepTransform
    actualQ3RawSourcePrefix centeredActualLambdaPairSource
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro s _hs
  simp only [Complex.ofReal_sub]
  ring

/-- The complete raw prefix is exactly the weighted full-source transform. -/
theorem actualQ3RawSourcePrefix_full_eq_transform (M n : Nat) :
    actualQ3RawSourcePrefix M n M.succ = actualQ3RawSourceTransform M n := by
  unfold actualQ3RawSourcePrefix actualQ3RawSourceTransform
    actualLambdaPairWeightedFiberSum
  rfl

/-- Complete-prefix specialization: the extracted local-density endpoint is
the selected sinc weight times the exact raw pair transform, minus the literal
mean-channel prefix. -/
theorem actualQ3LocalDensityMainTerm_eq_weight_mul_pairTransform_sub_meanConstant
    (M : Nat)
    (q : PairedOddBase (oddProjectRadius M))
    (n : Nat)
    (hq : q.val.val = 3) :
    actualQ3LocalDensityMainTerm M q n =
      selectedPairSourceCoordinateSincWeight M q n M *
        (actualQ3RawPairTransform M n -
          (actualLambdaPairSourceMean M : Complex) *
            q3ConstantPrefix n M.succ) := by
  have hPrefix := actualCenteredRamanujanPrefix_q3_eq_raw_sub_meanConstant
    M q n M.succ hq
  rw [actualQ3RawSourcePrefix_full_eq_transform,
    actualQ3RawSourceTransform_eq_pairTransform] at hPrefix
  have hEndpoint :
      actualCenteredRamanujanPrefix M q n M.succ =
        3 * actualQ3ProgressionDefectPrefix M (n : ZMod 3) M.succ := by
    rw [actualCenteredRamanujanPrefix_q3_eq_three_mul_defect_sub_scalarPrefix
      M q n M.succ hq, actualCenteredSourcePrefix_full_eq_zero]
    ring
  unfold actualQ3LocalDensityMainTerm
  calc
    3 * selectedPairSourceCoordinateSincWeight M q n M *
        actualQ3ProgressionDefectPrefix M (n : ZMod 3) M.succ =
      selectedPairSourceCoordinateSincWeight M q n M *
        actualCenteredRamanujanPrefix M q n M.succ := by
          rw [hEndpoint]
          ring
    _ = selectedPairSourceCoordinateSincWeight M q n M *
        (actualQ3RawPairTransform M n -
          (actualLambdaPairSourceMean M : Complex) *
            q3ConstantPrefix n M.succ) := by rw [hPrefix]

end GoldbachCircleMethodActualQ3WeightedFiberPullbackV18742
