import GoldbachCircleMethodExactLambdaPairSourceMeanSplitV18716

/-!
# V1.8.717: exact constant-channel Abel adapter for the actual V1.8.710 kernel

V1.8.716 already defines the source-separated literal V1.8.710 kernel and
proves the exact centered/constant split of the genuine Lambda-pair source.
This append-only module does not define a second kernel.  It proves the next
nonduplicative identities on the constant channel:

* the odd--odd carrier gate is automatic on `Finset.range M.succ`;
* the literal two-radius sinc factor and the unchanged kernel vanish at the
  moving diagonal `a = n`;
* under the explicit target-gate hypothesis, the moving notch can therefore be
  retained yet rewritten exactly as phase times the two-radius sinc weight;
* the finite kernel sum has an exact Abel endpoint/variation decomposition in
  the source coordinate;
* the V1.8.716 constant transform is the actual source mean times that exact
  decomposition.

No endpoint, variation sum, phase prefix, centered transform, or constant
channel is asserted to vanish or be small.  No conjugation is introduced.

`proof_status = NO_PROOF`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

open scoped BigOperators Classical

namespace GoldbachCircleMethodActualLambdaPairSourceMeanV710AdapterV18717

open GoldbachCircleMethodTwoScaleEvenBlockDefectReserveV1833
open GoldbachCircleMethodOddOddSignedFiberAdapterV18665
open GoldbachCircleMethodOddDoubleSincPairV18678
open GoldbachCircleMethodOddChannelEventualAbsorptionV18658
open GoldbachCircleMethodFullDenominatorFourClassPartitionV18688
open GoldbachCircleMethodActualOneFiberDFTRawPhaseSumV18705
open GoldbachCircleMethodActualJointModeCounterModulationV18709
open GoldbachCircleMethodActualDemodulatedOneFiberRelativeConvolutionV18710
open GoldbachCircleMethodExactLambdaPairSourceMeanSplitV18716

/-- On the actual source carrier, the odd--odd sum-carrier gate is automatic.
The canonical V1.8.716 kernel is not changed or simplified by definition. -/
theorem two_mul_mem_oddOddSumCarrier_of_mem_range_succ
    {M a : Nat} (ha : a ∈ Finset.range M.succ) :
    2 * a ∈ oddOddSumCarrier M := by
  apply Finset.mem_filter.mpr
  constructor
  · apply Finset.mem_range.mpr
    have haLt : a < M.succ := Finset.mem_range.mp ha
    omega
  · exact even_two_mul a

/-- Each literal radius factor is exactly zero at source coordinate `a = n`.
This records Lean's totalized `0 / 0 = 0` behavior explicitly. -/
theorem selectedPairRelativeTwoRadiusSinc_self_eq_zero
    (M : Nat)
    (q : PairedOddBase (oddProjectRadius M))
    (n : Nat) :
    selectedPairRelativeTwoRadiusSinc M q n n = 0 := by
  simp [selectedPairRelativeTwoRadiusSinc,
    selectedPairRelativeStepTwoCoordinate, explicitSincRadiusFactor]

/-- The unchanged V1.8.716 kernel is zero at the moving diagonal.  The literal
notch and the totalized sinc value agree on this zero. -/
theorem selectedPairSourceSeparatedKernel_self_eq_zero
    (M : Nat)
    (q : PairedOddBase (oddProjectRadius M))
    (n : Nat) (xi : ZMod q.val.val) :
    selectedPairSourceSeparatedKernel M q n xi n = 0 := by
  simp [selectedPairSourceSeparatedKernel]

/-- The exact additive-character phase along the source coordinate. -/
noncomputable def selectedPairRelativeAddCharPhase
    (qNat n a : Nat) [NeZero qNat] (xi : ZMod qNat) : Complex :=
  ZMod.stdAddChar
    (((((n : Int) - (a : Int)) : Int) : ZMod qNat) * xi)

/-- The unchanged literal two-radius sinc weight, now regarded as complex only
so it can enter the exact complex Abel identity. -/
noncomputable def selectedPairSourceCoordinateSincWeight
    (M : Nat)
    (q : PairedOddBase (oddProjectRadius M))
    (n a : Nat) : Complex :=
  (selectedPairRelativeTwoRadiusSinc M q n a : Complex)

/-- Exact forward source-coordinate variation of the two-radius sinc weight.
This is a definition, not a bounded-variation estimate. -/
noncomputable def selectedPairSourceCoordinateSincVariation
    (M : Nat)
    (q : PairedOddBase (oddProjectRadius M))
    (n a : Nat) : Complex :=
  selectedPairSourceCoordinateSincWeight M q n (a + 1) -
    selectedPairSourceCoordinateSincWeight M q n a

/-- Exact finite prefix of the relative additive-character phase.  No
conductor-size bound is claimed here. -/
noncomputable def selectedPairRelativeAddCharPhasePrefix
    (qNat n : Nat) [NeZero qNat] (xi : ZMod qNat) (k : Nat) : Complex :=
  ∑ a ∈ Finset.range k, selectedPairRelativeAddCharPhase qNat n a xi

/-- Under the literal target gate and on the actual finite source carrier, the
unchanged V1.8.716 kernel is exactly phase times two-radius sinc.  At `a = n`
both sides are zero, so the moving notch is not silently deleted. -/
theorem selectedPairSourceSeparatedKernel_eq_phase_mul_sinc_of_target_of_mem_range
    (M : Nat)
    (q : PairedOddBase (oddProjectRadius M))
    (n : Nat) (xi : ZMod q.val.val) (a : Nat)
    (hTarget : 2 * n ∈ evenTargetBlock M)
    (ha : a ∈ Finset.range M.succ) :
    selectedPairSourceSeparatedKernel M q n xi a =
      selectedPairRelativeAddCharPhase q.val.val n a xi *
        selectedPairSourceCoordinateSincWeight M q n a := by
  have hCarrier := two_mul_mem_oddOddSumCarrier_of_mem_range_succ ha
  by_cases han : a = n
  · subst a
    rw [selectedPairSourceSeparatedKernel_self_eq_zero]
    unfold selectedPairSourceCoordinateSincWeight
    rw [selectedPairRelativeTwoRadiusSinc_self_eq_zero]
    simp
  · have hTwoNe : 2 * a ≠ 2 * n := by omega
    simp [selectedPairSourceSeparatedKernel, hTarget, hCarrier, hTwoNe,
      selectedPairRelativeAddCharPhase,
      selectedPairSourceCoordinateSincWeight]

/-- Exact normal form of the constant-channel kernel sum under the explicit
target gate.  The source carrier gate and moving notch have been discharged by
the preceding equalities, not by approximation. -/
theorem sum_selectedPairSourceSeparatedKernel_eq_sinc_phase_sum
    (M : Nat)
    (q : PairedOddBase (oddProjectRadius M))
    (n : Nat) (xi : ZMod q.val.val)
    (hTarget : 2 * n ∈ evenTargetBlock M) :
    (∑ a ∈ Finset.range M.succ,
        selectedPairSourceSeparatedKernel M q n xi a) =
      ∑ a ∈ Finset.range M.succ,
        selectedPairSourceCoordinateSincWeight M q n a *
          selectedPairRelativeAddCharPhase q.val.val n a xi := by
  apply Finset.sum_congr rfl
  intro a ha
  rw [selectedPairSourceSeparatedKernel_eq_phase_mul_sinc_of_target_of_mem_range
    M q n xi a hTarget ha]
  rw [mul_comm]

/-- Exact Abel endpoint/variation decomposition of the constant-channel kernel
sum.  Every phase prefix and sinc variation remains explicit and unbounded. -/
theorem sum_selectedPairSourceSeparatedKernel_eq_endpoint_sub_sincVariations
    (M : Nat)
    (q : PairedOddBase (oddProjectRadius M))
    (n : Nat) (xi : ZMod q.val.val)
    (hTarget : 2 * n ∈ evenTargetBlock M) :
    (∑ a ∈ Finset.range M.succ,
        selectedPairSourceSeparatedKernel M q n xi a) =
      selectedPairSourceCoordinateSincWeight M q n M *
          selectedPairRelativeAddCharPhasePrefix q.val.val n xi M.succ -
        ∑ a ∈ Finset.range M,
          selectedPairSourceCoordinateSincVariation M q n a *
            selectedPairRelativeAddCharPhasePrefix q.val.val n xi (a + 1) := by
  rw [sum_selectedPairSourceSeparatedKernel_eq_sinc_phase_sum
    M q n xi hTarget]
  have habel := Finset.sum_range_by_parts
    (selectedPairSourceCoordinateSincWeight M q n)
    (fun a => selectedPairRelativeAddCharPhase q.val.val n a xi)
    M.succ
  simp only [Nat.succ_sub_one, smul_eq_mul] at habel
  simpa [selectedPairSourceCoordinateSincVariation,
    selectedPairRelativeAddCharPhasePrefix] using habel

/-- The actual constant-channel transform is the fixed source mean times the
exact Abel endpoint/variation expression.  Nothing on the right is asserted
to be zero or small. -/
theorem actualLambdaPairConstantKernelTransform_eq_mean_mul_endpoint_sub_sincVariations
    (M : Nat)
    (q : PairedOddBase (oddProjectRadius M))
    (n : Nat) (xi : ZMod q.val.val)
    (hTarget : 2 * n ∈ evenTargetBlock M) :
    actualLambdaPairConstantKernelTransform M
        (selectedPairSourceSeparatedKernel M q n xi) =
      (actualLambdaPairSourceMean M : Complex) *
        (selectedPairSourceCoordinateSincWeight M q n M *
            selectedPairRelativeAddCharPhasePrefix q.val.val n xi M.succ -
          ∑ a ∈ Finset.range M,
            selectedPairSourceCoordinateSincVariation M q n a *
              selectedPairRelativeAddCharPhasePrefix q.val.val n xi (a + 1)) := by
  rw [actualLambdaPairConstantKernelTransform_eq_mean_mul_sum]
  rw [sum_selectedPairSourceSeparatedKernel_eq_endpoint_sub_sincVariations
    M q n xi hTarget]

/-- The existing exact V1.8.716 raw-mode split with only its constant channel
rewritten by the exact Abel identity.  The centered transform remains present
and no q-saving is claimed for either term. -/
theorem selectedPairOneFiberDemodulatedRawPhaseSum_eq_centered_add_mean_mul_endpoint_sub_sincVariations
    (M : Nat)
    (q : PairedOddBase (oddProjectRadius M))
    (n : Nat) (xi : ZMod q.val.val)
    (hTarget : 2 * n ∈ evenTargetBlock M) :
    selectedPairOneFiberDemodulatedRawPhaseSum M q n xi =
      centeredActualLambdaPairKernelTransform M
          (selectedPairSourceSeparatedKernel M q n xi) +
        (actualLambdaPairSourceMean M : Complex) *
          (selectedPairSourceCoordinateSincWeight M q n M *
              selectedPairRelativeAddCharPhasePrefix q.val.val n xi M.succ -
            ∑ a ∈ Finset.range M,
              selectedPairSourceCoordinateSincVariation M q n a *
                selectedPairRelativeAddCharPhasePrefix q.val.val n xi (a + 1)) := by
  rw [selectedPairOneFiberDemodulatedRawPhaseSum_eq_centered_add_constant]
  rw [actualLambdaPairConstantKernelTransform_eq_mean_mul_endpoint_sub_sincVariations
    M q n xi hTarget]

end GoldbachCircleMethodActualLambdaPairSourceMeanV710AdapterV18717
