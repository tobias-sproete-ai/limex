import GoldbachCircleMethodActualDemodulatedOneFiberRelativeConvolutionV18710

/-!
# V1.8.716: exact source-bound mean split of the Lambda-pair fiber

This append-only module repairs the adequacy defect isolated in V1.8.715.
There is no freely chosen comparison function.  The source is definitionally
the actual arithmetic fiber

`H_M(a) = oddOddPairFiberMass M (2 * a)`

on `Finset.range M.succ`, and its comparison channel is the uniquely specified
finite arithmetic mean of that source.

The module proves exact pointwise reconstruction, exact zero total mass of the
centered source, and exact linear splitting against an arbitrary supplied
complex kernel.  The kernel parameter retains all later target, character,
notch, and sinc weights rather than replacing any of them.

No theorem says that the centered transform or the constant channel is zero or
small.  No moment, dispersion, exceptional-set, or Goldbach conclusion is
proved.

`proof_status = NO_PROOF`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

open scoped BigOperators Classical ComplexConjugate

namespace GoldbachCircleMethodExactLambdaPairSourceMeanSplitV18716

open GoldbachCircleMethodTwoScaleEvenBlockDefectReserveV1833
open GoldbachCircleMethodOddOddSignedFiberAdapterV18665
open GoldbachCircleMethodOddDoubleSincPairV18678
open GoldbachCircleMethodOddChannelEventualAbsorptionV18658
open GoldbachCircleMethodFullDenominatorFourClassPartitionV18688
open GoldbachCircleMethodActualOneFiberDFTRawPhaseSumV18705
open GoldbachCircleMethodActualJointModeCounterModulationV18709
open GoldbachCircleMethodActualDemodulatedOneFiberRelativeConvolutionV18710

/-- The genuine arithmetic source on the finite half-target coordinate.  It is
not a field, hypothesis, or caller-selectable comparison function. -/
noncomputable def actualLambdaPairSource (M a : Nat) : Real :=
  oddOddPairFiberMass M (2 * a)

/-- The unique finite arithmetic mean of the actual source on
`Finset.range M.succ`.  The denominator is exactly the carrier cardinality
`M + 1`. -/
noncomputable def actualLambdaPairSourceMean (M : Nat) : Real :=
  (∑ a ∈ Finset.range M.succ, actualLambdaPairSource M a) / (M.succ : Real)

/-- The actual source centered by its definitionally fixed finite mean. -/
noncomputable def centeredActualLambdaPairSource (M a : Nat) : Real :=
  actualLambdaPairSource M a - actualLambdaPairSourceMean M

/-- The constant channel attached to the same fixed source mean. -/
noncomputable def actualLambdaPairConstantChannel (M _a : Nat) : Real :=
  actualLambdaPairSourceMean M

/-- Exact pointwise reconstruction of the source from its fixed centered and
constant channels. -/
theorem actualLambdaPairSource_eq_centered_add_constant
    (M a : Nat) :
    actualLambdaPairSource M a =
      centeredActualLambdaPairSource M a +
        actualLambdaPairConstantChannel M a := by
  simp [centeredActualLambdaPairSource, actualLambdaPairConstantChannel]

/-- The fixed centered source has exact zero total mass on its defining finite
carrier.  No asymptotic estimate is used. -/
theorem sum_centeredActualLambdaPairSource_eq_zero (M : Nat) :
    ∑ a ∈ Finset.range M.succ, centeredActualLambdaPairSource M a = 0 := by
  simp only [centeredActualLambdaPairSource]
  rw [Finset.sum_sub_distrib]
  rw [Finset.sum_const, Finset.card_range]
  simp only [nsmul_eq_mul]
  unfold actualLambdaPairSourceMean
  have hsucc : (M.succ : Real) ≠ 0 := by positivity
  field_simp
  ring

/-- Linear transform of a real source against an explicitly supplied complex
kernel.  The kernel stays a parameter so every actual arithmetic and analytic
weight can be retained by later specializations. -/
noncomputable def sourceKernelTransform
    (M : Nat) (H : Nat → Real) (kernel : Nat → Complex) : Complex :=
  ∑ a ∈ Finset.range M.succ, (H a : Complex) * kernel a

/-- The transform of the definitionally fixed Lambda-pair source. -/
noncomputable def actualLambdaPairKernelTransform
    (M : Nat) (kernel : Nat → Complex) : Complex :=
  sourceKernelTransform M (actualLambdaPairSource M) kernel

/-- The transform of the fixed mean-zero channel. -/
noncomputable def centeredActualLambdaPairKernelTransform
    (M : Nat) (kernel : Nat → Complex) : Complex :=
  sourceKernelTransform M (centeredActualLambdaPairSource M) kernel

/-- The transform of the fixed constant channel.  It is intentionally retained
as an exact finite term; this module makes no vanishing or smallness claim. -/
noncomputable def actualLambdaPairConstantKernelTransform
    (M : Nat) (kernel : Nat → Complex) : Complex :=
  sourceKernelTransform M (actualLambdaPairConstantChannel M) kernel

/-- Exact linear split for the actual source against every supplied complex
kernel.  This is an identity, not a cancellation estimate. -/
theorem actualLambdaPairKernelTransform_eq_centered_add_constant
    (M : Nat) (kernel : Nat → Complex) :
    actualLambdaPairKernelTransform M kernel =
      centeredActualLambdaPairKernelTransform M kernel +
        actualLambdaPairConstantKernelTransform M kernel := by
  unfold actualLambdaPairKernelTransform
    centeredActualLambdaPairKernelTransform
    actualLambdaPairConstantKernelTransform sourceKernelTransform
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  simp only [Finset.mem_range] at ha
  rw [← add_mul]
  congr 1
  exact_mod_cast actualLambdaPairSource_eq_centered_add_constant M a

/-- The constant-channel transform can be factored exactly as the fixed source
mean times the unweighted complex kernel sum.  This exposes rather than hides
the remaining constant contribution. -/
theorem actualLambdaPairConstantKernelTransform_eq_mean_mul_sum
    (M : Nat) (kernel : Nat → Complex) :
    actualLambdaPairConstantKernelTransform M kernel =
      (actualLambdaPairSourceMean M : Complex) *
        (∑ a ∈ Finset.range M.succ, kernel a) := by
  unfold actualLambdaPairConstantKernelTransform sourceKernelTransform
    actualLambdaPairConstantChannel
  rw [Finset.mul_sum]

/-- The literal V1.8.710 selected-pair kernel with the arithmetic source mass
factored out, while retaining the even-target gate, odd--odd carrier, moving
notch, character phase, and both original sinc radii. -/
noncomputable def selectedPairSourceSeparatedKernel
    (M : Nat)
    (q : PairedOddBase (oddProjectRadius M))
    (n : Nat) (xi : ZMod q.val.val) (a : Nat) : Complex :=
  if 2 * n ∈ evenTargetBlock M ∧
      2 * a ∈ oddOddSumCarrier M ∧ 2 * a ≠ 2 * n then
    ZMod.stdAddChar
        (((((n : Int) - (a : Int)) : Int) : ZMod q.val.val) * xi) *
      (selectedPairRelativeTwoRadiusSinc M q n a : Complex)
  else 0

/-- One actual V1.8.710 term is exactly the definitionally fixed Lambda-pair
source times the source-separated literal kernel. -/
theorem selectedPairOneFiberRelativeConvolutionTerm_eq_source_mul_kernel
    (M : Nat)
    (q : PairedOddBase (oddProjectRadius M))
    (n : Nat) (xi : ZMod q.val.val) (a : Nat) :
    selectedPairOneFiberRelativeConvolutionTerm M q n xi a =
      (actualLambdaPairSource M a : Complex) *
        selectedPairSourceSeparatedKernel M q n xi a := by
  unfold selectedPairOneFiberRelativeConvolutionTerm
    selectedPairSourceSeparatedKernel selectedPairRelativeSincFiberWeight
    actualLambdaPairSource
  split_ifs
  next => push_cast; ring
  next => ring

/-- The actual V1.8.710 demodulated raw phase sum is the source-bound kernel
transform.  This is the adequacy bridge from the generic linear algebra above
back to the literal Goldbach branch. -/
theorem selectedPairOneFiberDemodulatedRawPhaseSum_eq_actualSourceTransform
    (M : Nat)
    (q : PairedOddBase (oddProjectRadius M))
    (n : Nat) (xi : ZMod q.val.val) :
    selectedPairOneFiberDemodulatedRawPhaseSum M q n xi =
      actualLambdaPairKernelTransform M
        (selectedPairSourceSeparatedKernel M q n xi) := by
  rw [selectedPairOneFiberDemodulatedRawPhaseSum_eq_relativeConvolution]
  unfold actualLambdaPairKernelTransform sourceKernelTransform
  apply Finset.sum_congr rfl
  intro a _ha
  exact selectedPairOneFiberRelativeConvolutionTerm_eq_source_mul_kernel
    M q n xi a

/-- Exact actual-kernel mean split.  Both terms remain present; in particular,
the constant channel is not silently discarded. -/
theorem selectedPairOneFiberDemodulatedRawPhaseSum_eq_centered_add_constant
    (M : Nat)
    (q : PairedOddBase (oddProjectRadius M))
    (n : Nat) (xi : ZMod q.val.val) :
    selectedPairOneFiberDemodulatedRawPhaseSum M q n xi =
      centeredActualLambdaPairKernelTransform M
          (selectedPairSourceSeparatedKernel M q n xi) +
        actualLambdaPairConstantKernelTransform M
          (selectedPairSourceSeparatedKernel M q n xi) := by
  rw [selectedPairOneFiberDemodulatedRawPhaseSum_eq_actualSourceTransform]
  exact actualLambdaPairKernelTransform_eq_centered_add_constant M _

end GoldbachCircleMethodExactLambdaPairSourceMeanSplitV18716
