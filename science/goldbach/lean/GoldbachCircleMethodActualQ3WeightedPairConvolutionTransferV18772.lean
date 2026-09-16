import GoldbachCircleMethodActualModelQ3CompositeReserveFloorDecisionV18770
import GoldbachCircleMethodActualQ3UnitClassDifferenceV18754

/-!
# V1.8.772: actual q=3 weighted pair-convolution transfer

The local-density part of the literal q=3 triangular prefix is rewritten on
the unchanged odd-von-Mangoldt carrier as one signed weighted convolution.
The second factor is the exact finite-prefix zero-class mass minus the common
mean of the two unit classes.  The coefficient retains both q=3 unit phases;
no absolute value and no free main term is introduced.

The module also records a finite structural negative witness: a common
two-point prefix ceiling and the same terminal sum do not determine the sign
of a signed weighted correlation.  Consequently the one-dimensional class
estimate used upstream cannot, by itself, supply the positive project-reserve
floor.  A carrier-specific correlation or weight-compatibility theorem is
still required.

No actual-source negative sequence, positive composite-reserve floor,
exceptional-set estimate, or Goldbach conclusion is proved.
`proof_status = NO_PROOF`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

open scoped BigOperators Classical ArithmeticFunction.vonMangoldt

namespace GoldbachCircleMethodActualQ3WeightedPairConvolutionTransferV18772

open GoldbachCircleMethodOddChannelEventualAbsorptionV18658
open GoldbachCircleMethodFullDenominatorFourClassPartitionV18688
open GoldbachCircleMethodOddOddFourierBesselBridgeV18668
open GoldbachCircleMethodExactLambdaPairSourceMeanSplitV18716
open GoldbachCircleMethodActualLambdaPairSourceMeanV710AdapterV18717
open GoldbachCircleMethodActualQ3WeightedFiberPullbackV18742
open GoldbachCircleMethodActualOddLambdaQ3ResidueDiscrepancyV18752
open GoldbachCircleMethodActualQ3PrefixLocalDensityExtractionV18753
open GoldbachCircleMethodActualQ3UnitClassDifferenceV18754

/-- The exact q=3 unit-phase coefficient seen by the outer odd-Lambda
coordinate after the local-density extraction. -/
noncomputable def actualQ3OuterUnitPhaseCoefficient
    (n a : Nat) : Complex :=
  ZMod.stdAddChar (((-2 * (n : Int) : Int) : ZMod 3) * (1 : ZMod 3)) *
      ZMod.stdAddChar ((a : ZMod 3) * (1 : ZMod 3)) +
    ZMod.stdAddChar (((-2 * (n : Int) : Int) : ZMod 3) * (2 : ZMod 3)) *
      ZMod.stdAddChar ((a : ZMod 3) * (2 : ZMod 3))

/-- Literal signed weighted pair convolution obtained from the q=3
local-density modes.  Both coordinates use the actual finite odd-Lambda
source: the outer coordinate appears pointwise and the inner coordinate via
its exact residue-prefix masses. -/
noncomputable def actualQ3WeightedPairLocalDensityConvolution
    (M n k : Nat) : Complex :=
  ∑ a ∈ oddCarrier M,
    ((ArithmeticFunction.vonMangoldt a : Complex) *
        (oddLambdaQ3ResidueMass M (2 * k - a) (0 : ZMod 3) -
          oddLambdaQ3UnitMean M (2 * k - a))) *
      actualQ3OuterUnitPhaseCoefficient n a

/-- Exact carrier-preserving transfer from the two local-density Fourier
modes to one signed weighted pair convolution. -/
theorem actualQ3RawTriangularPairLocalDensity_eq_weightedPairConvolution
    (M n k : Nat) :
    actualQ3RawTriangularPairLocalDensity M n k =
      actualQ3WeightedPairLocalDensityConvolution M n k := by
  unfold actualQ3RawTriangularPairLocalDensity
    actualQ3TriangularPairLocalDensityMode
    actualQ3WeightedPairLocalDensityConvolution
    actualQ3OuterUnitPhaseCoefficient
  simp_rw [oddLambdaQ3LocalDensityMode_eq_zeroMass_sub_unitMean
    M _ (1 : ZMod 3) (by decide)]
  simp_rw [oddLambdaQ3LocalDensityMode_eq_zeroMass_sub_unitMean
    M _ (2 : ZMod 3) (by decide)]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _ha
  ring

/-- The centered local-density prefix is therefore the literal weighted pair
convolution minus the already fixed project mean term.  This statement does
not change either carrier or coefficient. -/
theorem actualQ3CenteredTriangularLocalDensityMain_eq_weightedPairConvolution_sub_mean
    (M n k : Nat) :
    actualQ3CenteredTriangularLocalDensityMain M n k =
      actualQ3WeightedPairLocalDensityConvolution M n k -
        (actualLambdaPairSourceMean M : Complex) * q3ConstantPrefix n k := by
  unfold actualQ3CenteredTriangularLocalDensityMain
  rw [actualQ3RawTriangularPairLocalDensity_eq_weightedPairConvolution]

/-- Exact transfer through the project's unchanged Sinc/Abel weight.  The
local-density remainder is now displayed as a signed weighted pair
convolution at every triangular prefix; no norm or positivity inference is
inserted. -/
theorem actualQ3LocalDensityTriangularRemainder_eq_weightedPairConvolutionAbel
    (M : Nat) (q : PairedOddBase (oddProjectRadius M)) (n : Nat) :
    actualQ3LocalDensityTriangularRemainder M q n =
      -∑ a ∈ Finset.range M,
        selectedPairSourceCoordinateSincVariation M q n a *
          (actualQ3WeightedPairLocalDensityConvolution M n (a + 1) -
            (actualLambdaPairSourceMean M : Complex) *
              q3ConstantPrefix n (a + 1)) := by
  unfold actualQ3LocalDensityTriangularRemainder
  simp_rw [
    actualQ3CenteredTriangularLocalDensityMain_eq_weightedPairConvolution_sub_mean]

/-- Minimal abstract signed correlation used only to test what information a
prefix ceiling can logically force. -/
noncomputable def twoPointSignedCorrelation
    (w x : Fin 2 → Real) : Real :=
  ∑ i, w i * x i

/-- The information profile supplied by a unit-size prefix ceiling together
with a zero terminal sum. -/
def TwoPointPrefixAdmissible (x : Fin 2 → Real) : Prop :=
  |x 0| ≤ 1 ∧ |x 0 + x 1| ≤ 1 ∧ x 0 + x 1 = 0

def structuralWeight : Fin 2 → Real := fun i =>
  if i = 0 then 1 else -1

def structuralPositiveSource : Fin 2 → Real := fun i =>
  if i = 0 then 1 else -1

def structuralNegativeSource : Fin 2 → Real := fun i =>
  if i = 0 then -1 else 1

theorem structuralPositiveSource_prefixAdmissible :
    TwoPointPrefixAdmissible structuralPositiveSource := by
  norm_num [TwoPointPrefixAdmissible, structuralPositiveSource]

theorem structuralNegativeSource_prefixAdmissible :
    TwoPointPrefixAdmissible structuralNegativeSource := by
  norm_num [TwoPointPrefixAdmissible, structuralNegativeSource]

theorem structuralPositiveSource_correlation :
    twoPointSignedCorrelation structuralWeight structuralPositiveSource = 2 := by
  norm_num [twoPointSignedCorrelation, structuralWeight,
    structuralPositiveSource, Fin.sum_univ_two]

theorem structuralNegativeSource_correlation :
    twoPointSignedCorrelation structuralWeight structuralNegativeSource = -2 := by
  norm_num [twoPointSignedCorrelation, structuralWeight,
    structuralNegativeSource, Fin.sum_univ_two]

/-- Structural negative witness for the invalid inference schema
"common prefix ceiling plus common terminal sum determines the sign of a
signed weighted convolution".  It is not a negative witness for the actual
von-Mangoldt source. -/
theorem prefixCeiling_does_not_determine_signed_correlation :
    TwoPointPrefixAdmissible structuralPositiveSource ∧
      TwoPointPrefixAdmissible structuralNegativeSource ∧
      0 < twoPointSignedCorrelation structuralWeight structuralPositiveSource ∧
      twoPointSignedCorrelation structuralWeight structuralNegativeSource < 0 := by
  refine ⟨structuralPositiveSource_prefixAdmissible,
    structuralNegativeSource_prefixAdmissible, ?_, ?_⟩
  · rw [structuralPositiveSource_correlation]
    norm_num
  · rw [structuralNegativeSource_correlation]
    norm_num

end GoldbachCircleMethodActualQ3WeightedPairConvolutionTransferV18772
