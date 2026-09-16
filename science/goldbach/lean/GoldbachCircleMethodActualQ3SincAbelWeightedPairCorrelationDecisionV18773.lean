import GoldbachCircleMethodActualQ3WeightedPairConvolutionTransferV18772
import GoldbachCircleMethodActualCenteredQ3ResidueObstructionV18730

/-!
# V1.8.773: actual q=3 Sinc/Abel weighted pair-correlation decision

This append-only module evaluates the remaining outer q=3 phase in the
literal weighted pair convolution.  It is exactly the denominator-three
Ramanujan coefficient at `a - 2n`, hence it is the real selector `2` on the
target residue class and `-1` on the other two classes.

The result removes all complex-phase ambiguity from the outer coefficient.
It does not prove a positive Sinc/Abel weighted correlation floor, and it
does not construct an unbounded negative sequence for the actual
von-Mangoldt source.  The requested dichotomy therefore remains fail-closed.

No exceptional-set estimate or Goldbach conclusion is proved.
`proof_status = NO_PROOF`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

open scoped BigOperators Classical ArithmeticFunction.vonMangoldt

namespace GoldbachCircleMethodActualQ3SincAbelWeightedPairCorrelationDecisionV18773

open GoldbachCircleMethodActualCenteredQ3ResidueObstructionV18730
open GoldbachCircleMethodFiniteResiduePrefixV1866
open GoldbachCircleMethodOddChannelEventualAbsorptionV18658
open GoldbachCircleMethodFullDenominatorFourClassPartitionV18688
open GoldbachCircleMethodExactLambdaPairSourceMeanSplitV18716
open GoldbachCircleMethodActualLambdaPairSourceMeanV710AdapterV18717
open GoldbachCircleMethodActualQ3WeightedFiberPullbackV18742
open GoldbachCircleMethodActualQ3TriangularOneDimensionalModeReductionV18751
open GoldbachCircleMethodActualQ3WeightedPairConvolutionTransferV18772
open GoldbachCircleMethodOddOddFourierBesselBridgeV18668
open GoldbachCircleMethodActualOddLambdaQ3ResidueDiscrepancyV18752
open GoldbachCircleMethodActualQ3PrefixLocalDensityExtractionV18753

/-- The remaining outer q=3 coefficient is the literal Ramanujan coefficient
at the residue `a - 2n`.  No estimate or sign inference is used. -/
theorem actualQ3OuterUnitPhaseCoefficient_eq_unitCharacterSum
    (n a : Nat) :
    actualQ3OuterUnitPhaseCoefficient n a =
      @unitCharacterSum 3 ⟨by norm_num⟩
        ((((a : Int) - 2 * (n : Int) : Int) : ZMod 3)) := by
  rw [unitCharacterSum_three_eq_two_unit_phases]
  unfold actualQ3OuterUnitPhaseCoefficient
  have harg_one :
      (((((a : Int) - 2 * (n : Int) : Int) : ZMod 3)) * (1 : ZMod 3)) =
        (((-2 * (n : Int) : Int) : ZMod 3) * (1 : ZMod 3)) +
          ((a : ZMod 3) * (1 : ZMod 3)) := by
    push_cast
    ring
  have harg_two :
      (((((a : Int) - 2 * (n : Int) : Int) : ZMod 3)) * (2 : ZMod 3)) =
        (((-2 * (n : Int) : Int) : ZMod 3) * (2 : ZMod 3)) +
          ((a : ZMod 3) * (2 : ZMod 3)) := by
    push_cast
    ring
  rw [harg_one, harg_two, AddChar.map_add_eq_mul,
    AddChar.map_add_eq_mul]

/-- Consequently the outer coefficient is pointwise real and takes only the
values `2` and `-1`.  The zero test is kept in the exact cast/sign convention
of the source term. -/
theorem actualQ3OuterUnitPhaseCoefficient_eq_residueSelector
    (n a : Nat) :
    actualQ3OuterUnitPhaseCoefficient n a =
      if ((((a : Int) - 2 * (n : Int) : Int) : ZMod 3)) = 0
      then 2 else -1 := by
  rw [actualQ3OuterUnitPhaseCoefficient_eq_unitCharacterSum,
    unitCharacterSum_three_eq_if_zero]

theorem actualQ3OuterUnitPhaseCoefficient_im_eq_zero
    (n a : Nat) :
    (actualQ3OuterUnitPhaseCoefficient n a).im = 0 := by
  rw [actualQ3OuterUnitPhaseCoefficient_eq_residueSelector]
  split <;> norm_num

/-- Exact selector form of the actual q=3 weighted pair convolution.  The
sign-changing coefficient is now explicit on the unchanged odd-von-Mangoldt
carrier. -/
theorem actualQ3WeightedPairLocalDensityConvolution_eq_residueSelector
    (M n k : Nat) :
    actualQ3WeightedPairLocalDensityConvolution M n k =
      ∑ a ∈ oddCarrier M,
        ((ArithmeticFunction.vonMangoldt a : Complex) *
          (oddLambdaQ3ResidueMass M (2 * k - a) (0 : ZMod 3) -
            oddLambdaQ3UnitMean M (2 * k - a))) *
          (if ((((a : Int) - 2 * (n : Int) : Int) : ZMod 3)) = 0
            then 2 else -1) := by
  unfold actualQ3WeightedPairLocalDensityConvolution
  simp_rw [actualQ3OuterUnitPhaseCoefficient_eq_residueSelector]

/-- Kernel-checked endpoint of the present gate: the project Sinc/Abel
remainder is an exact Abel transform of a signed `2-or-minus-1` residue selector.
This identity deliberately retains the sign-sensitive correlation. -/
theorem actualQ3LocalDensityTriangularRemainder_eq_residueSelectorAbel
    (M : Nat) (q : PairedOddBase (oddProjectRadius M)) (n : Nat) :
    actualQ3LocalDensityTriangularRemainder M q n =
      -∑ t ∈ Finset.range M,
        selectedPairSourceCoordinateSincVariation M q n t *
          ((∑ a ∈ oddCarrier M,
              ((ArithmeticFunction.vonMangoldt a : Complex) *
                (oddLambdaQ3ResidueMass M (2 * (t + 1) - a) (0 : ZMod 3) -
                  oddLambdaQ3UnitMean M (2 * (t + 1) - a))) *
                (if ((((a : Int) - 2 * (n : Int) : Int) : ZMod 3)) = 0
                  then 2 else -1)) -
            (actualLambdaPairSourceMean M : Complex) *
              q3ConstantPrefix n (t + 1)) := by
  rw [actualQ3LocalDensityTriangularRemainder_eq_weightedPairConvolutionAbel]
  simp_rw [actualQ3WeightedPairLocalDensityConvolution_eq_residueSelector]

end GoldbachCircleMethodActualQ3SincAbelWeightedPairCorrelationDecisionV18773
