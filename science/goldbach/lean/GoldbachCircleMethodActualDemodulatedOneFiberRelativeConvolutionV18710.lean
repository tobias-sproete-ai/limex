import GoldbachCircleMethodActualJointModeCounterModulationV18709

/-!
# V1.8.710: exact relative-convolution form of one actual demodulated fiber

This append-only module expands the literal V1.8.709 demodulated raw mode all
the way back to the actual odd--odd pair-fiber mass and the two original sinc
radii belonging to the selected odd/double denominator pair.

The signed relative coordinate is kept in `Int`.  Consequently the expression
does not truncate when the fiber index exceeds the target half-index.  The
original even target gate, odd--odd fiber gate, moving notch, finite carrier,
arithmetic mass, and both denominator radii are retained exactly.

The result is an exact finite convolution-like identity.  It proves no
positivity, cancellation, variation estimate, dispersion bound, moment
estimate, exceptional-set estimate, or Goldbach conclusion.

`proof_status = NO_PROOF`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

open scoped BigOperators Classical

namespace GoldbachCircleMethodActualDemodulatedOneFiberRelativeConvolutionV18710

open GoldbachCircleMethodTwoScaleEvenBlockDefectReserveV1833
open GoldbachCircleMethodOddOddSignedFiberAdapterV18665
open GoldbachCircleMethodOddDoubleSincPairV18678
open GoldbachCircleMethodOddChannelEventualAbsorptionV18658
open GoldbachCircleMethodFullDenominatorFourClassPartitionV18688
open GoldbachCircleMethodSelectedPairLocalPeriodAbelAdapterV18691
open GoldbachCircleMethodSelectedPairSignedResidueWeightExactOneDimensionalFactorizationV18698
open GoldbachCircleMethodActualOneFiberDFTRawPhaseSumV18705
open GoldbachCircleMethodActualJointModeCounterModulationV18709

/-- The signed step-two displacement between target `2*n` and fiber `2*a`.
Using `Int` is essential: natural subtraction would erase the negative branch
when `a > n`. -/
def selectedPairRelativeStepTwoCoordinate (n a : Nat) : Int :=
  2 * ((n : Int) - (a : Int))

/-- The exact two-radius real sinc factor at the signed relative coordinate.
No radius is replaced or merged. -/
noncomputable def selectedPairRelativeTwoRadiusSinc
    (M : Nat)
    (q : PairedOddBase (oddProjectRadius M))
    (n a : Nat) : Real :=
  (explicitSincRadiusFactor M
      (oddProjectWidth M) (oddProjectRadius M)
      (selectedPairRelativeStepTwoCoordinate n a) q.val +
    explicitSincRadiusFactor M
      (oddProjectWidth M) (oddProjectRadius M)
      (selectedPairRelativeStepTwoCoordinate n a)
      (pairedDoubleDenominator q)).re

/-- The actual arithmetic fiber mass multiplied by the two literal selected
denominator radii. -/
noncomputable def selectedPairRelativeSincFiberWeight
    (M : Nat)
    (q : PairedOddBase (oddProjectRadius M))
    (n a : Nat) : Real :=
  oddOddPairFiberMass M (2 * a) *
    selectedPairRelativeTwoRadiusSinc M q n a

/-- One exact relative-convolution summand.  The Boolean gate is literally the
V1.8.698 target/fiber/notch gate, while the phase and both sinc radii depend
only on the signed relative displacement. -/
noncomputable def selectedPairOneFiberRelativeConvolutionTerm
    (M : Nat)
    (q : PairedOddBase (oddProjectRadius M))
    (n : Nat) (xi : ZMod q.val.val) (a : Nat) : Complex :=
  if 2 * n ∈ evenTargetBlock M ∧
      2 * a ∈ oddOddSumCarrier M ∧ 2 * a ≠ 2 * n then
    ZMod.stdAddChar
        (((((n : Int) - (a : Int)) : Int) : ZMod q.val.val) * xi) *
      (selectedPairRelativeSincFiberWeight M q n a : Complex)
  else 0

/-- The natural target/fiber subtraction occurring in the inherited exact
weight is exactly the signed step-two coordinate. -/
theorem int_two_mul_sub_eq_selectedPairRelativeStepTwoCoordinate
    (n a : Nat) :
    ((2 * n : Nat) : Int) - ((2 * a : Nat) : Int) =
      selectedPairRelativeStepTwoCoordinate n a := by
  unfold selectedPairRelativeStepTwoCoordinate
  push_cast
  ring

/-- The literal V1.8.698 halfweight is exactly the actual fiber mass times the
sum of both original sinc radius factors at signed displacement `2*(n-a)`.
All three inherited gates remain syntactically visible. -/
theorem selectedPairOneFiberHalfWeight_eq_if_relativeSincFiberWeight
    (M : Nat)
    (q : PairedOddBase (oddProjectRadius M))
    (n a : Nat) :
    selectedPairOneFiberHalfWeight M q n a =
      if 2 * n ∈ evenTargetBlock M ∧
          2 * a ∈ oddOddSumCarrier M ∧ 2 * a ≠ 2 * n then
        selectedPairRelativeSincFiberWeight M q n a
      else 0 := by
  unfold selectedPairOneFiberHalfWeight selectedPairRelativeSincFiberWeight
    selectedPairRelativeTwoRadiusSinc selectedPairExactSincFiberWeight
  rw [int_two_mul_sub_eq_selectedPairRelativeStepTwoCoordinate]

/-- Exact finite relative-convolution normal form of the actual demodulated
one-fiber raw phase sum.  Neither the phase nor the sinc factors lose the
negative-displacement branch. -/
theorem selectedPairOneFiberDemodulatedRawPhaseSum_eq_relativeConvolution
    (M : Nat)
    (q : PairedOddBase (oddProjectRadius M))
    (n : Nat) (xi : ZMod q.val.val) :
    selectedPairOneFiberDemodulatedRawPhaseSum M q n xi =
      ∑ a ∈ Finset.range M.succ,
        selectedPairOneFiberRelativeConvolutionTerm M q n xi a := by
  rw [selectedPairOneFiberDemodulatedRawPhaseSum_eq_relativePhaseSum]
  apply Finset.sum_congr rfl
  intro a _ha
  rw [selectedPairOneFiberHalfWeight_eq_if_relativeSincFiberWeight]
  unfold selectedPairOneFiberRelativeConvolutionTerm
  by_cases hN : 2 * n ∈ evenTargetBlock M
    <;> by_cases haCarrier : 2 * a ∈ oddOddSumCarrier M
    <;> by_cases haNotch : 2 * a ≠ 2 * n
    <;> simp [hN, haCarrier, haNotch]

end GoldbachCircleMethodActualDemodulatedOneFiberRelativeConvolutionV18710
