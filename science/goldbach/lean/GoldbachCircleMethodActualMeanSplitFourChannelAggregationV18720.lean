import GoldbachCircleMethodExactLambdaPairSourceMeanSplitV18716
import GoldbachCircleMethodActualJointModeCounterModulationV18709
import GoldbachCircleMethodActualSelectedPairJointRawModeIdentityV18707

/-!
# V1.8.720: exact four-channel mean-split aggregation of the actual ordered Gram

This append-only module expands the two definitionally source-bound V1.8.716
mean splits inside the literal V1.8.707/V1.8.709 ordered Gram.  It retains the
actual `-2*a` and `+2*b` unit modes, the original target gates, and the actual
V1.8.716 source-separated kernel.

The four channels are centered--centered (`ZZ`), centered--constant (`ZC`),
constant--centered (`CZ`), and constant--constant (`CC`).  All identities are
finite and exact.  There is no conjugation, absolute-value estimate, smallness
claim, freely chosen main fiber, moment theorem, exceptional-set theorem, or
Goldbach conclusion.

`proof_status = NO_PROOF`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

open scoped BigOperators Classical ComplexConjugate

namespace GoldbachCircleMethodActualMeanSplitFourChannelAggregationV18720

open GoldbachCircleMethodTwoScaleEvenBlockDefectReserveV1833
open GoldbachCircleMethodOddChannelEventualAbsorptionV18658
open GoldbachCircleMethodFullDenominatorFourClassPartitionV18688
open GoldbachCircleMethodFullChannelPartitionedGramV18689
open GoldbachCircleMethodActualSelectedPairJointRawModeIdentityV18707
open GoldbachCircleMethodActualJointModeCounterModulationV18709
open GoldbachCircleMethodExactLambdaPairSourceMeanSplitV18716

/-- The centered part of one literal counter-modulated V1.8.709 mode. -/
noncomputable def selectedPairCenteredMode
    (M : Nat)
    (q : PairedOddBase (oddProjectRadius M))
    (n : Nat) (xi : ZMod q.val.val) : Complex :=
  centeredActualLambdaPairKernelTransform M
    (selectedPairSourceSeparatedKernel M q n xi)

/-- The constant part of one literal counter-modulated V1.8.709 mode. -/
noncomputable def selectedPairConstantMode
    (M : Nat)
    (q : PairedOddBase (oddProjectRadius M))
    (n : Nat) (xi : ZMod q.val.val) : Complex :=
  actualLambdaPairConstantKernelTransform M
    (selectedPairSourceSeparatedKernel M q n xi)

/-- Centered--centered channel at one target coordinate and two unchanged
base modes. -/
noncomputable def selectedPairZZTerm
    (M : Nat)
    (q r : PairedOddBase (oddProjectRadius M))
    (n : Nat) (xi : ZMod q.val.val) (eta : ZMod r.val.val) : Complex :=
  selectedPairCenteredMode M q n xi * selectedPairCenteredMode M r n eta

/-- Centered--constant channel at one target coordinate. -/
noncomputable def selectedPairZCTerm
    (M : Nat)
    (q r : PairedOddBase (oddProjectRadius M))
    (n : Nat) (xi : ZMod q.val.val) (eta : ZMod r.val.val) : Complex :=
  selectedPairCenteredMode M q n xi * selectedPairConstantMode M r n eta

/-- Constant--centered channel at one target coordinate. -/
noncomputable def selectedPairCZTerm
    (M : Nat)
    (q r : PairedOddBase (oddProjectRadius M))
    (n : Nat) (xi : ZMod q.val.val) (eta : ZMod r.val.val) : Complex :=
  selectedPairConstantMode M q n xi * selectedPairCenteredMode M r n eta

/-- Constant--constant channel at one target coordinate. -/
noncomputable def selectedPairCCTerm
    (M : Nat)
    (q r : PairedOddBase (oddProjectRadius M))
    (n : Nat) (xi : ZMod q.val.val) (eta : ZMod r.val.val) : Complex :=
  selectedPairConstantMode M q n xi * selectedPairConstantMode M r n eta

/-- Exact product expansion of two actual counter-modulated modes into the
four source-mean channels.  Neither factor is conjugated. -/
theorem selectedPairDemodulatedProduct_eq_four_channels
    (M : Nat)
    (q r : PairedOddBase (oddProjectRadius M))
    (n : Nat) (xi : ZMod q.val.val) (eta : ZMod r.val.val) :
    selectedPairOneFiberDemodulatedRawPhaseSum M q n xi *
        selectedPairOneFiberDemodulatedRawPhaseSum M r n eta =
      selectedPairZZTerm M q r n xi eta +
        selectedPairZCTerm M q r n xi eta +
        selectedPairCZTerm M q r n xi eta +
        selectedPairCCTerm M q r n xi eta := by
  rw [selectedPairOneFiberDemodulatedRawPhaseSum_eq_centered_add_constant]
  rw [selectedPairOneFiberDemodulatedRawPhaseSum_eq_centered_add_constant]
  unfold selectedPairZZTerm selectedPairZCTerm selectedPairCZTerm
    selectedPairCCTerm selectedPairCenteredMode selectedPairConstantMode
  ring

/-- The sum of all four channels for one pair of unchanged base modes. -/
noncomputable def selectedPairFourChannelModeSum
    (M : Nat)
    (q r : PairedOddBase (oddProjectRadius M))
    (xi : ZMod q.val.val) (eta : ZMod r.val.val) : Complex :=
  ∑ n ∈ Finset.range M.succ,
    (selectedPairZZTerm M q r n xi eta +
      selectedPairZCTerm M q r n xi eta +
      selectedPairCZTerm M q r n xi eta +
      selectedPairCCTerm M q r n xi eta)

/-- On the literal unit modes used by V1.8.707, one joint raw mode is exactly
the sum of the four actual source-mean channels. -/
theorem selectedPairJointRawMode_unit_eq_fourChannelModeSum
    (M : Nat)
    (q r : PairedOddBase (oddProjectRadius M))
    (a : ZMod q.val.val) (b : ZMod r.val.val)
    (ha : IsUnit a) (hb : IsUnit b) :
    selectedPairJointRawMode M q r
        (-((2 : ZMod q.val.val) * a))
        ((2 : ZMod r.val.val) * b)
        (coupledTargetFrequency q r
          (-((2 : ZMod q.val.val) * a))
          ((2 : ZMod r.val.val) * b)) =
      selectedPairFourChannelModeSum M q r
        (-((2 : ZMod q.val.val) * a))
        ((2 : ZMod r.val.val) * b) := by
  rw [selectedPairJointRawMode_unit_mode_counter_modulation M q r a b ha hb]
  unfold selectedPairFourChannelModeSum
  apply Finset.sum_congr rfl
  intro n _hn
  exact selectedPairDemodulatedProduct_eq_four_channels M q r n _ _

/-- Pair-local `ZZ` aggregation over the unchanged `-2*a`, `+2*b` unit
character carrier. -/
noncomputable def selectedPairZZChannelSum
    (M : Nat)
    (q r : PairedOddBase (oddProjectRadius M)) : Complex :=
  ∑ a : ZMod q.val.val,
    ∑ b : ZMod r.val.val,
      if IsUnit a ∧ IsUnit b then
        ∑ n ∈ Finset.range M.succ,
          selectedPairZZTerm M q r n
            (-((2 : ZMod q.val.val) * a))
            ((2 : ZMod r.val.val) * b)
      else 0

/-- Pair-local `ZC` aggregation on the same carrier. -/
noncomputable def selectedPairZCChannelSum
    (M : Nat)
    (q r : PairedOddBase (oddProjectRadius M)) : Complex :=
  ∑ a : ZMod q.val.val,
    ∑ b : ZMod r.val.val,
      if IsUnit a ∧ IsUnit b then
        ∑ n ∈ Finset.range M.succ,
          selectedPairZCTerm M q r n
            (-((2 : ZMod q.val.val) * a))
            ((2 : ZMod r.val.val) * b)
      else 0

/-- Pair-local `CZ` aggregation on the same carrier. -/
noncomputable def selectedPairCZChannelSum
    (M : Nat)
    (q r : PairedOddBase (oddProjectRadius M)) : Complex :=
  ∑ a : ZMod q.val.val,
    ∑ b : ZMod r.val.val,
      if IsUnit a ∧ IsUnit b then
        ∑ n ∈ Finset.range M.succ,
          selectedPairCZTerm M q r n
            (-((2 : ZMod q.val.val) * a))
            ((2 : ZMod r.val.val) * b)
      else 0

/-- Pair-local `CC` aggregation on the same carrier. -/
noncomputable def selectedPairCCChannelSum
    (M : Nat)
    (q r : PairedOddBase (oddProjectRadius M)) : Complex :=
  ∑ a : ZMod q.val.val,
    ∑ b : ZMod r.val.val,
      if IsUnit a ∧ IsUnit b then
        ∑ n ∈ Finset.range M.succ,
          selectedPairCCTerm M q r n
            (-((2 : ZMod q.val.val) * a))
            ((2 : ZMod r.val.val) * b)
      else 0

/-- Exact aggregation of the literal V1.8.707 pair sum into the four actual
source-mean channels. -/
theorem selectedPairCoupledJointRawModeSum_eq_four_channels
    (M : Nat)
    (q r : PairedOddBase (oddProjectRadius M)) :
    selectedPairCoupledJointRawModeSum M q r =
      selectedPairZZChannelSum M q r + selectedPairZCChannelSum M q r +
        selectedPairCZChannelSum M q r + selectedPairCCChannelSum M q r := by
  unfold selectedPairCoupledJointRawModeSum selectedPairZZChannelSum
    selectedPairZCChannelSum selectedPairCZChannelSum selectedPairCCChannelSum
  simp only [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _ha
  apply Finset.sum_congr rfl
  intro b _hb
  by_cases ha : IsUnit a
  · by_cases hb : IsUnit b
    · simp only [ha, hb, and_self, if_true]
      rw [selectedPairJointRawMode_unit_eq_fourChannelModeSum M q r a b ha hb]
      unfold selectedPairFourChannelModeSum
      simp only [Finset.sum_add_distrib]
    · simp [ha, hb]
  · simp [ha]

/-- The actual V1.8.707 ordered off-diagonal Gram is exactly the complete
ordered `q,r` aggregation of `ZZ + ZC + CZ + CC`. -/
theorem ofReal_orderedOffDiagonalGram_eq_four_channel_aggregation
    (M : Nat) :
    (orderedOffDiagonalGram (evenTargetBlock M)
        (projectPairedBaseContribution M) : Complex) =
      ∑ q : PairedOddBase (oddProjectRadius M),
        ∑ r ∈ Finset.univ.erase q,
          (selectedPairZZChannelSum M q r + selectedPairZCChannelSum M q r +
            selectedPairCZChannelSum M q r + selectedPairCCChannelSum M q r) := by
  rw [ofReal_orderedOffDiagonalGram_eq_coupledJointRawModeSums]
  apply Finset.sum_congr rfl
  intro q _hq
  apply Finset.sum_congr rfl
  intro r _hr
  exact selectedPairCoupledJointRawModeSum_eq_four_channels M q r

end GoldbachCircleMethodActualMeanSplitFourChannelAggregationV18720
