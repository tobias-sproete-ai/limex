import GoldbachCircleMethodCCChannelUnitAggregationV18723

/-!
# V1.8.727: exact Ramanujan factorization of the actual mixed channels

This append-only module keeps the two literal unit-mode orientations separate.
The negative mode `-2*u` produces the integer frequency `2*(s-n)`, while the
positive mode `+2*u` produces `2*(n-s)`.  Both atomic identities retain the
unchanged even-target gate, odd--odd source-fiber gate, moving notch, and the
literal two-radius sinc factor before the unit sum is recognized as a
Ramanujan sum.

The resulting identities factor the actual V1.8.720 `ZC` and `CZ` channels
against the already fixed V1.8.723 constant-unit aggregates.  No target or
scale hypothesis is added because all gates remain inside the exact finite
expressions.  No channel is claimed to vanish or be small.

`proof_status = NO_PROOF`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

open scoped BigOperators Classical

namespace GoldbachCircleMethodActualMixedChannelRamanujanFactorizationV18727

open GoldbachCircleMethodTwoScaleEvenBlockDefectReserveV1833
open GoldbachCircleMethodOddOddSignedFiberAdapterV18665
open GoldbachCircleMethodOddChannelEventualAbsorptionV18658
open GoldbachCircleMethodFullDenominatorFourClassPartitionV18688
open GoldbachCircleMethodActualDemodulatedOneFiberRelativeConvolutionV18710
open GoldbachCircleMethodExactLambdaPairSourceMeanSplitV18716
open GoldbachCircleMethodActualMeanSplitFourChannelAggregationV18720
open GoldbachCircleMethodCCChannelUnitAggregationV18723
open GoldbachCircleMethodFiniteResiduePrefixV1866

/-- Unit aggregate of the actual centered transform on the literal negative
mode `-2*u`. -/
noncomputable def selectedPairNegativeCenteredUnitAggregate
    (M : Nat)
    (q : PairedOddBase (oddProjectRadius M))
    (n : Nat) : Complex :=
  ∑ u : ZMod q.val.val,
    if IsUnit u then
      selectedPairCenteredMode M q n
        (-((2 : ZMod q.val.val) * u))
    else 0

/-- Unit aggregate of the actual centered transform on the literal positive
mode `+2*u`. -/
noncomputable def selectedPairPositiveCenteredUnitAggregate
    (M : Nat)
    (q : PairedOddBase (oddProjectRadius M))
    (n : Nat) : Complex :=
  ∑ u : ZMod q.val.val,
    if IsUnit u then
      selectedPairCenteredMode M q n
        ((2 : ZMod q.val.val) * u)
    else 0

/-- The exact negative-mode Ramanujan transform.  The frequency is literally
`2*(s-n)` and all three original Boolean gates remain visible. -/
noncomputable def selectedPairNegativeCenteredRamanujanTransform
    (M : Nat)
    (q : PairedOddBase (oddProjectRadius M))
    (n : Nat) : Complex :=
  ∑ s ∈ Finset.range M.succ,
    (centeredActualLambdaPairSource M s : Complex) *
      (if 2 * n ∈ evenTargetBlock M ∧
          2 * s ∈ oddOddSumCarrier M ∧ 2 * s ≠ 2 * n then
        unitCharacterSum q.val.val
            (((2 * ((s : Int) - (n : Int)) : Int) : ZMod q.val.val)) *
          (selectedPairRelativeTwoRadiusSinc M q n s : Complex)
      else 0)

/-- The exact positive-mode Ramanujan transform.  Its distinct frequency is
literally `2*(n-s)`; no sign-evenness shortcut is used. -/
noncomputable def selectedPairPositiveCenteredRamanujanTransform
    (M : Nat)
    (q : PairedOddBase (oddProjectRadius M))
    (n : Nat) : Complex :=
  ∑ s ∈ Finset.range M.succ,
    (centeredActualLambdaPairSource M s : Complex) *
      (if 2 * n ∈ evenTargetBlock M ∧
          2 * s ∈ oddOddSumCarrier M ∧ 2 * s ≠ 2 * n then
        unitCharacterSum q.val.val
            (((2 * ((n : Int) - (s : Int)) : Int) : ZMod q.val.val)) *
          (selectedPairRelativeTwoRadiusSinc M q n s : Complex)
      else 0)

/-- Atomic negative unit sum.  Recognition as a Ramanujan sum occurs only
after preserving the original `-2*u` phase and the complete gate. -/
theorem sum_unit_selectedPairSourceSeparatedKernel_negative_eq_ramanujan
    (M : Nat)
    (q : PairedOddBase (oddProjectRadius M))
    (n s : Nat) :
    (∑ u : ZMod q.val.val,
      if IsUnit u then
        selectedPairSourceSeparatedKernel M q n
          (-((2 : ZMod q.val.val) * u)) s
      else 0) =
      if 2 * n ∈ evenTargetBlock M ∧
          2 * s ∈ oddOddSumCarrier M ∧ 2 * s ≠ 2 * n then
        unitCharacterSum q.val.val
            (((2 * ((s : Int) - (n : Int)) : Int) : ZMod q.val.val)) *
          (selectedPairRelativeTwoRadiusSinc M q n s : Complex)
      else 0 := by
  by_cases hTarget : 2 * n ∈ evenTargetBlock M
  · by_cases hFiber : 2 * s ∈ oddOddSumCarrier M
    · by_cases hNotch : 2 * s ≠ 2 * n
      · simp only [selectedPairSourceSeparatedKernel]
        simp only [hTarget, hFiber, true_and]
        rw [if_pos hNotch]
        unfold unitCharacterSum
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro u _hu
        by_cases hu : IsUnit u
        · have hNotch' : s * 2 ≠ n * 2 := by
            simpa [Nat.mul_comm] using hNotch
          simp only [hu, if_true]
          push_cast
          ring_nf
          rw [if_pos hNotch']
        · simp [hu]
      · simp [selectedPairSourceSeparatedKernel, hTarget, hFiber, hNotch]
    · simp [selectedPairSourceSeparatedKernel, hTarget, hFiber]
  · simp [selectedPairSourceSeparatedKernel, hTarget]

/-- Atomic positive unit sum with the independently retained frequency
`2*(n-s)`. -/
theorem sum_unit_selectedPairSourceSeparatedKernel_positive_eq_ramanujan
    (M : Nat)
    (q : PairedOddBase (oddProjectRadius M))
    (n s : Nat) :
    (∑ u : ZMod q.val.val,
      if IsUnit u then
        selectedPairSourceSeparatedKernel M q n
          ((2 : ZMod q.val.val) * u) s
      else 0) =
      if 2 * n ∈ evenTargetBlock M ∧
          2 * s ∈ oddOddSumCarrier M ∧ 2 * s ≠ 2 * n then
        unitCharacterSum q.val.val
            (((2 * ((n : Int) - (s : Int)) : Int) : ZMod q.val.val)) *
          (selectedPairRelativeTwoRadiusSinc M q n s : Complex)
      else 0 := by
  by_cases hTarget : 2 * n ∈ evenTargetBlock M
  · by_cases hFiber : 2 * s ∈ oddOddSumCarrier M
    · by_cases hNotch : 2 * s ≠ 2 * n
      · simp only [selectedPairSourceSeparatedKernel]
        simp only [hTarget, hFiber, true_and]
        rw [if_pos hNotch]
        unfold unitCharacterSum
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro u _hu
        by_cases hu : IsUnit u
        · have hNotch' : s * 2 ≠ n * 2 := by
            simpa [Nat.mul_comm] using hNotch
          simp only [hu, if_true]
          push_cast
          ring_nf
          rw [if_pos hNotch']
        · simp [hu]
      · simp [selectedPairSourceSeparatedKernel, hTarget, hFiber, hNotch]
    · simp [selectedPairSourceSeparatedKernel, hTarget, hFiber]
  · simp [selectedPairSourceSeparatedKernel, hTarget]

/-- Exact Ramanujan transform identity for the negative centered aggregate. -/
theorem selectedPairNegativeCenteredUnitAggregate_eq_ramanujanTransform
    (M : Nat)
    (q : PairedOddBase (oddProjectRadius M))
    (n : Nat) :
    selectedPairNegativeCenteredUnitAggregate M q n =
      selectedPairNegativeCenteredRamanujanTransform M q n := by
  unfold selectedPairNegativeCenteredUnitAggregate selectedPairCenteredMode
    centeredActualLambdaPairKernelTransform sourceKernelTransform
    selectedPairNegativeCenteredRamanujanTransform
  calc
    (∑ u : ZMod q.val.val,
        if IsUnit u then
          ∑ s ∈ Finset.range M.succ,
            (centeredActualLambdaPairSource M s : Complex) *
              selectedPairSourceSeparatedKernel M q n
                (-((2 : ZMod q.val.val) * u)) s
        else 0) =
      ∑ u : ZMod q.val.val,
        ∑ s ∈ Finset.range M.succ,
          if IsUnit u then
            (centeredActualLambdaPairSource M s : Complex) *
              selectedPairSourceSeparatedKernel M q n
                (-((2 : ZMod q.val.val) * u)) s
          else 0 := by
      apply Finset.sum_congr rfl
      intro u _hu
      by_cases hu : IsUnit u <;> simp [hu]
    _ = ∑ s ∈ Finset.range M.succ,
        ∑ u : ZMod q.val.val,
          if IsUnit u then
            (centeredActualLambdaPairSource M s : Complex) *
              selectedPairSourceSeparatedKernel M q n
                (-((2 : ZMod q.val.val) * u)) s
          else 0 := by
      simp_rw [Finset.sum_comm (s := Finset.univ)
        (t := Finset.range M.succ)]
    _ = ∑ s ∈ Finset.range M.succ,
        (centeredActualLambdaPairSource M s : Complex) *
          (∑ u : ZMod q.val.val,
            if IsUnit u then
              selectedPairSourceSeparatedKernel M q n
                (-((2 : ZMod q.val.val) * u)) s
            else 0) := by
      apply Finset.sum_congr rfl
      intro s _hs
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro u _hu
      by_cases hu : IsUnit u <;> simp [hu]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro s _hs
      rw [sum_unit_selectedPairSourceSeparatedKernel_negative_eq_ramanujan]

/-- Exact Ramanujan transform identity for the positive centered aggregate. -/
theorem selectedPairPositiveCenteredUnitAggregate_eq_ramanujanTransform
    (M : Nat)
    (q : PairedOddBase (oddProjectRadius M))
    (n : Nat) :
    selectedPairPositiveCenteredUnitAggregate M q n =
      selectedPairPositiveCenteredRamanujanTransform M q n := by
  unfold selectedPairPositiveCenteredUnitAggregate selectedPairCenteredMode
    centeredActualLambdaPairKernelTransform sourceKernelTransform
    selectedPairPositiveCenteredRamanujanTransform
  calc
    (∑ u : ZMod q.val.val,
        if IsUnit u then
          ∑ s ∈ Finset.range M.succ,
            (centeredActualLambdaPairSource M s : Complex) *
              selectedPairSourceSeparatedKernel M q n
                ((2 : ZMod q.val.val) * u) s
        else 0) =
      ∑ u : ZMod q.val.val,
        ∑ s ∈ Finset.range M.succ,
          if IsUnit u then
            (centeredActualLambdaPairSource M s : Complex) *
              selectedPairSourceSeparatedKernel M q n
                ((2 : ZMod q.val.val) * u) s
          else 0 := by
      apply Finset.sum_congr rfl
      intro u _hu
      by_cases hu : IsUnit u <;> simp [hu]
    _ = ∑ s ∈ Finset.range M.succ,
        ∑ u : ZMod q.val.val,
          if IsUnit u then
            (centeredActualLambdaPairSource M s : Complex) *
              selectedPairSourceSeparatedKernel M q n
                ((2 : ZMod q.val.val) * u) s
          else 0 := by
      simp_rw [Finset.sum_comm (s := Finset.univ)
        (t := Finset.range M.succ)]
    _ = ∑ s ∈ Finset.range M.succ,
        (centeredActualLambdaPairSource M s : Complex) *
          (∑ u : ZMod q.val.val,
            if IsUnit u then
              selectedPairSourceSeparatedKernel M q n
                ((2 : ZMod q.val.val) * u) s
            else 0) := by
      apply Finset.sum_congr rfl
      intro s _hs
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro u _hu
      by_cases hu : IsUnit u <;> simp [hu]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro s _hs
      rw [sum_unit_selectedPairSourceSeparatedKernel_positive_eq_ramanujan]

/-- One target slice of the actual `ZC` channel factors into the negative
centered aggregate and the existing positive constant aggregate. -/
theorem sum_unit_selectedPairZCTerm_eq_mul_mixedUnitAggregates
    (M : Nat)
    (q r : PairedOddBase (oddProjectRadius M))
    (n : Nat) :
    (∑ u : ZMod q.val.val,
      ∑ v : ZMod r.val.val,
        if IsUnit u ∧ IsUnit v then
          selectedPairZCTerm M q r n
            (-((2 : ZMod q.val.val) * u))
            ((2 : ZMod r.val.val) * v)
        else 0) =
      selectedPairNegativeCenteredUnitAggregate M q n *
        selectedPairPositiveConstantUnitAggregate M r n := by
  unfold selectedPairNegativeCenteredUnitAggregate
    selectedPairPositiveConstantUnitAggregate selectedPairZCTerm
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro u _hu
  by_cases huu : IsUnit u
  · simp only [huu, true_and, if_true]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v _hv
    by_cases huv : IsUnit v
    · simp [huv]
    · simp [huv]
  · simp [huu]

/-- Exact targetwise factorization of the actual V1.8.720 `ZC` channel. -/
theorem selectedPairZCChannelSum_eq_sum_mixedUnitAggregates
    (M : Nat)
    (q r : PairedOddBase (oddProjectRadius M)) :
    selectedPairZCChannelSum M q r =
      ∑ n ∈ Finset.range M.succ,
        selectedPairNegativeCenteredUnitAggregate M q n *
          selectedPairPositiveConstantUnitAggregate M r n := by
  unfold selectedPairZCChannelSum
  calc
    (∑ u : ZMod q.val.val,
      ∑ v : ZMod r.val.val,
        if IsUnit u ∧ IsUnit v then
          ∑ n ∈ Finset.range M.succ,
            selectedPairZCTerm M q r n
              (-((2 : ZMod q.val.val) * u))
              ((2 : ZMod r.val.val) * v)
        else 0) =
      ∑ u : ZMod q.val.val,
        ∑ v : ZMod r.val.val,
          ∑ n ∈ Finset.range M.succ,
            if IsUnit u ∧ IsUnit v then
              selectedPairZCTerm M q r n
                (-((2 : ZMod q.val.val) * u))
                ((2 : ZMod r.val.val) * v)
            else 0 := by
      apply Finset.sum_congr rfl
      intro u _hu
      apply Finset.sum_congr rfl
      intro v _hv
      by_cases h : IsUnit u ∧ IsUnit v <;> simp [h]
    _ = ∑ n ∈ Finset.range M.succ,
        ∑ u : ZMod q.val.val,
          ∑ v : ZMod r.val.val,
            if IsUnit u ∧ IsUnit v then
              selectedPairZCTerm M q r n
                (-((2 : ZMod q.val.val) * u))
                ((2 : ZMod r.val.val) * v)
            else 0 := by
      simp_rw [Finset.sum_comm (s := Finset.univ)
        (t := Finset.range M.succ)]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro n _hn
      exact sum_unit_selectedPairZCTerm_eq_mul_mixedUnitAggregates M q r n

/-- One target slice of the actual `CZ` channel factors into the existing
negative constant aggregate and the positive centered aggregate. -/
theorem sum_unit_selectedPairCZTerm_eq_mul_mixedUnitAggregates
    (M : Nat)
    (q r : PairedOddBase (oddProjectRadius M))
    (n : Nat) :
    (∑ u : ZMod q.val.val,
      ∑ v : ZMod r.val.val,
        if IsUnit u ∧ IsUnit v then
          selectedPairCZTerm M q r n
            (-((2 : ZMod q.val.val) * u))
            ((2 : ZMod r.val.val) * v)
        else 0) =
      selectedPairNegativeConstantUnitAggregate M q n *
        selectedPairPositiveCenteredUnitAggregate M r n := by
  unfold selectedPairNegativeConstantUnitAggregate
    selectedPairPositiveCenteredUnitAggregate selectedPairCZTerm
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro u _hu
  by_cases huu : IsUnit u
  · simp only [huu, true_and, if_true]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v _hv
    by_cases huv : IsUnit v
    · simp [huv]
    · simp [huv]
  · simp [huu]

/-- Exact targetwise factorization of the actual V1.8.720 `CZ` channel. -/
theorem selectedPairCZChannelSum_eq_sum_mixedUnitAggregates
    (M : Nat)
    (q r : PairedOddBase (oddProjectRadius M)) :
    selectedPairCZChannelSum M q r =
      ∑ n ∈ Finset.range M.succ,
        selectedPairNegativeConstantUnitAggregate M q n *
          selectedPairPositiveCenteredUnitAggregate M r n := by
  unfold selectedPairCZChannelSum
  calc
    (∑ u : ZMod q.val.val,
      ∑ v : ZMod r.val.val,
        if IsUnit u ∧ IsUnit v then
          ∑ n ∈ Finset.range M.succ,
            selectedPairCZTerm M q r n
              (-((2 : ZMod q.val.val) * u))
              ((2 : ZMod r.val.val) * v)
        else 0) =
      ∑ u : ZMod q.val.val,
        ∑ v : ZMod r.val.val,
          ∑ n ∈ Finset.range M.succ,
            if IsUnit u ∧ IsUnit v then
              selectedPairCZTerm M q r n
                (-((2 : ZMod q.val.val) * u))
                ((2 : ZMod r.val.val) * v)
            else 0 := by
      apply Finset.sum_congr rfl
      intro u _hu
      apply Finset.sum_congr rfl
      intro v _hv
      by_cases h : IsUnit u ∧ IsUnit v <;> simp [h]
    _ = ∑ n ∈ Finset.range M.succ,
        ∑ u : ZMod q.val.val,
          ∑ v : ZMod r.val.val,
            if IsUnit u ∧ IsUnit v then
              selectedPairCZTerm M q r n
                (-((2 : ZMod q.val.val) * u))
                ((2 : ZMod r.val.val) * v)
            else 0 := by
      simp_rw [Finset.sum_comm (s := Finset.univ)
        (t := Finset.range M.succ)]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro n _hn
      exact sum_unit_selectedPairCZTerm_eq_mul_mixedUnitAggregates M q r n

end GoldbachCircleMethodActualMixedChannelRamanujanFactorizationV18727
