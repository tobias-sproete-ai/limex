import GoldbachCircleMethodActualMeanSplitFourChannelAggregationV18720

/-!
# V1.8.723: exact signed unit-mode factorization of the actual CC channel

This append-only module does not estimate the constant--constant channel.  It
reorders the actual finite V1.8.720 carrier exactly and factors each target
slice into the product of the negative and positive unit-character constant
mode aggregates.  The signs `-2*a` and `+2*b` remain distinct.

No triangle inequality, smallness claim, centered-channel estimate, residual
estimate, moment theorem, exceptional-set theorem, or Goldbach conclusion is
introduced.

`proof_status = NO_PROOF`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

open scoped BigOperators Classical

namespace GoldbachCircleMethodCCChannelUnitAggregationV18723

open GoldbachCircleMethodOddChannelEventualAbsorptionV18658
open GoldbachCircleMethodFullDenominatorFourClassPartitionV18688
open GoldbachCircleMethodActualMeanSplitFourChannelAggregationV18720

/-- The unit-character aggregate of the actual constant mode at one target. -/
noncomputable def selectedPairNegativeConstantUnitAggregate
    (M : Nat)
    (q : PairedOddBase (oddProjectRadius M))
    (n : Nat) : Complex :=
  ∑ a : ZMod q.val.val,
    if IsUnit a then
      selectedPairConstantMode M q n
        (-((2 : ZMod q.val.val) * a))
    else 0

/-- The positive unit-character aggregate used by the second base mode. -/
noncomputable def selectedPairPositiveConstantUnitAggregate
    (M : Nat)
    (q : PairedOddBase (oddProjectRadius M))
    (n : Nat) : Complex :=
  ∑ a : ZMod q.val.val,
    if IsUnit a then
      selectedPairConstantMode M q n
        ((2 : ZMod q.val.val) * a)
    else 0

/-- Exact factorization of the two-dimensional unit carrier at one target. -/
theorem sum_unit_selectedPairCCTerm_eq_mul_constantUnitAggregates
    (M : Nat)
    (q r : PairedOddBase (oddProjectRadius M))
    (n : Nat) :
    (∑ a : ZMod q.val.val,
      ∑ b : ZMod r.val.val,
        if IsUnit a ∧ IsUnit b then
          selectedPairCCTerm M q r n
            (-((2 : ZMod q.val.val) * a))
            ((2 : ZMod r.val.val) * b)
        else 0) =
      selectedPairNegativeConstantUnitAggregate M q n *
        selectedPairPositiveConstantUnitAggregate M r n := by
  unfold selectedPairNegativeConstantUnitAggregate
    selectedPairPositiveConstantUnitAggregate selectedPairCCTerm
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _ha
  by_cases hua : IsUnit a
  · simp only [hua, true_and, if_true]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _hb
    by_cases hub : IsUnit b
    · simp [hub]
    · simp [hub]
  · simp [hua]

/-- Exact targetwise factorization of the actual V1.8.720 CC channel. -/
theorem selectedPairCCChannelSum_eq_sum_constantUnitAggregates
    (M : Nat)
    (q r : PairedOddBase (oddProjectRadius M)) :
    selectedPairCCChannelSum M q r =
      ∑ n ∈ Finset.range M.succ,
        selectedPairNegativeConstantUnitAggregate M q n *
          selectedPairPositiveConstantUnitAggregate M r n := by
  unfold selectedPairCCChannelSum
  calc
    (∑ a : ZMod q.val.val,
      ∑ b : ZMod r.val.val,
        if IsUnit a ∧ IsUnit b then
          ∑ n ∈ Finset.range M.succ,
            selectedPairCCTerm M q r n
              (-((2 : ZMod q.val.val) * a))
              ((2 : ZMod r.val.val) * b)
        else 0) =
      ∑ a : ZMod q.val.val,
        ∑ b : ZMod r.val.val,
          ∑ n ∈ Finset.range M.succ,
            if IsUnit a ∧ IsUnit b then
              selectedPairCCTerm M q r n
                (-((2 : ZMod q.val.val) * a))
                ((2 : ZMod r.val.val) * b)
            else 0 := by
      apply Finset.sum_congr rfl
      intro a _ha
      apply Finset.sum_congr rfl
      intro b _hb
      by_cases h : IsUnit a ∧ IsUnit b <;> simp [h]
    _ =
      ∑ n ∈ Finset.range M.succ,
        ∑ a : ZMod q.val.val,
          ∑ b : ZMod r.val.val,
            if IsUnit a ∧ IsUnit b then
              selectedPairCCTerm M q r n
                (-((2 : ZMod q.val.val) * a))
                ((2 : ZMod r.val.val) * b)
            else 0 := by
      simp_rw [Finset.sum_comm (s := Finset.univ)
        (t := Finset.range M.succ)]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro n _hn
      exact sum_unit_selectedPairCCTerm_eq_mul_constantUnitAggregates M q r n

end GoldbachCircleMethodCCChannelUnitAggregationV18723
