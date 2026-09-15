import GoldbachCircleMethodHighMinorBudgetV1822

/-!
# Finite one-sided exceptional-set transfer, V1.8.23

This module proves the finite Markov/cardinality mechanism needed by a future
Class-II exceptional-set argument.  It also proves the pointwise bridge from
the concrete V1.8.22 high-denominator integral to the `2 / 35` bad threshold.
It does not supply an analytic moment estimate or the still-missing
common-scale operator family needed to sum that estimate uniformly over `N`.

The threshold is the exact rational reserve `2 / 35`.  The analytic moment
bound is passed to the final theorem as an ordinary local hypothesis; it is
not installed as an axiom, global instance, or fabricated witness.
-/

set_option autoImplicit false

namespace GoldbachCircleMethodExceptionalTransferV1823

open scoped BigOperators
open GoldbachPurePrimeAdequacyV15
open GoldbachVonMangoldtDecompositionV16
open GoldbachPrimePowerDefectBoundV161
open GoldbachCircleMethodMajorMinorPartitionV172
open GoldbachCircleMethodHighMinorBudgetV1822

/-- The one-sided deficit detected by a negative-tail argument. -/
def negativePart (x : Real) : Real := max (-x) 0

/-- Exact rational threshold inherited from the V1.8.21 budget split. -/
noncomputable def classIIThreshold : Real := (2 : Real) / 35

theorem classIIThreshold_pos : 0 < classIIThreshold := by
  norm_num [classIIThreshold]

/-- Indices on which the abstract high-band value breaches the `2/35` reserve. -/
noncomputable def badIndices {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (H : ι → Real) (X : Real) : Finset ι :=
  s.filter (fun i => H i ≤ -(classIIThreshold * X))

/-- The finite negative-part second moment. -/
def negativePartSquaredMoment {ι : Type*}
    (s : Finset ι) (H : ι → Real) : Real :=
  ∑ i ∈ s, (negativePart (H i)) ^ 2

theorem negativePartSquaredMoment_nonneg {ι : Type*}
    (s : Finset ι) (H : ι → Real) :
    0 ≤ negativePartSquaredMoment s H := by
  unfold negativePartSquaredMoment
  positivity

/-- Every bad index contributes at least the squared threshold to the moment. -/
theorem threshold_sq_le_negativePart_sq_of_mem_bad
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (H : ι → Real) (X : Real) (hX : 0 < X)
    (i : ι) (hi : i ∈ badIndices s H X) :
    (classIIThreshold * X) ^ 2 ≤ (negativePart (H i)) ^ 2 := by
  have hBad : H i ≤ -(classIIThreshold * X) :=
    (Finset.mem_filter.mp hi).2
  have hThresholdNonneg : 0 ≤ classIIThreshold * X :=
    le_of_lt (mul_pos classIIThreshold_pos hX)
  have hThresholdLe : classIIThreshold * X ≤ negativePart (H i) := by
    unfold negativePart
    exact (by linarith : classIIThreshold * X ≤ -H i) |>.trans
      (le_max_left (-H i) 0)
  have hNegativePartNonneg : 0 ≤ negativePart (H i) := by
    unfold negativePart
    exact le_max_right (-H i) 0
  nlinarith

/--
Finite one-sided Markov core: the number of bad indices times the squared
reserve is bounded by the full negative-part second moment.
-/
theorem bad_card_mul_threshold_sq_le_moment
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (H : ι → Real) (X : Real) (hX : 0 < X) :
    ((badIndices s H X).card : Real) * (classIIThreshold * X) ^ 2 ≤
      negativePartSquaredMoment s H := by
  classical
  calc
    ((badIndices s H X).card : Real) * (classIIThreshold * X) ^ 2 =
        ∑ _i ∈ badIndices s H X, (classIIThreshold * X) ^ 2 := by simp
    _ ≤ ∑ i ∈ badIndices s H X, (negativePart (H i)) ^ 2 := by
      exact Finset.sum_le_sum fun i hi =>
        threshold_sq_le_negativePart_sq_of_mem_bad s H X hX i hi
    _ ≤ ∑ i ∈ s, (negativePart (H i)) ^ 2 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.filter_subset _ _
      · intro i _ _
        exact sq_nonneg (negativePart (H i))
    _ = negativePartSquaredMoment s H := rfl

/--
Conditional cardinality transfer.  `hMoment` is the still-open analytic input,
kept as a local parameter.  The conclusion is a real-valued cardinality bound.
-/
theorem bad_card_le_of_negativePart_moment
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (H : ι → Real) (X M : Real)
    (hX : 0 < X)
    (hMoment : negativePartSquaredMoment s H ≤ M) :
    ((badIndices s H X).card : Real) ≤
      M / (classIIThreshold * X) ^ 2 := by
  have hThresholdPos : 0 < classIIThreshold * X :=
    mul_pos classIIThreshold_pos hX
  have hSquarePos : 0 < (classIIThreshold * X) ^ 2 := sq_pos_of_pos hThresholdPos
  apply (le_div_iff₀ hSquarePos).2
  exact (bad_card_mul_threshold_sq_le_moment s H X hX).trans hMoment

/-- Exact lower-band coefficient used by the V1.8.21 budget split. -/
noncomputable def lowerBandThreshold : Real := (4 : Real) / 35

theorem lowerBandThreshold_pos : 0 < lowerBandThreshold := by
  norm_num [lowerBandThreshold]

/--
Concrete pointwise bridge into the abstract bad-index threshold.

If `N` is not a Goldbach number, V1.8.22's exact target restatement forces the
concrete high-band integral below `defect - lower`.  Combining the actual
V1.6.1 defect ceiling, a `4/35` lower-band bound, and the explicit `2/35`
reserve yields the one-sided bad threshold.  This theorem provides no lower
band estimate and no moment estimate; both remain hypotheses at their proper
interfaces.
-/
theorem not_goldbachAt_implies_highIntegralReal_le_negative_threshold
    (p : ArcParameters) (Q U : Nat) (E_L : Real)
    (hN : 1 ≤ p.N)
    (hNotGoldbach : ¬ GoldbachAt p.N)
    (hLower :
      lowerBandThreshold * (p.N : Real) - E_L ≤
        lowerIntegralReal p Q U)
    (hReserve :
      E_L +
          4 * Real.sqrt (p.N : Real) * (Real.log (p.N : Real)) ^ 2 ≤
        classIIThreshold * (p.N : Real)) :
    highIntegralReal p Q U ≤
      -(classIIThreshold * (p.N : Real)) := by
  have hHighNotGt :
      ¬ highIntegralReal p Q U >
          primePowerDefect p.N - lowerIntegralReal p Q U := by
    intro hHigh
    exact hNotGoldbach
      ((goldbachAt_iff_high_gt_defect_sub_lower p Q U).2 hHigh)
  have hHighLe :
      highIntegralReal p Q U ≤
        primePowerDefect p.N - lowerIntegralReal p Q U :=
    le_of_not_gt hHighNotGt
  have hDefect := primePowerDefect_le_four_sqrt_mul_log_sq hN
  have hThresholdIdentity :
      lowerBandThreshold = 2 * classIIThreshold := by
    norm_num [lowerBandThreshold, classIIThreshold]
  rw [hThresholdIdentity] at hLower
  linarith

/-- Exact real-valued dyadic-block convention used by the uniform threshold. -/
def InDyadicBlockXTwoX (X N : Real) : Prop := X ≤ N ∧ N ≤ 2 * X

/--
On the block `[X, 2X]`, a pointwise `-(2/35)N` upper bound implies the
uniform `-(2/35)X` upper bound used by the finite Markov theorem.
-/
theorem negative_threshold_transfer_on_dyadicBlock_X_twoX
    (X N H : Real)
    (hBlock : InDyadicBlockXTwoX X N)
    (hPointwise : H ≤ -(classIIThreshold * N)) :
    H ≤ -(classIIThreshold * X) := by
  have hThresholdNonneg : 0 ≤ classIIThreshold :=
    le_of_lt classIIThreshold_pos
  have hScaled : classIIThreshold * X ≤ classIIThreshold * N :=
    mul_le_mul_of_nonneg_left hBlock.1 hThresholdNonneg
  linarith

/--
Concrete dyadic corollary for the actual V1.8.22 operator.  This fixes the
common-threshold convention to `N ∈ [X, 2X]`; it must not be reused for the
different block convention `[X/2, X]`, whose common coefficient would be
`1/35` rather than `2/35`.
-/
theorem not_goldbachAt_on_dyadicBlock_X_twoX_implies_uniform_high_threshold
    (p : ArcParameters) (Q U : Nat) (E_L X : Real)
    (hN : 1 ≤ p.N)
    (hBlock : InDyadicBlockXTwoX X (p.N : Real))
    (hNotGoldbach : ¬ GoldbachAt p.N)
    (hLower :
      lowerBandThreshold * (p.N : Real) - E_L ≤
        lowerIntegralReal p Q U)
    (hReserve :
      E_L +
          4 * Real.sqrt (p.N : Real) * (Real.log (p.N : Real)) ^ 2 ≤
        classIIThreshold * (p.N : Real)) :
    highIntegralReal p Q U ≤ -(classIIThreshold * X) := by
  apply negative_threshold_transfer_on_dyadicBlock_X_twoX
    X (p.N : Real) (highIntegralReal p Q U) hBlock
  exact not_goldbachAt_implies_highIntegralReal_le_negative_threshold
    p Q U E_L hN hNotGoldbach hLower hReserve

end GoldbachCircleMethodExceptionalTransferV1823
