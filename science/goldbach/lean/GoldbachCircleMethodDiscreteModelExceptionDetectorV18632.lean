import GoldbachCircleMethodActualOvershootTwoChannelV18631

/-!
# V1.8.632: the discrete-model overshoot detects every Goldbach exception

On the fixed even block, the existing prime-power defect reserve and a uniform
`M / 14` lower bound for the unchanged discrete arc model imply that every
non-Goldbach target contributes at least `(M / 28)^2` to the model-overshoot
moment.  Consequently, a strict moment bound below `M^2 / 784` empties the
exception carrier.

This module proves only the reduction.  It supplies neither the model reserve
nor the strict model-overshoot moment estimate.

`proof_status = NO_PROOF`.
-/
set_option autoImplicit false

open scoped BigOperators Classical
open GoldbachPurePrimeAdequacyV15
open GoldbachVonMangoldtDecompositionV16
open GoldbachCircleMethodTwoScaleEvenBlockDefectReserveV1833
open GoldbachCircleMethodDiscreteArcModelReserveV1855
open GoldbachCircleMethodActualOvershootTwoChannelV18631

namespace GoldbachCircleMethodDiscreteModelExceptionDetectorV18632

/-- Without a prime-pair witness, the exact von-Mangoldt convolution equals
the already isolated prime-power defect. -/
theorem vonMangoldtPairSum_eq_primePowerDefect_of_not_goldbachAt
    (N : ℕ) (hNot : ¬ GoldbachAt N) :
    vonMangoldtPairSum N = primePowerDefect N := by
  have hNotPos : ¬ 0 < purePrimeSum N := by
    intro hPos
    exact hNot ((purePrimeSum_pos_iff_strictGoldbach N).mp hPos)
  have hPureNonneg : 0 ≤ purePrimeSum N := by
    unfold purePrimeSum
    exact Finset.sum_nonneg fun p hp => (purePrimeWeight_pos hp).le
  have hPure : purePrimeSum N = 0 :=
    le_antisymm (le_of_not_gt hNotPos) hPureNonneg
  rw [vonMangoldtPairSum_eq_purePrimeSum_add_primePowerDefect, hPure, zero_add]

/-- A non-Goldbach target in the fixed block creates at least `M / 28` of
positive discrete-model overshoot.  The defect remains an explicit
subtrahend. -/
theorem discreteModelOvershoot_ge_M_div_28_of_not_goldbachAt
    (M P R N : ℕ) (hN : N ∈ evenTargetBlock M)
    (hScale : 112 * (Real.log (M : ℝ)) ^ 2 ≤ Real.sqrt (M : ℝ))
    (hModel : (M : ℝ) / 14 ≤ discreteArcMainModel M N R P)
    (hNot : ¬ GoldbachAt N) :
    (M : ℝ) / 28 ≤ discreteModelOvershoot M P R N := by
  have hDefect := evenBlock_defect_reserve M hScale N hN
  have hFull := vonMangoldtPairSum_eq_primePowerDefect_of_not_goldbachAt N hNot
  have hNet :
      (M : ℝ) / 28 ≤ discreteArcMainModel M N R P - vonMangoldtPairSum N := by
    rw [hFull]
    linarith
  unfold discreteModelOvershoot
  exact hNet.trans (le_max_left _ _)

/-- If the squared model-overshoot moment is strictly below the contribution
forced by one exception, the fixed even block contains no exception.  This is
an exact finite decision gate, not an estimate of that moment. -/
theorem evenTargetBlock_exception_filter_eq_empty_of_modelOvershootMoment_lt
    (M P R : ℕ)
    (hScale : 112 * (Real.log (M : ℝ)) ^ 2 ≤ Real.sqrt (M : ℝ))
    (hModel : ∀ N ∈ evenTargetBlock M,
      (M : ℝ) / 14 ≤ discreteArcMainModel M N R P)
    (hMoment :
      discreteModelOvershootSquaredMoment M P R (evenTargetBlock M) <
        (M : ℝ) ^ 2 / 784) :
    (evenTargetBlock M).filter (fun N => ¬ GoldbachAt N) = ∅ := by
  ext N
  constructor
  · intro hNFilter
    have hData := Finset.mem_filter.mp hNFilter
    have hOvershoot :=
      discreteModelOvershoot_ge_M_div_28_of_not_goldbachAt M P R N hData.1
        hScale (hModel N hData.1) hData.2
    have hLeftNonneg : 0 ≤ (M : ℝ) / 28 := by positivity
    have hRightNonneg : 0 ≤ discreteModelOvershoot M P R N := by
      unfold discreteModelOvershoot
      exact le_max_right _ _
    have hSquare :
        ((M : ℝ) / 28) ^ 2 ≤ (discreteModelOvershoot M P R N) ^ 2 := by
      nlinarith [mul_nonneg hLeftNonneg hRightNonneg]
    have hSingle :
        (discreteModelOvershoot M P R N) ^ 2 ≤
          discreteModelOvershootSquaredMoment M P R (evenTargetBlock M) := by
      unfold discreteModelOvershootSquaredMoment
      exact Finset.single_le_sum
        (fun i _ => sq_nonneg (discreteModelOvershoot M P R i)) hData.1
    have hNormalization : ((M : ℝ) / 28) ^ 2 = (M : ℝ) ^ 2 / 784 := by
      ring
    rw [hNormalization] at hSquare
    exfalso
    linarith
  · intro hEmpty
    simp at hEmpty

/-- Effective-threshold wrapper using the already proved scale gate.  The
analytic inputs remain visible in the signature. -/
theorem evenTargetBlock_exception_filter_eq_empty_of_threshold
    (M P R : ℕ) (hLarge : defectScaleThreshold ≤ M)
    (hModel : ∀ N ∈ evenTargetBlock M,
      (M : ℝ) / 14 ≤ discreteArcMainModel M N R P)
    (hMoment :
      discreteModelOvershootSquaredMoment M P R (evenTargetBlock M) <
        (M : ℝ) ^ 2 / 784) :
    (evenTargetBlock M).filter (fun N => ¬ GoldbachAt N) = ∅ := by
  exact evenTargetBlock_exception_filter_eq_empty_of_modelOvershootMoment_lt
    M P R (log_sq_gate_of_threshold_le M hLarge) hModel hMoment

end GoldbachCircleMethodDiscreteModelExceptionDetectorV18632
