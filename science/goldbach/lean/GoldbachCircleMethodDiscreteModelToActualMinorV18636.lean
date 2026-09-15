import GoldbachCircleMethodDiscreteModelExceptionCountTransferV18635

/-!
# V1.8.636: discrete-model overshoot controlled by the actual minor channel

The positive overshoot of the fixed discrete Major model above the full
von-Mangoldt coefficient is bounded pointwise by two already declared
quantities: the literal Major-operator approximation error and the negative
part of the actual Minor coefficient.  Summing the squared inequality gives a
finite moment transfer, and composing it with V1.8.635 turns those two actual
channels into a quantitative Goldbach-exception count bound.

This module changes no operator and supplies no analytic estimate for either
channel.  In particular it does not prove a minor-arc moment bound, the uniform
discrete-model reserve, or Goldbach.

`proof_status = NO_PROOF`.
-/
set_option autoImplicit false

open scoped BigOperators Classical
open GoldbachPurePrimeAdequacyV15
open GoldbachVonMangoldtDecompositionV16
open GoldbachCircleMethodExceptionalTransferV1823
open GoldbachCircleMethodTwoScaleIntegralPartitionV1831
open GoldbachCircleMethodTwoScaleEvenBlockDefectReserveV1833
open GoldbachCircleMethodDiscreteArcModelReserveV1855
open GoldbachCircleMethodActualOvershootTwoChannelV18631
open GoldbachCircleMethodDiscreteModelExceptionCountTransferV18635

namespace GoldbachCircleMethodDiscreteModelToActualMinorV18636

/-- On the literal coefficient range, any positive overshoot of the discrete
Major model above the full arithmetic coefficient is paid for by the literal
Major-operator approximation error and/or the negative actual Minor
coefficient.  This is an exact order reduction, not an estimate. -/
theorem discreteModelOvershoot_le_operatorError_add_negativeMinor
    (M P R N : ℕ) (hNM : N ≤ M) :
    discreteModelOvershoot M P R N ≤
      operatorApproximationError M P R N +
        negativePart (twoScaleMinorIntegralReal M P R N) := by
  have hBalance := twoScaleMajor_add_minor_eq_vonMangoldtPairSum M P R N hNM
  unfold discreteModelOvershoot operatorApproximationError negativePart
  apply max_le
  · have hOperator :
        discreteArcMainModel M N R P - twoScaleMajorIntegralReal M P R N ≤
          |twoScaleMajorIntegralReal M P R N - discreteArcMainModel M N R P| := by
      simpa [abs_sub_comm] using
        (le_abs_self
          (discreteArcMainModel M N R P - twoScaleMajorIntegralReal M P R N))
    have hMinor :
        -twoScaleMinorIntegralReal M P R N ≤
          max (-twoScaleMinorIntegralReal M P R N) 0 :=
      le_max_left _ _
    linarith
  · exact add_nonneg (abs_nonneg _) (le_max_right _ _)

/-- Squared pointwise transfer with the exact elementary factor two. -/
theorem discreteModelOvershoot_sq_le_actual_channels
    (M P R N : ℕ) (hNM : N ≤ M) :
    (discreteModelOvershoot M P R N) ^ 2 ≤
      2 * (operatorApproximationError M P R N) ^ 2 +
        2 * (negativePart (twoScaleMinorIntegralReal M P R N)) ^ 2 := by
  have hle :=
    discreteModelOvershoot_le_operatorError_add_negativeMinor M P R N hNM
  have hx : 0 ≤ discreteModelOvershoot M P R N := by
    unfold discreteModelOvershoot
    exact le_max_right _ _
  have ha : 0 ≤ operatorApproximationError M P R N := by
    unfold operatorApproximationError
    exact abs_nonneg _
  have hb : 0 ≤ negativePart (twoScaleMinorIntegralReal M P R N) := by
    unfold negativePart
    exact le_max_right _ _
  have hprod : 0 ≤
      (operatorApproximationError M P R N +
          negativePart (twoScaleMinorIntegralReal M P R N) -
          discreteModelOvershoot M P R N) *
        (operatorApproximationError M P R N +
          negativePart (twoScaleMinorIntegralReal M P R N) +
          discreteModelOvershoot M P R N) :=
    mul_nonneg (sub_nonneg.mpr hle) (add_nonneg (add_nonneg ha hb) hx)
  nlinarith [hprod,
    sq_nonneg
      (operatorApproximationError M P R N -
        negativePart (twoScaleMinorIntegralReal M P R N))]

/-- Finite moment transfer on any carrier contained in the literal coefficient
range. -/
theorem discreteModelOvershootSquaredMoment_le_actual_channels
    (M P R : ℕ) (s : Finset ℕ) (hRange : ∀ N ∈ s, N ≤ M) :
    discreteModelOvershootSquaredMoment M P R s ≤
      2 * operatorApproximationSquaredMoment M P R s +
        2 * negativePartSquaredMoment s (twoScaleMinorIntegralReal M P R) := by
  unfold discreteModelOvershootSquaredMoment operatorApproximationSquaredMoment
    negativePartSquaredMoment
  calc
    _ ≤ ∑ N ∈ s,
        (2 * (operatorApproximationError M P R N) ^ 2 +
          2 * (negativePart (twoScaleMinorIntegralReal M P R N)) ^ 2) := by
      apply Finset.sum_le_sum
      intro N hN
      exact discreteModelOvershoot_sq_le_actual_channels M P R N (hRange N hN)
    _ = _ := by
      simp only [Finset.sum_add_distrib, Finset.mul_sum]

/-- Quantitative exception-count transfer expressed only through the literal
Major-operator approximation channel and the actual negative Minor channel.
The model reserve and both analytic moment estimates remain external. -/
theorem exception_card_mul_threshold_sq_le_actual_channels
    (M P R : ℕ)
    (hScale : 112 * (Real.log (M : ℝ)) ^ 2 ≤ Real.sqrt (M : ℝ))
    (hModel : ∀ N ∈ evenTargetBlock M,
      (M : ℝ) / 14 ≤ discreteArcMainModel M N R P) :
    ((((evenTargetBlock M).filter (fun N => ¬ GoldbachAt N)).card : ℝ) *
        ((M : ℝ) / 28) ^ 2) ≤
      2 * operatorApproximationSquaredMoment M P R (evenTargetBlock M) +
        2 * negativePartSquaredMoment (evenTargetBlock M)
          (twoScaleMinorIntegralReal M P R) := by
  have hCount :=
    exception_card_mul_threshold_sq_le_modelOvershootMoment
      M P R hScale hModel
  refine hCount.trans ?_
  apply discreteModelOvershootSquaredMoment_le_actual_channels
  intro N hN
  exact ((mem_evenTargetBlock_iff M N).1 hN).2.1

end GoldbachCircleMethodDiscreteModelToActualMinorV18636
