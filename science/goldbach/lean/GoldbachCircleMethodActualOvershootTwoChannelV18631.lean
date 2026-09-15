import GoldbachCircleMethodActualMajorOvershootIdentityV18630
import GoldbachCircleMethodActualOperatorErrorTransferV1861

/-!
# V1.8.631: actual overshoot split into two concrete channels

The actual Major overshoot is bounded by the sum of (i) the error between the
literal Major operator and the fixed discrete arc model and (ii) the positive
overshoot of that same discrete model above the full von-Mangoldt coefficient.

The first channel is connected to the already kernelized local arc-approximation
transfer.  The second remains an arithmetic target-correlation problem.  No
estimate for the second channel is supplied here.

`proof_status = NO_PROOF`.
-/
set_option autoImplicit false

open scoped BigOperators Classical
open GoldbachVonMangoldtDecompositionV16
open GoldbachCircleMethodTwoScaleIntegralPartitionV1831
open GoldbachCircleMethodDiscreteMainKernelV1852
open GoldbachCircleMethodDiscreteArcModelReserveV1855
open GoldbachCircleMethodMajorMinorPartitionV172
open GoldbachCircleMethodTwoScaleMaskAdapterV1829
open GoldbachCircleMethodFixedScaleTransferV1824
open GoldbachCircleMethodFourierIdentityV171
open GoldbachCircleMethodClosedArcCoordinatesV1857
open GoldbachCircleMethodActualOperatorErrorTransferV1861
open GoldbachCircleMethodActualMajorOvershootIdentityV18630

namespace GoldbachCircleMethodActualOvershootTwoChannelV18631

/-- Literal error between the actual Major coefficient and its discrete arc
model. -/
noncomputable def operatorApproximationError (M P R N : ℕ) : ℝ :=
  |twoScaleMajorIntegralReal M P R N - discreteArcMainModel M N R P|

/-- Positive overshoot of the discrete arc model above the full arithmetic
coefficient. -/
noncomputable def discreteModelOvershoot (M P R N : ℕ) : ℝ :=
  max (discreteArcMainModel M N R P - vonMangoldtPairSum N) 0

/-- Pointwise two-channel split.  This is a deterministic order inequality,
not an analytic estimate. -/
theorem actualMajorOvershoot_le_two_channel (M P R N : ℕ) :
    actualMajorOvershoot M P R N ≤
      operatorApproximationError M P R N + discreteModelOvershoot M P R N := by
  unfold actualMajorOvershoot operatorApproximationError discreteModelOvershoot
  apply max_le
  · have hop := le_abs_self
      (twoScaleMajorIntegralReal M P R N - discreteArcMainModel M N R P)
    have hmodel := le_max_left
      (discreteArcMainModel M N R P - vonMangoldtPairSum N) 0
    linarith
  · exact add_nonneg (abs_nonneg _) (le_max_right _ _)

/-- Squared pointwise form with the exact factor two from
`(a+b)^2 ≤ 2a^2+2b^2`. -/
theorem actualMajorOvershoot_sq_le_two_channel (M P R N : ℕ) :
    (actualMajorOvershoot M P R N) ^ 2 ≤
      2 * (operatorApproximationError M P R N) ^ 2 +
        2 * (discreteModelOvershoot M P R N) ^ 2 := by
  have hle := actualMajorOvershoot_le_two_channel M P R N
  have hx : 0 ≤ actualMajorOvershoot M P R N := by
    unfold actualMajorOvershoot
    exact le_max_right _ _
  have ha : 0 ≤ operatorApproximationError M P R N := by
    unfold operatorApproximationError
    exact abs_nonneg _
  have hb : 0 ≤ discreteModelOvershoot M P R N := by
    unfold discreteModelOvershoot
    exact le_max_right _ _
  have hprod : 0 ≤
      (operatorApproximationError M P R N + discreteModelOvershoot M P R N -
          actualMajorOvershoot M P R N) *
        (operatorApproximationError M P R N + discreteModelOvershoot M P R N +
          actualMajorOvershoot M P R N) :=
    mul_nonneg (sub_nonneg.mpr hle) (add_nonneg (add_nonneg ha hb) hx)
  nlinarith [hprod,
    sq_nonneg (operatorApproximationError M P R N - discreteModelOvershoot M P R N)]

/-- Squared operator-approximation error on a finite carrier. -/
noncomputable def operatorApproximationSquaredMoment
    (M P R : ℕ) (s : Finset ℕ) : ℝ :=
  ∑ N ∈ s, (operatorApproximationError M P R N) ^ 2

/-- Squared discrete-model overshoot on a finite carrier. -/
noncomputable def discreteModelOvershootSquaredMoment
    (M P R : ℕ) (s : Finset ℕ) : ℝ :=
  ∑ N ∈ s, (discreteModelOvershoot M P R N) ^ 2

/-- Finite two-channel reduction for the actual overshoot moment. -/
theorem actualMajorOvershootSquaredMoment_le_two_channel
    (M P R : ℕ) (s : Finset ℕ) :
    actualMajorOvershootSquaredMoment M P R s ≤
      2 * operatorApproximationSquaredMoment M P R s +
        2 * discreteModelOvershootSquaredMoment M P R s := by
  unfold actualMajorOvershootSquaredMoment operatorApproximationSquaredMoment
    discreteModelOvershootSquaredMoment
  calc
    _ ≤ ∑ N ∈ s,
        (2 * (operatorApproximationError M P R N) ^ 2 +
          2 * (discreteModelOvershoot M P R N) ^ 2) := by
      apply Finset.sum_le_sum
      intro N _hN
      exact actualMajorOvershoot_sq_le_two_channel M P R N
    _ = _ := by
      simp only [Finset.sum_add_distrib, Finset.mul_sum]

/-- Uniform pointwise envelope supplied by the existing actual-operator error
transfer. -/
noncomputable def operatorPointwiseEnvelope (M P R : ℕ) (ε : ℝ) : ℝ :=
  (2 * (M : ℝ) * ε + ε ^ 2) *
    (∑ i : ReducedRationalIndex R, 2 * twoScaleArcRadius M P i)

/-- The local rational-arc approximation bounds the first channel on every
finite target carrier.  This does not address the second channel. -/
theorem operatorApproximationSquaredMoment_le_card_mul_envelope_sq
    (M P R : ℕ) (s : Finset ℕ)
    (hR : 1 ≤ R) (hscale : 2 * P * R < M) (ε : ℝ)
    (happrox : ∀ i : ReducedRationalIndex R,
      ∀ x ∈ Metric.closedBall (majorArcCenter i) (twoScaleArcRadius M P i),
        ‖exponentialSum M.succ x -
          (((ArithmeticFunction.moebius i.val.1 : ℤ) : ℂ) /
              (Nat.totient i.val.1 : ℂ)) *
            discreteMainPolynomial M (x - majorArcCenter i)‖ ≤ ε) :
    operatorApproximationSquaredMoment M P R s ≤
      (s.card : ℝ) * (operatorPointwiseEnvelope M P R ε) ^ 2 := by
  unfold operatorApproximationSquaredMoment
  calc
    _ ≤ ∑ _N ∈ s, (operatorPointwiseEnvelope M P R ε) ^ 2 := by
      apply Finset.sum_le_sum
      intro N _hN
      have hbound := original_major_real_error_bound M P R N hR hscale ε happrox
      change operatorApproximationError M P R N ≤
        operatorPointwiseEnvelope M P R ε at hbound
      have hleft : 0 ≤ operatorApproximationError M P R N := by
        unfold operatorApproximationError
        exact abs_nonneg _
      have hright : 0 ≤ operatorPointwiseEnvelope M P R ε := hleft.trans hbound
      have hprod : 0 ≤
          (operatorPointwiseEnvelope M P R ε - operatorApproximationError M P R N) *
            (operatorPointwiseEnvelope M P R ε + operatorApproximationError M P R N) :=
        mul_nonneg (sub_nonneg.mpr hbound) (add_nonneg hright hleft)
      nlinarith [hprod]
    _ = _ := by simp

end GoldbachCircleMethodActualOvershootTwoChannelV18631
