import GoldbachCircleMethodDiscreteModelToActualMinorV18636

/-!
# V1.8.637: actual one-sided Minor moment to full Minor energy

The negative-part square of a real coefficient is bounded by its full square.
Summing this elementary inequality connects the one-sided actual Minor channel
from V1.8.636 to the conventional full second moment used by classical
exceptional-set arguments.

No full-energy estimate, operator approximation estimate, uniform model
reserve, or Goldbach theorem is supplied here.

`proof_status = NO_PROOF`.
-/
set_option autoImplicit false

open scoped BigOperators Classical
open GoldbachPurePrimeAdequacyV15
open GoldbachCircleMethodExceptionalTransferV1823
open GoldbachCircleMethodTwoScaleIntegralPartitionV1831
open GoldbachCircleMethodTwoScaleEvenBlockDefectReserveV1833
open GoldbachCircleMethodDiscreteArcModelReserveV1855
open GoldbachCircleMethodActualOvershootTwoChannelV18631
open GoldbachCircleMethodSignedMagnitudeIdentityV18628
open GoldbachCircleMethodDiscreteModelToActualMinorV18636

namespace GoldbachCircleMethodActualMinorFullEnergyTransferV18637

/-- The one-sided negative-part square never exceeds the full square. -/
theorem negativePart_sq_le_square (x : ℝ) :
    (negativePart x) ^ 2 ≤ x ^ 2 := by
  unfold negativePart
  by_cases hx : 0 ≤ x
  · rw [max_eq_right]
    · simpa using sq_nonneg x
    · linarith
  · have hx' : x < 0 := lt_of_not_ge hx
    rw [max_eq_left]
    · nlinarith
    · linarith

/-- Finite one-sided-to-full-energy transfer on an arbitrary carrier. -/
theorem negativePartSquaredMoment_le_squareEnergy
    {ι : Type*} (s : Finset ι) (H : ι → ℝ) :
    negativePartSquaredMoment s H ≤ squareEnergy s H := by
  unfold negativePartSquaredMoment squareEnergy
  exact Finset.sum_le_sum fun i _hi => negativePart_sq_le_square (H i)

/-- Quantitative Goldbach-exception count controlled by the literal Major
operator-error moment and the conventional full actual-Minor square energy.
All number-theoretic estimates remain explicit external obligations. -/
theorem exception_card_mul_threshold_sq_le_operatorError_add_minorEnergy
    (M P R : ℕ)
    (hScale : 112 * (Real.log (M : ℝ)) ^ 2 ≤ Real.sqrt (M : ℝ))
    (hModel : ∀ N ∈ evenTargetBlock M,
      (M : ℝ) / 14 ≤ discreteArcMainModel M N R P) :
    ((((evenTargetBlock M).filter (fun N => ¬ GoldbachAt N)).card : ℝ) *
        ((M : ℝ) / 28) ^ 2) ≤
      2 * operatorApproximationSquaredMoment M P R (evenTargetBlock M) +
        2 * squareEnergy (evenTargetBlock M)
          (twoScaleMinorIntegralReal M P R) := by
  have hChannels :=
    exception_card_mul_threshold_sq_le_actual_channels
      M P R hScale hModel
  have hMinor := negativePartSquaredMoment_le_squareEnergy
    (evenTargetBlock M) (twoScaleMinorIntegralReal M P R)
  linarith

end GoldbachCircleMethodActualMinorFullEnergyTransferV18637
