import GoldbachCircleMethodActualMinorFullEnergyTransferV18637
import GoldbachCircleMethodMajorOperatorErrorEnergyV18634
import GoldbachCircleMethodChebyshevEnergyBudgetV1889

/-!
# V1.8.638: actual-channel budget in the exact project normalization

This module keeps the literal V1.8.637 right-hand side and binds both of its
channels to already existing fixed-function Bessel energies.  It then composes
the existing local Major approximation envelope and the existing conservative
Vaughan/Chebyshev Minor budget without changing the mask, target carrier,
Fourier normalization, cutoff parameters, or constants.

`RealVaughanEstimate C`, the local Major approximation, and the discrete-model
reserve remain explicit premises.  No inhabitant of those analytic premises,
exceptional-set decay, exception-set emptiness, or Goldbach theorem is supplied.

`proof_status = NO_PROOF`.
-/
set_option autoImplicit false

open scoped BigOperators Classical
open MeasureTheory AddCircle
open GoldbachPurePrimeAdequacyV15
open GoldbachCircleMethodExceptionalTransferV1823
open GoldbachCircleMethodFourierIdentityV171
open GoldbachCircleMethodMajorMinorPartitionV172
open GoldbachCircleMethodTwoScaleMaskAdapterV1829
open GoldbachCircleMethodTwoScaleIntegralPartitionV1831
open GoldbachCircleMethodTwoScaleEvenBlockDefectReserveV1833
open GoldbachCircleMethodTwoScaleBesselBridgeV1834
open GoldbachCircleMethodDiscreteMainKernelV1852
open GoldbachCircleMethodDiscreteArcModelReserveV1855
open GoldbachCircleMethodActualOvershootTwoChannelV18631
open GoldbachCircleMethodSignedMagnitudeIdentityV18628
open GoldbachCircleMethodMajorOperatorErrorBesselV18633
open GoldbachCircleMethodMajorOperatorErrorEnergyV18634
open GoldbachCircleMethodRealApproximationMinorAdapterV1873
open GoldbachCircleMethodChebyshevEnergyBudgetV1889
open GoldbachCircleMethodActualMinorFullEnergyTransferV18637

namespace GoldbachCircleMethodActualChannelProjectBudgetV18638

/-- The full real square energy of the literal Minor coefficients on any
finite natural-frequency carrier is bounded by the fourth moment of the
unchanged two-scale Minor mask. -/
theorem squareEnergy_twoScaleMinorIntegralReal_le_minorFourthMoment
    (M P R : ℕ) (s : Finset ℕ) :
    squareEnergy s (twoScaleMinorIntegralReal M P R) ≤
      minorFourthMoment M P R := by
  unfold squareEnergy
  calc
    _ ≤ ∑ N ∈ s,
        ‖fourierCoeff (maskedSquare M P R) (N : ℤ)‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro N _hN
      rw [minorReal_eq_re_fourierCoeff]
      rw [← sq_abs]
      exact (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).mpr
        (Complex.abs_re_le_norm _)
    _ ≤ _ := finite_sq_coeff_le_minorFourthMoment M P R s

/-- Exact normalization bridge for the two literal V1.8.637 channels.  The
target carrier is arbitrary; no carrier-cardinality factor is introduced. -/
theorem actualChannelBudget_le_exactBesselEnergies
    (M P R : ℕ) (s : Finset ℕ) (hR : 1 ≤ R)
    (hscale : 2 * P * R < M) :
    2 * operatorApproximationSquaredMoment M P R s +
        2 * squareEnergy s (twoScaleMinorIntegralReal M P R) ≤
      2 * majorOperatorErrorEnergy M P R +
        2 * minorFourthMoment M P R := by
  have hMajor := operatorApproximationSquaredMoment_le_errorEnergy
    M P R s hR hscale
  have hMinor :=
    squareEnergy_twoScaleMinorIntegralReal_le_minorFourthMoment M P R s
  linarith

/-- The exact actual-channel budget with all currently available explicit
project envelopes.  The two analytic source inputs remain visible premises:
the local Major approximation and `RealVaughanEstimate C`. -/
theorem actualChannelBudget_le_explicitProjectBudget
    (C ε : ℝ) (hC : 0 ≤ C) (hV : RealVaughanEstimate C)
    (M P R : ℕ) (s : Finset ℕ) (hM : 3 ≤ M)
    (hP : 0 < P) (hPM : P ≤ M) (hR : 1 ≤ R)
    (hscale : 2 * P * R < M) (hε : 0 ≤ ε)
    (happrox : ∀ i : ReducedRationalIndex R,
      ∀ x ∈ Metric.closedBall (majorArcCenter i) (twoScaleArcRadius M P i),
        ‖exponentialSum M.succ x -
          (((ArithmeticFunction.moebius i.val.1 : ℤ) : ℂ) /
            (Nat.totient i.val.1 : ℂ)) *
              discreteMainPolynomial M (x - majorArcCenter i)‖ ≤ ε) :
    2 * operatorApproximationSquaredMoment M P R s +
        2 * squareEnergy s (twoScaleMinorIntegralReal M P R) ≤
      2 * (majorOperatorErrorEnvelope M ε) ^ 2 +
        2 * chebyshevFourthBudget M P R C := by
  have hBase := actualChannelBudget_le_exactBesselEnergies
    M P R s hR hscale
  have hMajor := majorOperatorErrorEnergy_le_envelope_sq
    M P R hscale ε hε happrox
  have hMinor := minorFourthMoment_le_chebyshev_budget
    C hC hV M P R hM hP hPM (by omega)
  linarith

/-- Quantitative exception-count transfer with the exact V1.8.637 target and
the explicit project-normalized envelopes substituted.  The model reserve is
kept separate and explicit. -/
theorem exception_card_mul_threshold_sq_le_explicitProjectBudget
    (C ε : ℝ) (hC : 0 ≤ C) (hV : RealVaughanEstimate C)
    (M P R : ℕ) (hM : 3 ≤ M) (hP : 0 < P) (hPM : P ≤ M)
    (hR : 1 ≤ R) (hscale : 2 * P * R < M) (hε : 0 ≤ ε)
    (hScale : 112 * (Real.log (M : ℝ)) ^ 2 ≤ Real.sqrt (M : ℝ))
    (hModel : ∀ N ∈ evenTargetBlock M,
      (M : ℝ) / 14 ≤ discreteArcMainModel M N R P)
    (happrox : ∀ i : ReducedRationalIndex R,
      ∀ x ∈ Metric.closedBall (majorArcCenter i) (twoScaleArcRadius M P i),
        ‖exponentialSum M.succ x -
          (((ArithmeticFunction.moebius i.val.1 : ℤ) : ℂ) /
            (Nat.totient i.val.1 : ℂ)) *
              discreteMainPolynomial M (x - majorArcCenter i)‖ ≤ ε) :
    ((((evenTargetBlock M).filter (fun N => ¬ GoldbachAt N)).card : ℝ) *
        ((M : ℝ) / 28) ^ 2) ≤
      2 * (majorOperatorErrorEnvelope M ε) ^ 2 +
        2 * chebyshevFourthBudget M P R C := by
  exact
    (exception_card_mul_threshold_sq_le_operatorError_add_minorEnergy
      M P R hScale hModel).trans
      (actualChannelBudget_le_explicitProjectBudget
        C ε hC hV M P R (evenTargetBlock M) hM hP hPM hR hscale hε happrox)

end GoldbachCircleMethodActualChannelProjectBudgetV18638
