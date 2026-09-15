import GoldbachCircleMethodOddOddFourierBesselBridgeV18668
import GoldbachCircleMethodSignedMagnitudeIdentityV18628

/-!
# V1.8.669: exact project-normalized Odd-Odd signed budget

V1.8.668 identifies the compensated Odd-Odd deficit with a literal Fourier
coefficient and gives a Bessel ceiling.  The Bessel route is deliberately not
promoted here: it discards precisely the coefficient-sign bias needed by the
one-sided exceptional-set gate.

This module instead freezes the exact project-normalized coefficient and proves
that the remaining Odd-Odd premise is equivalent to one explicit signed-bias
inequality.  The threshold is `M^2 / 6272`, twice the one-sided allocation
`M^2 / 12544`, with no asymptotic notation and no hidden normalization.

No estimate of the signed bias is supplied.  The final theorem is conditional
on that still-uninhabited analytic input.

`proof_status = NO_PROOF`.
-/

set_option autoImplicit false

open scoped BigOperators Classical
open Filter Topology
open GoldbachCircleMethodExceptionalTransferV1823
open GoldbachCircleMethodTwoScaleEvenBlockDefectReserveV1833
open GoldbachCircleMethodSignedMagnitudeIdentityV18628
open GoldbachCircleMethodUniformModelReserveCubicScaleV18639
open GoldbachCircleMethodEventualAnalyticInputReductionV18642
open GoldbachCircleMethodOddChannelEventualAbsorptionV18658
open GoldbachCircleMethodDiagonalCompensatedEvenSubchannelsV18667
open GoldbachCircleMethodOddOddFourierBesselBridgeV18668

namespace GoldbachCircleMethodOddOddExactSignedBudgetV18669

/-- The exact full Odd-Odd Minor coefficient in the project's fixed schedule.
This is a name for an existing coefficient, not a new analytic operator. -/
noncomputable def projectOddOddCoefficient (M N : Nat) : Real :=
  oddOddMinorKernelConvolution M
    (oddProjectWidth M) (oddProjectRadius M) N

/-- The geometric scale condition required by the exact kernel adapter holds
eventually at the fixed project schedule. -/
theorem project_scale_condition_eventually :
    ∀ᶠ M : Nat in atTop,
      2 * oddProjectWidth M * oddProjectRadius M < M := by
  filter_upwards [logRadius_cubic_window_eventually 10] with M hM
  exact cubicModelScale_window M (oddProjectRadius M) hM

/-- Pointwise project-normalized identification with the compensated deficit.
The sign is exact: the harmful input `-compensatedOddOddDeficit` is the actual
Odd-Odd Minor coefficient. -/
theorem neg_compensatedOddOddDeficit_eq_projectCoefficient
    (M N : Nat)
    (hscale : 2 * oddProjectWidth M * oddProjectRadius M < M) :
    -compensatedOddOddDeficit M
        (oddProjectWidth M) (oddProjectRadius M) N =
      projectOddOddCoefficient M N := by
  unfold projectOddOddCoefficient
  rw [compensatedOddOddDeficit_eq_neg_minorConvolution M
    (oddProjectWidth M) (oddProjectRadius M) N hscale]
  ring

/-- Exact finite target-moment identification at the fixed schedule. -/
theorem compensatedOddOdd_project_moment_eq_coefficient_moment
    (M : Nat)
    (hscale : 2 * oddProjectWidth M * oddProjectRadius M < M) :
    negativePartSquaredMoment (evenTargetBlock M)
        (fun N => -compensatedOddOddDeficit M
          (oddProjectWidth M) (oddProjectRadius M) N) =
      negativePartSquaredMoment (evenTargetBlock M)
        (projectOddOddCoefficient M) := by
  apply Finset.sum_congr rfl
  intro N _hN
  simp only
  rw [neg_compensatedOddOddDeficit_eq_projectCoefficient M N hscale]

/-- Exact signed-magnitude decomposition for the project coefficient. -/
theorem projectOddOdd_negativePartMoment_eq_half_signedGap (M : Nat) :
    negativePartSquaredMoment (evenTargetBlock M)
        (projectOddOddCoefficient M) =
      (squareEnergy (evenTargetBlock M) (projectOddOddCoefficient M) -
        signedMagnitudeCorrelation (evenTargetBlock M)
          (projectOddOddCoefficient M)) / 2 := by
  exact negativePartSquaredMoment_eq_half_signed_gap
    (evenTargetBlock M) (projectOddOddCoefficient M)

/-- The exact remaining project budget.  This equivalence is the normalization
audit: no factor, target, sign, or denominator is left implicit. -/
theorem compensatedOddOdd_project_budget_iff_signedGap
    (M : Nat)
    (hscale : 2 * oddProjectWidth M * oddProjectRadius M < M) :
    negativePartSquaredMoment (evenTargetBlock M)
        (fun N => -compensatedOddOddDeficit M
          (oddProjectWidth M) (oddProjectRadius M) N) <
        (M : Real) ^ 2 / 12544 ↔
      squareEnergy (evenTargetBlock M) (projectOddOddCoefficient M) -
          signedMagnitudeCorrelation (evenTargetBlock M)
            (projectOddOddCoefficient M) <
        (M : Real) ^ 2 / 6272 := by
  rw [compensatedOddOdd_project_moment_eq_coefficient_moment M hscale]
  rw [projectOddOdd_negativePartMoment_eq_half_signedGap]
  constructor <;> intro h <;> nlinarith

/-- Equivalent lower-bound form: what remains is positive sign bias, not
pairwise sign cancellation and not a second total-energy estimate. -/
theorem project_signedGap_lt_iff_signedBias_gt (M : Nat) :
    squareEnergy (evenTargetBlock M) (projectOddOddCoefficient M) -
          signedMagnitudeCorrelation (evenTargetBlock M)
            (projectOddOddCoefficient M) <
        (M : Real) ^ 2 / 6272 ↔
      squareEnergy (evenTargetBlock M) (projectOddOddCoefficient M) -
          (M : Real) ^ 2 / 6272 <
        signedMagnitudeCorrelation (evenTargetBlock M)
          (projectOddOddCoefficient M) := by
  constructor <;> intro h <;> linarith

/-- Exact conditional handoff into V1.8.667.  This theorem consumes the
signed-bias estimate under the project normalization; it does not inhabit it. -/
theorem project_totalJordan_eventually_lt_one_over_784_of_signedBias
    (hBias :
      ∀ᶠ M : Nat in atTop,
        squareEnergy (evenTargetBlock M) (projectOddOddCoefficient M) -
            (M : Real) ^ 2 / 6272 <
          signedMagnitudeCorrelation (evenTargetBlock M)
            (projectOddOddCoefficient M)) :
    ∀ᶠ M : Nat in atTop,
      GoldbachCircleMethodExplicitJordanDeficitV18651.explicitJordanDeficitSquaredMoment M
          (oddProjectWidth M) (oddProjectRadius M) (evenTargetBlock M) <
        (M : Real) ^ 2 / 784 := by
  apply project_totalJordan_eventually_lt_one_over_784_of_compensatedOddOdd
  filter_upwards [project_scale_condition_eventually, hBias] with M hscale hM
  exact (compensatedOddOdd_project_budget_iff_signedGap M hscale).2
    ((project_signedGap_lt_iff_signedBias_gt M).2 hM)

end GoldbachCircleMethodOddOddExactSignedBudgetV18669
