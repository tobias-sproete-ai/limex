import GoldbachCircleMethodOddOddExactSignedBudgetV18669
import GoldbachCircleMethodOddOddSmallDenominatorNegativeWitnessV18666

/-!
# V1.8.670: signed small-denominator core and large-denominator perturbation

The exact project coefficient from V1.8.669 is split without absolute values.
The `q <= 2` terms remain inside a compensated signed core together with the
entire Odd-Odd diagonal reserve.  Only the `q > 2` terms are exposed as a
separate perturbation.

The one-sided project moment is then bounded by a small-core one-sided moment
and an ordinary square-energy budget for the large-denominator perturbation.
The concrete allocation `M^2/50176` to each input is exactly sufficient for
the required `M^2/12544` Odd-Odd budget.

Neither input budget is inhabited here.  V1.8.666 forbids termwise
nonnegativity of the `q <= 2` kernel, but it neither proves nor disproves the
sign of the compensated small core: its diagonal reserve and the subtraction
of the complete signed small-denominator deficit must be analyzed together.

`proof_status = NO_PROOF`.
-/

set_option autoImplicit false

open scoped BigOperators Classical
open Filter Topology
open GoldbachCircleMethodExceptionalTransferV1823
open GoldbachCircleMethodTwoScaleEvenBlockDefectReserveV1833
open GoldbachCircleMethodActualMinorFullEnergyTransferV18637
open GoldbachCircleMethodActualOneSidedKernelLeakageV18648
open GoldbachCircleMethodOddChannelEventualAbsorptionV18658
open GoldbachCircleMethodTotalJordanEvenGateV18659
open GoldbachCircleMethodOddOddSignedFiberAdapterV18665
open GoldbachCircleMethodOddOddSmallDenominatorNegativeWitnessV18666
open GoldbachCircleMethodDiagonalCompensatedEvenSubchannelsV18667
open GoldbachCircleMethodOddOddExactSignedBudgetV18669

namespace GoldbachCircleMethodOddOddSmallCoreLargePerturbationV18670

/-- Exact signed `q <= 2` off-diagonal Odd-Odd deficit. -/
noncomputable def smallDenominatorOddOddDeficit
    (M P R N : Nat) : Real :=
  ∑ t ∈ oddOddOffDiagonalSumCarrier M N,
    oddOddPairFiberMass M t *
      (explicitSmallDenominatorSincKernel M P R
        ((N : Int) - (t : Int))).re

/-- Exact signed `q > 2` off-diagonal Odd-Odd deficit. -/
noncomputable def largeDenominatorOddOddDeficit
    (M P R N : Nat) : Real :=
  ∑ t ∈ oddOddOffDiagonalSumCarrier M N,
    oddOddPairFiberMass M t *
      (explicitLargeDenominatorSincKernel M P R
        ((N : Int) - (t : Int))).re

/-- The diagonal reserve is kept with the literal signed `q <= 2` core. -/
noncomputable def compensatedSmallDenominatorCore
    (M P R N : Nat) : Real :=
  explicitDiagonalOddOddReserve M P R N -
    smallDenominatorOddOddDeficit M P R N

/-- The exact additive perturbation induced by the `q > 2` off-diagonal
deficit. -/
noncomputable def largeDenominatorPerturbation
    (M P R N : Nat) : Real :=
  -largeDenominatorOddOddDeficit M P R N

theorem explicitOddOddSubchannelDeficit_eq_small_add_large
    (M P R N : Nat) :
    GoldbachCircleMethodEvenSubchannelSplitV18660.explicitOddOddSubchannelDeficit
        M P R N =
      smallDenominatorOddOddDeficit M P R N +
        largeDenominatorOddOddDeficit M P R N := by
  rw [explicitOddOddSubchannelDeficit_eq_small_add_large_fibers]
  unfold smallDenominatorOddOddDeficit largeDenominatorOddOddDeficit
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t _ht
  ring

/-- Exact signed split of the project coefficient.  No triangle inequality is
used in this identity. -/
theorem projectOddOddCoefficient_eq_smallCore_add_largePerturbation
    (M N : Nat)
    (hscale : 2 * oddProjectWidth M * oddProjectRadius M < M) :
    projectOddOddCoefficient M N =
      compensatedSmallDenominatorCore M
          (oddProjectWidth M) (oddProjectRadius M) N +
        largeDenominatorPerturbation M
          (oddProjectWidth M) (oddProjectRadius M) N := by
  rw [← neg_compensatedOddOddDeficit_eq_projectCoefficient M N hscale]
  unfold compensatedOddOddDeficit compensatedSmallDenominatorCore
    largeDenominatorPerturbation
  rw [explicitOddOddSubchannelDeficit_eq_small_add_large]
  ring

/-- Generic one-sided square-energy split. -/
theorem negativePartSquaredMoment_add_le_two
    {ι : Type*} (s : Finset ι) (A B : ι → Real) :
    negativePartSquaredMoment s (fun i => A i + B i) ≤
      2 * negativePartSquaredMoment s A +
        2 * negativePartSquaredMoment s B := by
  unfold negativePartSquaredMoment
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _hi
  have h := negativePart_add_le (A i) (B i)
  have hA := negativePart_nonneg (A i)
  have hB := negativePart_nonneg (B i)
  have hAB := negativePart_nonneg (A i + B i)
  nlinarith [sq_nonneg (negativePart (A i) - negativePart (B i))]

/-- The exact coefficient moment is controlled by a sign-sensitive small-core
moment and an L2 perturbation budget for `q > 2`. -/
theorem projectOddOdd_moment_le_smallCore_add_largeEnergy
    (M : Nat)
    (hscale : 2 * oddProjectWidth M * oddProjectRadius M < M) :
    negativePartSquaredMoment (evenTargetBlock M)
        (projectOddOddCoefficient M) ≤
      2 * negativePartSquaredMoment (evenTargetBlock M)
          (compensatedSmallDenominatorCore M
            (oddProjectWidth M) (oddProjectRadius M)) +
        2 * GoldbachCircleMethodSignedMagnitudeIdentityV18628.squareEnergy
          (evenTargetBlock M)
          (largeDenominatorPerturbation M
            (oddProjectWidth M) (oddProjectRadius M)) := by
  have hsplit : projectOddOddCoefficient M =
      fun N =>
        compensatedSmallDenominatorCore M
            (oddProjectWidth M) (oddProjectRadius M) N +
          largeDenominatorPerturbation M
            (oddProjectWidth M) (oddProjectRadius M) N := by
    funext N
    exact projectOddOddCoefficient_eq_smallCore_add_largePerturbation M N hscale
  rw [hsplit]
  have hSplitMoment := negativePartSquaredMoment_add_le_two (evenTargetBlock M)
      (compensatedSmallDenominatorCore M
        (oddProjectWidth M) (oddProjectRadius M))
      (largeDenominatorPerturbation M
        (oddProjectWidth M) (oddProjectRadius M))
  have hLarge := negativePartSquaredMoment_le_squareEnergy
    (evenTargetBlock M)
    (largeDenominatorPerturbation M
      (oddProjectWidth M) (oddProjectRadius M))
  have hLargeScaled :
      2 * negativePartSquaredMoment (evenTargetBlock M)
          (largeDenominatorPerturbation M
            (oddProjectWidth M) (oddProjectRadius M)) ≤
        2 * GoldbachCircleMethodSignedMagnitudeIdentityV18628.squareEnergy
          (evenTargetBlock M)
          (largeDenominatorPerturbation M
            (oddProjectWidth M) (oddProjectRadius M)) :=
    mul_le_mul_of_nonneg_left hLarge (by norm_num)
  exact hSplitMoment.trans (add_le_add le_rfl hLargeScaled)

/-- Equal allocation of the exact remaining budget.  Both assumptions remain
open analytic obligations. -/
theorem compensatedOddOdd_project_budget_of_smallCore_and_largeEnergy
    (M : Nat)
    (hscale : 2 * oddProjectWidth M * oddProjectRadius M < M)
    (hSmall :
      negativePartSquaredMoment (evenTargetBlock M)
          (compensatedSmallDenominatorCore M
            (oddProjectWidth M) (oddProjectRadius M)) <
        (M : Real) ^ 2 / 50176)
    (hLarge :
      GoldbachCircleMethodSignedMagnitudeIdentityV18628.squareEnergy
          (evenTargetBlock M)
          (largeDenominatorPerturbation M
            (oddProjectWidth M) (oddProjectRadius M)) <
        (M : Real) ^ 2 / 50176) :
    negativePartSquaredMoment (evenTargetBlock M)
        (fun N => -compensatedOddOddDeficit M
          (oddProjectWidth M) (oddProjectRadius M) N) <
      (M : Real) ^ 2 / 12544 := by
  rw [compensatedOddOdd_project_moment_eq_coefficient_moment M hscale]
  have hBound := projectOddOdd_moment_le_smallCore_add_largeEnergy M hscale
  nlinarith

/-- Conditional project handoff with the two honest analytic obligations left
visible. -/
theorem project_totalJordan_eventually_lt_one_over_784_of_splitBudgets
    (hSmall :
      ∀ᶠ M : Nat in atTop,
        negativePartSquaredMoment (evenTargetBlock M)
            (compensatedSmallDenominatorCore M
              (oddProjectWidth M) (oddProjectRadius M)) <
          (M : Real) ^ 2 / 50176)
    (hLarge :
      ∀ᶠ M : Nat in atTop,
        GoldbachCircleMethodSignedMagnitudeIdentityV18628.squareEnergy
            (evenTargetBlock M)
            (largeDenominatorPerturbation M
              (oddProjectWidth M) (oddProjectRadius M)) <
          (M : Real) ^ 2 / 50176) :
    ∀ᶠ M : Nat in atTop,
      GoldbachCircleMethodExplicitJordanDeficitV18651.explicitJordanDeficitSquaredMoment M
          (oddProjectWidth M) (oddProjectRadius M) (evenTargetBlock M) <
        (M : Real) ^ 2 / 784 := by
  apply project_totalJordan_eventually_lt_one_over_784_of_compensatedOddOdd
  filter_upwards [project_scale_condition_eventually, hSmall, hLarge]
    with M hscale hS hL
  exact compensatedOddOdd_project_budget_of_smallCore_and_largeEnergy
    M hscale hS hL

end GoldbachCircleMethodOddOddSmallCoreLargePerturbationV18670
