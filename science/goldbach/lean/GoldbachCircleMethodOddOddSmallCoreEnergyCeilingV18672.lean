import GoldbachCircleMethodOddOddLargeDenominatorEnergyReductionV18671

/-!
# V1.8.672: elementary energy ceiling for the compensated small core

The diagonal reserve in the V1.8.670 small-denominator core is nonnegative.
Consequently, subtracting that reserve cannot enlarge the negative part beyond
the absolute size of the signed `q <= 2` deficit.  This module proves that
elementary pointwise fact, sums it on an arbitrary finite carrier, and records
the exact signed-magnitude reformulation of the project threshold.

The resulting project handoff remains conditional on a square-energy estimate
for the literal small-denominator Odd-Odd deficit.  No such analytic estimate,
no pointwise sign assertion, and no Goldbach conclusion is supplied here.

`proof_status = NO_PROOF`.
-/

set_option autoImplicit false

open scoped BigOperators Classical
open GoldbachCircleMethodExceptionalTransferV1823
open GoldbachCircleMethodTwoScaleEvenBlockDefectReserveV1833
open GoldbachCircleMethodActualMinorFullEnergyTransferV18637
open GoldbachCircleMethodOddChannelEventualAbsorptionV18658
open GoldbachCircleMethodDiagonalCompensatedEvenSubchannelsV18667
open GoldbachCircleMethodSignedMagnitudeIdentityV18628
open GoldbachCircleMethodOddOddSmallCoreLargePerturbationV18670
open GoldbachCircleMethodOddOddLargeDenominatorEnergyReductionV18671

namespace GoldbachCircleMethodOddOddSmallCoreEnergyCeilingV18672

/-- If `reserve` is nonnegative, its subtraction from `deficit` can only
reduce the harmful negative part of `reserve - deficit`. -/
theorem negativePart_reserve_sub_deficit_sq_le_deficit_sq
    (reserve deficit : Real) (hreserve : 0 <= reserve) :
    negativePart (reserve - deficit) ^ 2 <= deficit ^ 2 := by
  unfold negativePart
  by_cases hdiff : 0 <= reserve - deficit
  · rw [max_eq_right (neg_nonpos.mpr hdiff)]
    nlinarith [sq_nonneg deficit]
  · have hle : reserve <= deficit := by linarith
    have hdeficit : 0 <= deficit := hreserve.trans hle
    have hneg : 0 <= -(reserve - deficit) := by linarith
    rw [max_eq_left hneg]
    nlinarith [sq_nonneg reserve]

/-- Specialization to the literal V1.8.670 compensated small-denominator
Odd-Odd core.  The nonnegative term is exactly the V1.8.667 diagonal reserve. -/
theorem negativePart_compensatedSmallDenominatorCore_sq_le_deficit_sq
    (M P R N : Nat) :
    negativePart (compensatedSmallDenominatorCore M P R N) ^ 2 <=
      smallDenominatorOddOddDeficit M P R N ^ 2 := by
  unfold compensatedSmallDenominatorCore
  exact negativePart_reserve_sub_deficit_sq_le_deficit_sq
    (explicitDiagonalOddOddReserve M P R N)
    (smallDenominatorOddOddDeficit M P R N)
    (explicitDiagonalOddOddReserve_nonneg M P R N)

/-- Finite-moment ceiling on any unchanged target carrier.  This is an
inequality between two exact finite quantities, not an estimate of the right
side. -/
theorem compensatedSmallDenominatorCore_moment_le_deficit_energy
    (M P R : Nat) (s : Finset Nat) :
    negativePartSquaredMoment s
        (compensatedSmallDenominatorCore M P R) <=
      squareEnergy s (smallDenominatorOddOddDeficit M P R) := by
  unfold negativePartSquaredMoment squareEnergy
  exact Finset.sum_le_sum fun N _hN =>
    negativePart_compensatedSmallDenominatorCore_sq_le_deficit_sq M P R N

/-- Exact signed-magnitude normalization of the V1.8.670 small-core budget.
The denominator `25088` is half of `50176`, so the right-hand threshold is
twice the left-hand threshold; no estimate is introduced. -/
theorem project_smallCore_moment_lt_iff_signedGap (M : Nat) :
    negativePartSquaredMoment (evenTargetBlock M)
        (compensatedSmallDenominatorCore M
          (oddProjectWidth M) (oddProjectRadius M)) <
        (M : Real) ^ 2 / 50176 <->
      squareEnergy (evenTargetBlock M)
          (compensatedSmallDenominatorCore M
            (oddProjectWidth M) (oddProjectRadius M)) -
        signedMagnitudeCorrelation (evenTargetBlock M)
          (compensatedSmallDenominatorCore M
            (oddProjectWidth M) (oddProjectRadius M)) <
        (M : Real) ^ 2 / 25088 := by
  rw [negativePartSquaredMoment_eq_half_signed_gap]
  constructor <;> intro h <;> nlinarith

/-- A strict square-energy estimate for the literal small-denominator deficit
is sufficient for the exact V1.8.670 one-sided small-core input.  The premise
remains an open analytic obligation. -/
theorem project_smallCore_moment_lt_of_smallDeficitEnergy
    (M : Nat)
    (hSmallEnergy :
      squareEnergy (evenTargetBlock M)
          (smallDenominatorOddOddDeficit M
            (oddProjectWidth M) (oddProjectRadius M)) <
        (M : Real) ^ 2 / 50176) :
    negativePartSquaredMoment (evenTargetBlock M)
        (compensatedSmallDenominatorCore M
          (oddProjectWidth M) (oddProjectRadius M)) <
      (M : Real) ^ 2 / 50176 :=
  (compensatedSmallDenominatorCore_moment_le_deficit_energy M
    (oddProjectWidth M) (oddProjectRadius M) (evenTargetBlock M)).trans_lt
      hSmallEnergy

/-- Conditional project handoff through V1.8.670.  Both the small signed
deficit energy and the large perturbation energy remain explicit inputs. -/
theorem compensatedOddOdd_project_budget_of_smallDeficit_and_largeEnergy
    (M : Nat)
    (hscale : 2 * oddProjectWidth M * oddProjectRadius M < M)
    (hSmallEnergy :
      squareEnergy (evenTargetBlock M)
          (smallDenominatorOddOddDeficit M
            (oddProjectWidth M) (oddProjectRadius M)) <
        (M : Real) ^ 2 / 50176)
    (hLarge :
      squareEnergy (evenTargetBlock M)
          (largeDenominatorPerturbation M
            (oddProjectWidth M) (oddProjectRadius M)) <
        (M : Real) ^ 2 / 50176) :
    negativePartSquaredMoment (evenTargetBlock M)
        (fun N => -GoldbachCircleMethodDiagonalCompensatedEvenSubchannelsV18667.compensatedOddOddDeficit
          M (oddProjectWidth M) (oddProjectRadius M) N) <
      (M : Real) ^ 2 / 12544 := by
  exact compensatedOddOdd_project_budget_of_smallCore_and_largeEnergy M hscale
    (project_smallCore_moment_lt_of_smallDeficitEnergy M hSmallEnergy) hLarge

/-- The same conditional handoff with the V1.8.671 fixed-denominator aggregate
as the large-channel premise.  Both analytic estimates remain explicit. -/
theorem compensatedOddOdd_project_budget_of_smallDeficit_and_fixedLargeBudget
    (M : Nat)
    (hscale : 2 * oddProjectWidth M * oddProjectRadius M < M)
    (hSmallEnergy :
      squareEnergy (evenTargetBlock M)
          (smallDenominatorOddOddDeficit M
            (oddProjectWidth M) (oddProjectRadius M)) <
        (M : Real) ^ 2 / 50176)
    (hFixed :
      ((largeDenominatorCarrier (oddProjectRadius M)).card : Real) *
        ∑ q ∈ largeDenominatorCarrier (oddProjectRadius M),
          squareEnergy (evenTargetBlock M)
            (fixedLargeDenominatorPerturbation M
              (oddProjectWidth M) (oddProjectRadius M) q) <
        (M : Real) ^ 2 / 50176) :
    negativePartSquaredMoment (evenTargetBlock M)
        (fun N => -GoldbachCircleMethodDiagonalCompensatedEvenSubchannelsV18667.compensatedOddOddDeficit
          M (oddProjectWidth M) (oddProjectRadius M) N) <
      (M : Real) ^ 2 / 12544 := by
  apply compensatedOddOdd_project_budget_of_smallDeficit_and_largeEnergy M hscale
    hSmallEnergy
  exact project_largePerturbation_energy_lt_of_fixedDenominatorBudget M hFixed

end GoldbachCircleMethodOddOddSmallCoreEnergyCeilingV18672
