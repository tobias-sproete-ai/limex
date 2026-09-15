import GoldbachCircleMethodPrimitiveChiFourFullMeanNegativeWitnessV18360

/-!
# Goldbach V1.8.362: exact power-weight mean sign threshold

The pairwise-period `Q^4` estimate controls the incomplete-interval boundary,
but it does not determine the sign of the arithmetic mean.  At the genuine
primitive quadratic character modulo four and the symmetric target `4=2+2`,
this module computes the exact power-weight mean and isolates its sign gate.

No exceptional zero is asserted.  The final negative theorem is conditional
only on the displayed endpoint-weight inequality.  It is not a Goldbach
counterexample and does not establish any asymptotic obstruction.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped BigOperators Classical

namespace GoldbachCircleMethodPowerWeightMeanSignThresholdV18362

open GoldbachCircleMethodActualUnitPairArithmeticV18194
open GoldbachCircleMethodActualFrozenModelCompleteDiagonalV18213
open GoldbachCircleMethodActualUnitPairSignedResidualV18214
open GoldbachCircleMethodSignedDiagonalResidualCounterexampleV18339
open GoldbachCircleMethodPrimitiveChiFourFullMeanNegativeWitnessV18360
open GoldbachCircleMethodExceptionalWeightBoundaryV18128
open GoldbachCircleMethodFullFrozenPairwiseIntervalV18323
open GoldbachCircleMethodPowerWeightAbelIntervalV18331
open GoldbachCircleMethodVariableMeanDiagonalNormalFormV18334

/-- Exact chi-four bracket at target four for equal real weights. -/
theorem unitPairBracket_four_equal (s : ℝ) :
    unitPairBracket 4 4 complexChiFour (s : ℂ) (s : ℂ) =
      2 - 2 * (s : ℂ) ^ 2 := by
  rw [actual_unit_pair_bracket 4 4 complexChiFour complexChiFour_isPrimitive
    complexChiFour_inv (s : ℂ) (s : ℂ)]
  rw [unitPairCount_four_four]
  rw [unitCharacterSum_four_four]
  have hminus : (-1 : ZMod 4) = (3 : ZMod 4) := by
    change (3 : ZMod 4) = (3 : ZMod 4)
    rfl
  rw [hminus, complexChiFour_three]
  norm_num [complexChiFour, ZMod.χ₄]
  ring

/-- Exact frozen arithmetic mean at target four. -/
theorem fullFrozenPairwiseMean_four_equal (s : ℝ) :
    (fullFrozenPairwiseMean
      (by norm_num : 1 ≤ 4) fourLevel complexChiFourPrimitive
      (fun _ => ((1 : ℝ) : ℂ)) (fun _ => (1 : ℂ))
      (s : ℂ) (s : ℂ) 4).re = (7 : ℝ) / 4 - 2 * s ^ 2 := by
  rw [GoldbachCircleMethodVariableMeanUnitPairNormalFormV18335.fullFrozenPairwiseMean_eq_signedResidual_add_unitPairBracket
    (by norm_num : 1 ≤ 4) divisorsOfTwelve fourLevel complexChiFourPrimitive
    complexChiFour_inv (fun _ => ((1 : ℝ) : ℂ)) (fun _ => (1 : ℂ))
    (s : ℂ) (s : ℂ) 4]
  change
    (signedDiagonalResidual divisorsOfTwelve fourLevel
          (fun _ => ((1 : ℝ) : ℂ)) (fun _ => (1 : ℂ)) (4 : ZMod 12) +
        ((4 : ℂ) / (Nat.totient 4 : ℂ) ^ 2) *
          coupledDiagonal divisorsOfTwelve fourLevel
            (fun _ => ((1 : ℝ) : ℂ)) (fun _ => (1 : ℂ)) (4 : ZMod 12) *
          unitPairBracket 4 (4 : ℤ) complexChiFour (s : ℂ) (s : ℂ)).re =
      (7 : ℝ) / 4 - 2 * s ^ 2
  rw [unitPairBracket_four_equal, Complex.add_re, signedDiagonalResidual_four_negative]
  have htot : Nat.totient 4 = 2 := by decide
  rw [htot]
  norm_num [Complex.mul_re]
  have hC :
      (coupledDiagonal divisorsOfTwelve fourLevel
        (fun _ => (1 : ℂ)) (fun _ => (1 : ℂ)) (4 : ZMod 12)).re = 1 := by
    simpa using coupledDiagonal_four_four_re
  rw [hC]
  simp only [pow_two, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero]
  norm_num
  ring

/-- The genuine one-point power-weight mean at the symmetric split `4=2+2`
has this exact closed form. -/
theorem powerPairwiseVariableMean_four_symmetric (b : ℝ) :
    (powerPairwiseVariableMean
      (by norm_num : 1 ≤ 4) fourLevel complexChiFourPrimitive
      (fun _ => ((1 : ℝ) : ℂ)) (fun _ => (1 : ℂ)) b 4 2 1).re =
      (7 : ℝ) / 4 - 2 * (powerWeight b 2) ^ 2 := by
  simp only [fourLevel]
  rw [powerPairwiseVariableMean_eq_sum_fullFrozenPairwiseMean]
  rw [Finset.sum_range_succ, Finset.sum_range_zero]
  simp only [zero_add, Nat.reduceAdd, Nat.reduceSub]
  simpa only [fourLevel] using
    fullFrozenPairwiseMean_four_equal (powerWeight b 2)

/-- Exact fail-closed sign gate: if the symmetric endpoint weight crosses
`sqrt(7/8)`, the arithmetic mean is negative. -/
theorem powerPairwiseVariableMean_four_symmetric_negative
    (b : ℝ) (hweight : (7 : ℝ) / 8 < (powerWeight b 2) ^ 2) :
    (powerPairwiseVariableMean
      (by norm_num : 1 ≤ 4) fourLevel complexChiFourPrimitive
      (fun _ => ((1 : ℝ) : ℂ)) (fun _ => (1 : ℂ)) b 4 2 1).re < 0 := by
  rw [powerPairwiseVariableMean_four_symmetric]
  linarith

end GoldbachCircleMethodPowerWeightMeanSignThresholdV18362
