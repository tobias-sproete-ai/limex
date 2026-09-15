import GoldbachCircleMethodAttestedAdjustedDeficitAbsorptionV18343

/-!
# V1.8.344: exact variable unit-pair correction

The crude zero-gap lower bound is not the only information available for the
unit-pair brackets.  The older mixed Ramanujan/character orthogonality theorem
V1.8.214 gives an exact bracket identity.  This module sums that identity over
the spatially varying power weights and identifies the V1.8.340 deficit with
one exact correction sum.

No estimate or sign is imposed on the correction.  The purpose is to expose
the two arithmetic channels that can exhibit cancellation, rather than losing
them inside an energy norm or a common-LCM bound.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodVariableUnitPairExactCorrectionV18344

open GoldbachCircleMethodActualUnitPairArithmeticV18194
open GoldbachCircleMethodActualUnitPairSignedResidualV18214
open GoldbachCircleMethodActualUnitPairWeightedReserveV18195
open GoldbachCircleMethodExceptionalModelDiagonalV18107
open GoldbachCircleMethodExceptionalWeightBoundaryV18128
open GoldbachCircleMethodFiniteResiduePrefixV1866
open GoldbachCircleMethodGeneralCoprimeCharacterV1868
open GoldbachCircleMethodVariableMeanCombinedReserveV18340
open GoldbachCircleMethodVariableMeanUnitPairNormalFormV18335

/-- Exact per-position correction: a linear primitive-character marginal
minus the quadratic Ramanujan self-convolution channel. -/
noncomputable def variableUnitPairCorrectionSum
    (r N A T : ℕ) [NeZero r]
    (chi : DirichletCharacter ℂ r) (b : ℝ) : ℂ :=
  ∑ i ∈ Finset.range T,
    (((powerWeight b (N - (A + i)) : ℂ) +
        (powerWeight b (A + i) : ℂ)) *
        ((ArithmeticFunction.moebius r : ℤ) : ℂ) * chi (N : ZMod r) -
      (powerWeight b (N - (A + i)) : ℂ) *
        (powerWeight b (A + i) : ℂ) * chi (-1) *
        unitCharacterSum r (N : ZMod r))

/-- Summed exact mixed-orthogonality normal form for the variable bracket.
The literal carrier count is separated from the two oscillatory channels. -/
theorem variableUnitPairBracketSum_eq_count_sub_exactCorrection
    (r N A T : ℕ) [NeZero r]
    (chi : DirichletCharacter ℂ r) (hchi : chi.IsPrimitive)
    (hInv : chi⁻¹ = chi) (b : ℝ) :
    variableUnitPairBracketSum r N A T chi b =
      (T : ℂ) * (unitPairCount r (N : ℤ) : ℂ) -
        variableUnitPairCorrectionSum r N A T chi b := by
  unfold variableUnitPairBracketSum variableUnitPairCorrectionSum
  calc
    (∑ i ∈ Finset.range T,
        unitPairBracket r (N : ℤ) chi
          (powerWeight b (N - (A + i)) : ℂ)
          (powerWeight b (A + i) : ℂ)) =
        ∑ i ∈ Finset.range T,
          ((unitPairCount r (N : ℤ) : ℂ) -
            ((((powerWeight b (N - (A + i)) : ℂ) +
                (powerWeight b (A + i) : ℂ)) *
                ((ArithmeticFunction.moebius r : ℤ) : ℂ) *
                chi (N : ZMod r)) -
              ((powerWeight b (N - (A + i)) : ℂ) *
                (powerWeight b (A + i) : ℂ) * chi (-1) *
                unitCharacterSum r (N : ZMod r)))) := by
      apply Finset.sum_congr rfl
      intro i _hi
      rw [actual_unit_pair_bracket r (N : ℤ) chi hchi hInv]
      simp only [Int.cast_natCast]
      ring
    _ = _ := by
      rw [Finset.sum_sub_distrib]
      simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_range]

/-- The scalar deficit of V1.8.340 is exactly the real part of the summed
mixed Ramanujan/character correction. -/
theorem variableUnitPairDeficit_eq_exactCorrection_re
    (r N A T : ℕ) [NeZero r]
    (chi : DirichletCharacter ℂ r) (hchi : chi.IsPrimitive)
    (hInv : chi⁻¹ = chi) (b : ℝ) :
    variableUnitPairDeficit r N A T chi b =
      (variableUnitPairCorrectionSum r N A T chi b).re := by
  unfold variableUnitPairDeficit
  rw [variableUnitPairBracketSum_eq_count_sub_exactCorrection
    r N A T chi hchi hInv b]
  simp only [Complex.sub_re, Complex.mul_re, Complex.natCast_re,
    Complex.natCast_im, mul_zero, sub_zero]
  ring

end GoldbachCircleMethodVariableUnitPairExactCorrectionV18344
