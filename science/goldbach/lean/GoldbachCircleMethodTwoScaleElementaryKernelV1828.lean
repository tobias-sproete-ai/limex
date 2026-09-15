import GoldbachCircleMethodFixedScaleClassIICompositionV1825
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.Exponential

/-!
# Two-scale elementary arithmetic kernel, V1.8.28

Only the corrected `N - 1` budget and finite one-sided Markov arithmetic are
formalized here. No Fourier mask, Ramanujan sum, singular-series floor, or
external analytic estimate is defined or assumed.
-/

set_option autoImplicit false

namespace GoldbachCircleMethodTwoScaleElementaryKernelV1828

open GoldbachCircleMethodExceptionalTransferV1823

/-- The explicit lower-floor constant used by the two-scale candidate. -/
noncomputable def twoScaleKappa : Real :=
  2 - Real.exp (Real.pi ^ 2 / 24)

theorem twoScaleKappa_gt_two_sevenths :
    (2 : Real) / 7 < twoScaleKappa := by
  have hpi : Real.pi < (3.15 : Real) := Real.pi_lt_d2
  have hpiSq : Real.pi ^ 2 < (10 : Real) := by
    nlinarith [Real.pi_pos]
  have hxPos : 0 < Real.pi ^ 2 / (24 : Real) := by positivity
  have hx : Real.pi ^ 2 / (24 : Real) < (5 : Real) / 12 := by
    linarith
  have hxTwo : Real.pi ^ 2 / (24 : Real) < 2 := hx.trans (by norm_num)
  have hExp := Real.exp_lt_two_add_div_two_sub hxPos hxTwo
  have hFrac :
      (2 + Real.pi ^ 2 / 24) / (2 - Real.pi ^ 2 / 24) <
        (12 : Real) / 7 := by
    rw [div_lt_iff₀ (by linarith)]
    linarith
  have hExpBound : Real.exp (Real.pi ^ 2 / 24) < (12 : Real) / 7 :=
    hExp.trans hFrac
  dsimp [twoScaleKappa]
  linarith

/-- Corrected `N - 1` major-budget implication. -/
theorem corrected_major_budget
    (M N eta major : Real)
    (hM : 2 ≤ M)
    (hN : M / 2 ≤ N)
    (hMajor : twoScaleKappa * (N - 1) - M * eta ≤ major)
    (hGate : 2 / (7 * M) + eta ≤ 1 / 14) :
    M / 14 ≤ major := by
  have hMPos : 0 < M := by linarith
  have hNOne : 0 ≤ N - 1 := by linarith
  have hKappa : (2 : Real) / 7 ≤ twoScaleKappa :=
    twoScaleKappa_gt_two_sevenths.le
  have hScaled : (2 / 7) * (N - 1) ≤ twoScaleKappa * (N - 1) :=
    mul_le_mul_of_nonneg_right hKappa hNOne
  have hGateMul := mul_le_mul_of_nonneg_left hGate hMPos.le
  have hCancel : M * (2 / (7 * M)) = (2 : Real) / 7 := by
    field_simp
  rw [mul_add, hCancel] at hGateMul
  nlinarith

/-- Markov scale whose `2/35` threshold is exactly `M/28`. -/
noncomputable def twoScaleMarkovX (M : Real) : Real := 5 * M / 8

theorem classIIThreshold_mul_twoScaleMarkovX (M : Real) :
    classIIThreshold * twoScaleMarkovX M = M / 28 := by
  norm_num [classIIThreshold, twoScaleMarkovX]
  ring

/-- `4 M² B` moment input gives the exact factor `3136 = 4 * 28²`. -/
theorem bad_card_le_3136_of_moment
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (H : ι → Real) (M B : Real)
    (hM : 0 < M)
    (hMoment : negativePartSquaredMoment s H ≤ 4 * M ^ 2 * B) :
    ((badIndices s H (twoScaleMarkovX M)).card : Real) ≤ 3136 * B := by
  have hX : 0 < twoScaleMarkovX M := by
    dsimp [twoScaleMarkovX]
    positivity
  have hTransfer := bad_card_le_of_negativePart_moment
    s H (twoScaleMarkovX M) (4 * M ^ 2 * B) hX hMoment
  rw [classIIThreshold_mul_twoScaleMarkovX] at hTransfer
  calc
    ((badIndices s H (twoScaleMarkovX M)).card : Real) ≤
        (4 * M ^ 2 * B) / (M / 28) ^ 2 := hTransfer
    _ = 3136 * B := by
      field_simp
      ring

end GoldbachCircleMethodTwoScaleElementaryKernelV1828
