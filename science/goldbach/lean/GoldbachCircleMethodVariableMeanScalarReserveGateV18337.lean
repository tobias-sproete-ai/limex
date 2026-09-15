import GoldbachCircleMethodVariableUnitPairBracketReserveV18336

/-!
# Goldbach V1.8.337: variable mean scalar reserve gate

The exact unit-pair normal form is projected to real scalars.  Since the
variable bracket sum is real, no uncontrolled imaginary cross term survives.
This reduces positivity of the variable arithmetic mean to the sign of the
fixed signed diagonal residual together with already explicit lower bounds
for the coupled diagonal and bracket sum.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodVariableMeanScalarReserveGateV18337

open GoldbachCircleMethodActualFrozenModelCompleteDiagonalV18213
open GoldbachCircleMethodActualUnitPairSignedResidualV18214
open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodPowerWeightAbelIntervalV18331
open GoldbachCircleMethodVariableMeanUnitPairNormalFormV18335
open GoldbachCircleMethodVariableUnitPairBracketReserveV18336

/-- Exact scalar normal form.  The self-inverse hypothesis eliminates the
only possible imaginary cross term from the variable bracket sum. -/
theorem powerPairwiseVariableMean_re_eq_scalar_normal_form
    {Q K : ℕ} [NeZero K] (hQ : 1 ≤ Q)
    (hK : ∀ q : PositiveLevel Q, q.val ∣ K)
    (r : PositiveLevel Q)
    (chi : {χ : DirichletCharacter ℂ r.val // χ.IsPrimitive})
    (hInv : chi.val⁻¹ = chi.val)
    (v w : ℕ → ℂ) (b : ℝ) (N A T : ℕ) :
    (powerPairwiseVariableMean hQ r chi v w b N A T).re =
      (T : ℝ) * (signedDiagonalResidual hK r v w (N : ZMod K)).re +
        ((r.val : ℝ) / (r.val.totient : ℝ) ^ 2) *
          (coupledDiagonal hK r v w (N : ZMod K)).re *
          (variableUnitPairBracketSum r.val N A T chi.val b).re := by
  rw [powerPairwiseVariableMean_eq_residual_add_unitPairBracketSum
    hQ hK r chi hInv v w]
  have him := variableUnitPairBracketSum_im_eq_zero
    r.val N A T chi.val hInv b
  have hscale :
      ((r.val : ℂ) / (r.val.totient : ℂ) ^ 2) =
        (((r.val : ℝ) / (r.val.totient : ℝ) ^ 2 : ℝ) : ℂ) := by
    norm_cast
    push_cast
    rfl
  rw [hscale]
  simp only [Complex.add_re, Complex.mul_re, Complex.natCast_re,
    Complex.natCast_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, mul_zero, sub_zero, him]

/-- Generic monotone reserve transfer.  No sign is assumed for the coupled
diagonal or bracket sum beyond the explicitly supplied lower floors.  The
only structural sign premise is the fixed signed-residual gate. -/
theorem powerPairwiseVariableMean_re_lower_of_scalar_floors
    {Q K : ℕ} [NeZero K] (hQ : 1 ≤ Q)
    (hK : ∀ q : PositiveLevel Q, q.val ∣ K)
    (r : PositiveLevel Q)
    (chi : {χ : DirichletCharacter ℂ r.val // χ.IsPrimitive})
    (hInv : chi.val⁻¹ = chi.val)
    (v w : ℕ → ℂ) (b : ℝ) (N A T : ℕ)
    (C D : ℝ)
    (hResidual : 0 ≤ (signedDiagonalResidual hK r v w (N : ZMod K)).re)
    (hC0 : 0 ≤ C)
    (hC : C ≤ (coupledDiagonal hK r v w (N : ZMod K)).re)
    (hD0 : 0 ≤ D)
    (hD : D ≤ (variableUnitPairBracketSum r.val N A T chi.val b).re) :
    ((r.val : ℝ) / (r.val.totient : ℝ) ^ 2) * C * D ≤
      (powerPairwiseVariableMean hQ r chi v w b N A T).re := by
  have hscale : 0 ≤ (r.val : ℝ) / (r.val.totient : ℝ) ^ 2 := by positivity
  have hCactual : 0 ≤
      (coupledDiagonal hK r v w (N : ZMod K)).re := hC0.trans hC
  have hprod : C * D ≤
      (coupledDiagonal hK r v w (N : ZMod K)).re *
        (variableUnitPairBracketSum r.val N A T chi.val b).re :=
    mul_le_mul hC hD hD0 hCactual
  have hscaled := mul_le_mul_of_nonneg_left hprod hscale
  rw [powerPairwiseVariableMean_re_eq_scalar_normal_form
    hQ hK r chi hInv v w b N A T]
  have hT : 0 ≤ (T : ℝ) := Nat.cast_nonneg T
  nlinarith [mul_nonneg hT hResidual]

end GoldbachCircleMethodVariableMeanScalarReserveGateV18337
