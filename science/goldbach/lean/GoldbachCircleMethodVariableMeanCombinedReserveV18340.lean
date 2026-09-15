import GoldbachCircleMethodSignedDiagonalResidualCounterexampleV18339

/-!
# V1.8.340: combined variable-mean reserve

V1.8.339 proves that the isolated signed residual can be negative.  This
module therefore eliminates that auxiliary split from the reserve gate.  It
collects the actual principal diagonal and the actual unit-pair deficit in one
exact scalar identity.  The resulting inequality is the minimal absorption
obligation left after the pairwise `Q^4` boundary cost from V1.8.333.

No sign or asymptotic estimate is asserted for the deficit, and no Goldbach
conclusion is made.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodVariableMeanCombinedReserveV18340

open GoldbachCircleMethodActualFrozenModelCompleteDiagonalV18213
open GoldbachCircleMethodActualUnitPairArithmeticV18194
open GoldbachCircleMethodActualUnitPairSignedResidualV18214
open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodPowerWeightAbelIntervalV18331
open GoldbachCircleMethodVariableMeanScalarReserveGateV18337
open GoldbachCircleMethodVariableMeanUnitPairNormalFormV18335

/-- The amount by which the summed unit-pair bracket falls short of the
unweighted literal unit-pair count over `T` spatial indices. -/
noncomputable def variableUnitPairDeficit
    (r N A T : ℕ) [NeZero r]
    (chi : DirichletCharacter ℂ r) (b : ℝ) : ℝ :=
  (T : ℝ) * (unitPairCount r (N : ℤ) : ℝ) -
    (variableUnitPairBracketSum r N A T chi b).re

/-- The literal unit-pair count depends only on the target residue modulo the
conductor. -/
theorem unitPairCount_congr_target
    (r : ℕ) [NeZero r] {m₁ m₂ : ℤ}
    (hm : (m₁ : ZMod r) = (m₂ : ZMod r)) :
    unitPairCount r m₁ = unitPairCount r m₂ := by
  unfold unitPairCount
  apply congrArg Finset.card
  ext x
  simp only [mem_unitPairResidues]
  rw [hm]

/-- Exact combined scalar normal form.  Unlike the V1.8.337 reserve theorem,
this identity requires no sign premise on `signedDiagonalResidual`. -/
theorem powerPairwiseVariableMean_re_eq_principal_sub_deficit
    {Q K : ℕ} [NeZero K] (hQ : 1 ≤ Q)
    (hK : ∀ q : PositiveLevel Q, q.val ∣ K)
    (r : PositiveLevel Q)
    (chi : {χ : DirichletCharacter ℂ r.val // χ.IsPrimitive})
    (hInv : chi.val⁻¹ = chi.val)
    (v w : ℕ → ℂ) (b : ℝ) (N A T : ℕ) :
    (powerPairwiseVariableMean hQ r chi v w b N A T).re =
      (T : ℝ) * (principalDiagonal hK v w (N : ZMod K)).re -
        ((r.val : ℝ) / (r.val.totient : ℝ) ^ 2) *
          (coupledDiagonal hK r v w (N : ZMod K)).re *
          variableUnitPairDeficit r.val N A T chi.val b := by
  rw [powerPairwiseVariableMean_re_eq_scalar_normal_form
    hQ hK r chi hInv v w b N A T]
  unfold signedDiagonalResidual variableUnitPairDeficit
  have hscale :
      ((r.val : ℂ) / (r.val.totient : ℂ) ^ 2) =
        (((r.val : ℝ) / (r.val.totient : ℝ) ^ 2 : ℝ) : ℂ) := by
    norm_cast
    push_cast
    rfl
  have htarget :
      ((((N : ZMod K).val : ℕ) : ℤ) : ZMod r.val) =
        ((N : ℤ) : ZMod r.val) := by
    calc
      ((((N : ZMod K).val : ℕ) : ℤ) : ZMod r.val) =
          ZMod.castHom (hK r) (ZMod r.val) (N : ZMod K) :=
        actual_unit_pair_target_readback (hK r) (N : ZMod K)
      _ = ((N : ℤ) : ZMod r.val) := by simp
  have hcount :
      unitPairCount r.val (((N : ZMod K).val : ℕ) : ℤ) =
        unitPairCount r.val (N : ℤ) :=
    unitPairCount_congr_target r.val htarget
  have hscalar :
      ((r.val : ℂ) / (r.val.totient : ℂ) ^ 2) *
          (unitPairCount r.val (((N : ZMod K).val : ℕ) : ℤ) : ℂ) =
        ((((r.val : ℝ) / (r.val.totient : ℝ) ^ 2) *
          (unitPairCount r.val (((N : ZMod K).val : ℕ) : ℤ) : ℝ) : ℝ) : ℂ) := by
    rw [hscale]
    norm_cast
  have hscaledCoupled :
      ((((r.val : ℂ) / (r.val.totient : ℂ) ^ 2) *
          (unitPairCount r.val (((N : ZMod K).val : ℕ) : ℤ) : ℂ) *
          coupledDiagonal hK r v w (N : ZMod K)).re) =
        ((r.val : ℝ) / (r.val.totient : ℝ) ^ 2) *
          (unitPairCount r.val (((N : ZMod K).val : ℕ) : ℤ) : ℝ) *
          (coupledDiagonal hK r v w (N : ZMod K)).re := by
    rw [hscalar]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    ring
  rw [Complex.sub_re, hscaledCoupled, hcount]
  ring

/-- Exact admission criterion for any desired real lower reserve `L`.  This is
the noncircular replacement for the false uniform residual-nonnegativity
route: the weighted deficit, and only that deficit, must fit inside the
principal budget above `L`. -/
theorem powerPairwiseVariableMean_re_ge_iff_deficit_absorbed
    {Q K : ℕ} [NeZero K] (hQ : 1 ≤ Q)
    (hK : ∀ q : PositiveLevel Q, q.val ∣ K)
    (r : PositiveLevel Q)
    (chi : {χ : DirichletCharacter ℂ r.val // χ.IsPrimitive})
    (hInv : chi.val⁻¹ = chi.val)
    (v w : ℕ → ℂ) (b : ℝ) (N A T : ℕ) (L : ℝ) :
    L ≤ (powerPairwiseVariableMean hQ r chi v w b N A T).re ↔
      ((r.val : ℝ) / (r.val.totient : ℝ) ^ 2) *
          (coupledDiagonal hK r v w (N : ZMod K)).re *
          variableUnitPairDeficit r.val N A T chi.val b ≤
        (T : ℝ) * (principalDiagonal hK v w (N : ZMod K)).re - L := by
  rw [powerPairwiseVariableMean_re_eq_principal_sub_deficit
    hQ hK r chi hInv v w b N A T]
  constructor <;> intro h <;> linarith

end GoldbachCircleMethodVariableMeanCombinedReserveV18340
