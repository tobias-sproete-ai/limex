import GoldbachCircleMethodVariableMeanDiagonalNormalFormV18334
import GoldbachCircleMethodActualUnitPairSignedResidualV18214

/-!
# Goldbach V1.8.335: variable mean unit-pair normal form

This module rewrites the variable pairwise arithmetic mean as the sum of one
fixed signed diagonal residual and the genuine finite unit-pair bracket at
each spatial weight pair.  It exposes the exact remaining arithmetic reserve
problem after the V1.8.333 pairwise Abel absorption.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodVariableMeanUnitPairNormalFormV18335

open GoldbachCircleMethodActualFrozenModelCompleteDiagonalV18213
open GoldbachCircleMethodActualUnitPairSignedResidualV18214
open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodExceptionalWeightBoundaryV18128
open GoldbachCircleMethodFullFrozenPairwiseIntervalV18323
open GoldbachCircleMethodPairwiseMeanDiagonalCompatibilityV18324
open GoldbachCircleMethodPowerWeightAbelIntervalV18331
open GoldbachCircleMethodVariableMeanDiagonalNormalFormV18334

/-- The genuine finite sum of unit-pair brackets at the two variable power
weights. -/
noncomputable def variableUnitPairBracketSum
    (r N A T : ℕ) [NeZero r]
    (chi : DirichletCharacter ℂ r) (b : ℝ) : ℂ :=
  ∑ i ∈ Finset.range T,
    unitPairBracket r (N : ℤ) chi
      (powerWeight b (N - (A + i)) : ℂ)
      (powerWeight b (A + i) : ℂ)

/-- The unit-pair bracket depends on its integer target only through its
residue modulo the conductor. -/
theorem unitPairBracket_congr_target
    (r : ℕ) [NeZero r] (chi : DirichletCharacter ℂ r)
    {m₁ m₂ : ℤ} (hm : (m₁ : ZMod r) = (m₂ : ZMod r))
    (t₁ t₂ : ℂ) :
    unitPairBracket r m₁ chi t₁ t₂ =
      unitPairBracket r m₂ chi t₁ t₂ := by
  have hcarrier :
      GoldbachCircleMethodActualUnitPairArithmeticV18194.unitPairResidues r m₁ =
        GoldbachCircleMethodActualUnitPairArithmeticV18194.unitPairResidues r m₂ := by
    ext x
    simp only [GoldbachCircleMethodActualUnitPairArithmeticV18194.mem_unitPairResidues]
    rw [hm]
  unfold unitPairBracket
  rw [hcarrier]
  apply Finset.sum_congr rfl
  intro x _hx
  rw [hm]

/-- One frozen pairwise mean is exactly a fixed signed residual plus the
genuine unit-pair bracket. -/
theorem fullFrozenPairwiseMean_eq_signedResidual_add_unitPairBracket
    {Q K : ℕ} [NeZero K] (hQ : 1 ≤ Q)
    (hK : ∀ q : PositiveLevel Q, q.val ∣ K)
    (r : PositiveLevel Q)
    (chi : {χ : DirichletCharacter ℂ r.val // χ.IsPrimitive})
    (hInv : chi.val⁻¹ = chi.val)
    (v w : ℕ → ℂ) (t₁ t₂ : ℂ) (N : ℕ) :
    fullFrozenPairwiseMean hQ r chi v w t₁ t₂ N =
      signedDiagonalResidual hK r v w (N : ZMod K) +
        ((r.val : ℂ) / (r.val.totient : ℂ) ^ 2) *
          coupledDiagonal hK r v w (N : ZMod K) *
          unitPairBracket r.val (N : ℤ) chi.val t₁ t₂ := by
  have htarget :
      ((((N : ZMod K).val : ℕ) : ℤ) : ZMod r.val) =
        ((N : ℤ) : ZMod r.val) := by
    calc
      ((((N : ZMod K).val : ℕ) : ℤ) : ZMod r.val) =
          ZMod.castHom (hK r) (ZMod r.val) (N : ZMod K) :=
        actual_unit_pair_target_readback (hK r) (N : ZMod K)
      _ = ((N : ℤ) : ZMod r.val) := by simp
  calc
    _ = (∑ x : ZMod K,
          frozenCoefficient hQ r chi v t₁ ((N : ZMod K) - x) *
            frozenCoefficient hQ r chi w t₂ x) / (K : ℂ) :=
      (normalized_complete_frozen_eq_pairwiseMean
        hQ hK r chi hInv v w t₁ t₂ N).symm
    _ = signedDiagonalResidual hK r v w (N : ZMod K) +
          ((r.val : ℂ) / (r.val.totient : ℂ) ^ 2) *
            coupledDiagonal hK r v w (N : ZMod K) *
            unitPairBracket r.val (((N : ZMod K).val : ℕ) : ℤ)
              chi.val t₁ t₂ :=
      actual_frozen_model_unit_pair_residual
        hQ hK r chi hInv v w t₁ t₂ (N : ZMod K)
    _ = _ := by
      rw [unitPairBracket_congr_target r.val chi.val htarget]

/-- Exact collected unit-pair normal form.  The common-period object is used
only to certify the arithmetic mean; V1.8.333 already controls the incomplete
interval without that period. -/
theorem powerPairwiseVariableMean_eq_residual_add_unitPairBracketSum
    {Q K : ℕ} [NeZero K] (hQ : 1 ≤ Q)
    (hK : ∀ q : PositiveLevel Q, q.val ∣ K)
    (r : PositiveLevel Q)
    (chi : {χ : DirichletCharacter ℂ r.val // χ.IsPrimitive})
    (hInv : chi.val⁻¹ = chi.val)
    (v w : ℕ → ℂ) (b : ℝ) (N A T : ℕ) :
    powerPairwiseVariableMean hQ r chi v w b N A T =
      (T : ℂ) * signedDiagonalResidual hK r v w (N : ZMod K) +
        ((r.val : ℂ) / (r.val.totient : ℂ) ^ 2) *
          coupledDiagonal hK r v w (N : ZMod K) *
          variableUnitPairBracketSum r.val N A T chi.val b := by
  rw [powerPairwiseVariableMean_eq_sum_fullFrozenPairwiseMean]
  unfold variableUnitPairBracketSum
  simp_rw [fullFrozenPairwiseMean_eq_signedResidual_add_unitPairBracket
    hQ hK r chi hInv v w]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_const, nsmul_eq_mul]
  rw [Finset.card_range]
  rw [← Finset.mul_sum]

end GoldbachCircleMethodVariableMeanUnitPairNormalFormV18335
