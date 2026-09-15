import GoldbachCircleMethodStructurallyAdmissibleFullCoupledCorrectionV18395
import GoldbachCircleMethodVariableUnitPairCorrectionFactorizationV18345

/-!
# Goldbach V1.8.396: source-bound variable coupled correction

V1.8.395 controls a two-coefficient frozen correction.  The variable source
model of V1.8.344 has a stricter coefficient contract: its linear and
quadratic weights are independently fixed by the canonical pair carrier.
This module binds that exact source correction to the two already controlled
marginals and inherits their `Q^4` budget.

No coefficients are reverse-engineered from a free pair `t₁,t₂`, and no
reserve absorption or Goldbach statement is asserted.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodSourceBoundVariableCoupledCorrectionV18396

open GoldbachCircleMethodActualFrozenModelCompleteDiagonalV18213
open GoldbachCircleMethodBlockPairCarrierV18227
open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodCanonicalCoupledFirstMarginalActualBindingV18381
open GoldbachCircleMethodCanonicalCoupledSecondMarginalSourceBindingV18391
open GoldbachCircleMethodCanonicalFullFirstMarginalQuarticV18382
open GoldbachCircleMethodCanonicalTargetLinearWeightBindingV18367
open GoldbachCircleMethodCanonicalTargetQuadraticWeightBindingV18385
open GoldbachCircleMethodStructurallyAdmissibleActiveSlotV18258
open GoldbachCircleMethodStructurallyAdmissibleFullCoupledCorrectionV18395
open GoldbachCircleMethodStructurallyAdmissibleFullSecondMarginalV18394
open GoldbachCircleMethodVariableUnitPairCorrectionFactorizationV18345
open GoldbachCircleMethodVariableUnitPairExactCorrectionV18344

/-- Literal target sum of the actual variable source correction from V1.8.344,
including the original active-conductor normalization and coupled diagonal.
The minus sign converts the V1.8.344 deficit convention into the correction
sign of the V1.8.213 frozen-model identity. -/
noncomputable def sourceNormalizedActualVariableCorrectionTargetSum
    {Q K : ℕ} [NeZero K]
    (hK : ∀ q : PositiveLevel Q, q.val ∣ K)
    (e : StructurallyAdmissibleActiveSlot Q)
    (v w : ℕ → ℂ) (B A T : ℕ) (b : ℝ) : ℂ :=
  ∑ i ∈ Finset.range T,
    -(((e.val.1.val : ℂ) / ((e.val.1.val.totient : ℂ) ^ 2)) *
      coupledDiagonal hK e.val.1 v w ((A + 2 * i : ℕ) : ZMod K) *
      variableUnitPairCorrectionSum e.val.1.val (A + 2 * i)
        (blockPairLower B (A + 2 * i))
        (blockPairUpper B (A + 2 * i) -
          blockPairLower B (A + 2 * i) + 1)
        e.val.2.val b)

/-- Exact source binding: the actual variable correction is the quadratic
second marginal minus the linear first marginal. -/
theorem source_variable_correction_eq_second_sub_first
    {Q K : ℕ} [NeZero K]
    (hK : ∀ q : PositiveLevel Q, q.val ∣ K)
    (e : StructurallyAdmissibleActiveSlot Q)
    (v w : ℕ → ℂ)
    (B A Kgrow S : ℕ) (b : ℝ)
    (hB : 2 ≤ B) (hBA : B ≤ A)
    (hNonempty : 2 * (B / 2 + 1) ≤ A)
    (hKgrow : 1 ≤ Kgrow) (hS : 1 ≤ S)
    (hFinal : A + 2 * Kgrow + 2 * (S - 1) ≤ 2 * B) :
    sourceNormalizedActualVariableCorrectionTargetSum
        hK e v w B A (Kgrow + S) b =
      normalizedActualCoupledSecondMarginal
          hK e v w B A (Kgrow + S) b -
        normalizedActualCoupledFirstMarginal
          hK e.val.1 e.val.2.val v w B A (Kgrow + S) b := by
  unfold sourceNormalizedActualVariableCorrectionTargetSum
    normalizedActualCoupledSecondMarginal
    normalizedActualCoupledFirstMarginal
    actualCoupledSecondMarginalTargetSum
    actualCoupledFirstMarginalTargetSum
  simp_rw [Finset.mul_sum]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  have hiT : i < Kgrow + S := Finset.mem_range.mp hi
  have hBN : B ≤ A + 2 * i := by omega
  have hN2B : A + 2 * i ≤ 2 * B := by omega
  have hInterval :
      blockPairLower B (A + 2 * i) ≤
        blockPairUpper B (A + 2 * i) := by
    unfold blockPairLower blockPairUpper
    omega
  rw [variableUnitPairCorrectionSum_eq_scalar_channels]
  rw [variableLinearPowerWeightSum_canonical_block_eq
      B (A + 2 * i) b (by omega) hBN hInterval]
  rw [variableQuadraticPowerWeightSum_canonical_block_eq
      B (A + 2 * i) b (by omega) hBN hInterval]
  rw [Algebra.smul_def, Algebra.smul_def]
  simp only [Complex.coe_algebraMap]
  ring

/-- The genuinely source-bound variable correction inherits the complete
pairwise-period `Q^4` budget. -/
theorem source_variable_correction_norm_le_quartic
    {Q K : ℕ} [NeZero K]
    (hKperiod : ∀ q : PositiveLevel Q, q.val ∣ K)
    (e : StructurallyAdmissibleActiveSlot Q)
    (v w : ℕ → ℂ) (M : ℝ) (hM : 0 ≤ M)
    (hv : ∀ n, ‖v n‖ ≤ M) (hw : ∀ n, ‖w n‖ ≤ M)
    (B A Kgrow S : ℕ) (b : ℝ) (hb : 0 ≤ b) (hA : Even A)
    (hB : 2 ≤ B) (hBA : B ≤ A)
    (hNonempty : 2 * (B / 2 + 1) ≤ A)
    (hKgrow : 1 ≤ Kgrow)
    (hGrowingLast : A + 2 * (Kgrow - 1) ≤
      GoldbachCircleMethodCanonicalTargetWeightPiecewiseGeometryV18368.blockPairTurningTarget B)
    (hS : 1 ≤ S)
    (hShrinkingFirst :
      GoldbachCircleMethodCanonicalTargetWeightPiecewiseGeometryV18368.blockPairTurningTarget B ≤
        A + 2 * Kgrow)
    (hFinal : A + 2 * Kgrow + 2 * (S - 1) ≤ 2 * B) :
    ‖sourceNormalizedActualVariableCorrectionTargetSum
        hKperiod e v w B A (Kgrow + S) b‖ ≤
      2 * (B : ℝ) * (3 + 4 * b) * (Q : ℝ) ^ 4 * M ^ 2 +
        8 * (B : ℝ) * (Q : ℝ) ^ 4 * M ^ 2 := by
  rw [source_variable_correction_eq_second_sub_first hKperiod e v w
    B A Kgrow S b hB hBA hNonempty hKgrow hS hFinal]
  have hsecond := normalized_actual_coupled_second_marginal_norm_le_quartic
    hKperiod e v w M hM hv hw B A Kgrow S b hb hB hBA hNonempty
      hKgrow hGrowingLast hS hShrinkingFirst hFinal
  have hfirstOr := normalized_actual_coupled_first_marginal_parity_complete
    hKperiod e.val.1 e.val.2.val (admissible_active_character_ne_one e)
      v w M hM hv hw B A Kgrow S b hb hA (by omega) hBA hNonempty
        hKgrow hGrowingLast hS hShrinkingFirst hFinal
  have hfirst :
      ‖normalizedActualCoupledFirstMarginal
        hKperiod e.val.1 e.val.2.val v w B A (Kgrow + S) b‖ ≤
        8 * (B : ℝ) * (Q : ℝ) ^ 4 * M ^ 2 := by
    rcases hfirstOr with hzero | hbound
    · rw [hzero, norm_zero]
      positivity
    · exact hbound
  exact (norm_sub_le _ _).trans (add_le_add hsecond hfirst)

end GoldbachCircleMethodSourceBoundVariableCoupledCorrectionV18396
