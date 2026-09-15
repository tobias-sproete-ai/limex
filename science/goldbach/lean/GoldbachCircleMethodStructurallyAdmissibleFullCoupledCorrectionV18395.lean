import GoldbachCircleMethodStructurallyAdmissibleFullSecondMarginalV18394
import GoldbachCircleMethodCanonicalFullFirstMarginalQuarticV18382

/-!
# Goldbach V1.8.395: full coupled correction at quartic cutoff cost

The two source-bound target marginals are recombined with the literal frozen
model coefficients `t1*t2` and `t1+t2`.  This yields an exact target-sum
normal form followed by one `Q^4` norm budget for the complete coupled
correction of a structurally admissible active slot.

This is a finite boundary-cost theorem.  It neither proves that the budget is
absorbed by the positive reserve nor proves Goldbach.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodStructurallyAdmissibleFullCoupledCorrectionV18395

open GoldbachCircleMethodActualFrozenModelCompleteDiagonalV18213
open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodCanonicalCoupledFirstMarginalActualBindingV18381
open GoldbachCircleMethodCanonicalCoupledSecondMarginalSourceBindingV18391
open GoldbachCircleMethodCanonicalFullFirstMarginalQuarticV18382
open GoldbachCircleMethodCanonicalTargetLinearWeightBindingV18367
open GoldbachCircleMethodCanonicalTargetQuadraticWeightBindingV18385
open GoldbachCircleMethodFiniteResiduePrefixV1866
open GoldbachCircleMethodStructurallyAdmissibleActiveSlotV18258
open GoldbachCircleMethodStructurallyAdmissibleFullSecondMarginalV18394

/-- A structurally admissible primitive active character is nonprincipal. -/
theorem admissible_active_character_ne_one {Q : ℕ}
    (e : StructurallyAdmissibleActiveSlot Q) : e.val.2.val ≠ 1 := by
  intro hchi
  have hgt : 1 < e.val.1.val := e.property.1
  have hprim : e.val.2.val.conductor = e.val.1.val := e.val.2.property
  rw [hchi, DirichletCharacter.conductor_one] at hprim
  omega

/-- Direct source expression for the complete coupled correction after target
weight binding, before any estimate. -/
noncomputable def literalNormalizedActualCoupledCorrectionTargetSum
    {Q K : ℕ} [NeZero K]
    (hK : ∀ q : PositiveLevel Q, q.val ∣ K)
    (e : StructurallyAdmissibleActiveSlot Q)
    (v w : ℕ → ℂ) (t₁ t₂ : ℂ)
    (B A T : ℕ) (b : ℝ) : ℂ :=
  ∑ i ∈ Finset.range T,
    ((e.val.1.val : ℂ) / ((e.val.1.val.totient : ℂ) ^ 2)) *
      (t₁ * t₂ * (canonicalTargetQuadraticWeight B (A + 2 * i) b : ℂ) *
          e.val.2.val (-1) *
          unitCharacterSum e.val.1.val
            ((A + 2 * i : ℕ) : ZMod e.val.1.val) -
        (t₁ + t₂) * (canonicalTargetLinearWeight B (A + 2 * i) b : ℂ) *
          ((ArithmeticFunction.moebius e.val.1.val : ℤ) : ℂ) *
          e.val.2.val ((A + 2 * i : ℕ) : ZMod e.val.1.val)) *
      coupledDiagonal hK e.val.1 v w ((A + 2 * i : ℕ) : ZMod K)

/-- Exact recombination of the two canonical marginals into the direct
frozen-model correction target sum. -/
theorem literal_coupled_correction_eq_marginals
    {Q K : ℕ} [NeZero K]
    (hK : ∀ q : PositiveLevel Q, q.val ∣ K)
    (e : StructurallyAdmissibleActiveSlot Q)
    (v w : ℕ → ℂ) (t₁ t₂ : ℂ)
    (B A T : ℕ) (b : ℝ) :
    literalNormalizedActualCoupledCorrectionTargetSum
        hK e v w t₁ t₂ B A T b =
      t₁ * t₂ * normalizedActualCoupledSecondMarginal
          hK e v w B A T b -
        (t₁ + t₂) * normalizedActualCoupledFirstMarginal
          hK e.val.1 e.val.2.val v w B A T b := by
  unfold literalNormalizedActualCoupledCorrectionTargetSum
    normalizedActualCoupledSecondMarginal
    normalizedActualCoupledFirstMarginal
    actualCoupledSecondMarginalTargetSum
    actualCoupledFirstMarginalTargetSum
  simp_rw [Finset.mul_sum]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [Algebra.smul_def, Algebra.smul_def]
  simp only [Complex.coe_algebraMap]
  ring

/-- The complete source-bound coupled correction has quartic cutoff cost,
with the two scalar adjustment norms retained explicitly. -/
theorem literal_coupled_correction_norm_le_quartic
    {Q K : ℕ} [NeZero K]
    (hKperiod : ∀ q : PositiveLevel Q, q.val ∣ K)
    (e : StructurallyAdmissibleActiveSlot Q)
    (v w : ℕ → ℂ) (M : ℝ) (hM : 0 ≤ M)
    (hv : ∀ n, ‖v n‖ ≤ M) (hw : ∀ n, ‖w n‖ ≤ M)
    (t₁ t₂ : ℂ)
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
    ‖literalNormalizedActualCoupledCorrectionTargetSum
        hKperiod e v w t₁ t₂ B A (Kgrow + S) b‖ ≤
      ‖t₁‖ * ‖t₂‖ *
          (2 * (B : ℝ) * (3 + 4 * b) * (Q : ℝ) ^ 4 * M ^ 2) +
        ‖t₁ + t₂‖ *
          (8 * (B : ℝ) * (Q : ℝ) ^ 4 * M ^ 2) := by
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
  rw [literal_coupled_correction_eq_marginals]
  calc
    _ ≤ ‖t₁ * t₂ * normalizedActualCoupledSecondMarginal
          hKperiod e v w B A (Kgrow + S) b‖ +
        ‖(t₁ + t₂) * normalizedActualCoupledFirstMarginal
          hKperiod e.val.1 e.val.2.val v w B A (Kgrow + S) b‖ :=
      norm_sub_le _ _
    _ = ‖t₁‖ * ‖t₂‖ *
          ‖normalizedActualCoupledSecondMarginal
            hKperiod e v w B A (Kgrow + S) b‖ +
        ‖t₁ + t₂‖ *
          ‖normalizedActualCoupledFirstMarginal
            hKperiod e.val.1 e.val.2.val v w B A (Kgrow + S) b‖ := by
      simp only [norm_mul]
    _ ≤ _ := add_le_add
      (mul_le_mul_of_nonneg_left hsecond
        (mul_nonneg (norm_nonneg _) (norm_nonneg _)))
      (mul_le_mul_of_nonneg_left hfirst (norm_nonneg _))

end GoldbachCircleMethodStructurallyAdmissibleFullCoupledCorrectionV18395
