import GoldbachCircleMethodCollisionLiteralWeightFactorizationV18555
import GoldbachCircleMethodLiteralCoefficientDiagonalMajorantV18533

/-!
# Goldbach V1.8.556: collision totient-ratio envelope

The complement levels carried by the periodic atom are combined with the
literal reciprocal-totient coefficients.  On the genuine active carriers,
`l^2 * ‖side(r,l)‖^2` is bounded by the square of the two local ratios
`(r/phi(r)) * (l/phi(l))`, the input envelope, and the primitive source
energy.  Thus no bare polynomial `l*k` loss remains in the pointwise
collision-energy majorant.
-/

set_option autoImplicit false

open scoped BigOperators Classical ComplexConjugate

namespace GoldbachCircleMethodCollisionTotientRatioEnvelopeV18556

open GoldbachCircleMethodActualCompanionCompleteDiagonalV18204
open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodCanonicalCoupledFirstMarginalAggregationV18378
open GoldbachCircleMethodCollisionLiteralWeightFactorizationV18555
open GoldbachCircleMethodLiteralCoefficientDiagonalMajorantV18533
open GoldbachCircleMethodLogCutoffPresieveBindingV18120
open GoldbachCircleMethodPairwiseActiveCostAggregationV18318
open GoldbachCircleMethodPrimitiveBaseSlotEnergyV18474

/-- Positive local totient ratio. -/
noncomputable def levelTotientRatio (n : ℕ) : ℝ :=
  (n : ℝ) / (n.totient : ℝ)

theorem levelTotientRatio_nonneg (n : ℕ) : 0 ≤ levelTotientRatio n := by
  unfold levelTotientRatio
  positivity

/-- One active side absorbs its complementary level into the exact
reciprocal-totient coefficient. -/
theorem complement_sq_mul_literalCollisionSideWeight_norm_sq_le
    {Q : ℕ} (B N : ℕ) (H : ℝ) (w : ℕ → ℂ)
    (r l : PositiveLevel Q)
    (χ : {χ : DirichletCharacter ℂ r.val // χ.IsPrimitive})
    (V : ℝ)
    (hactive : r.val * l.val ≤ Q ∧ Nat.Coprime r.val l.val)
    (hw : ‖w (r.val * l.val)‖ ≤ V) :
    (l.val : ℝ) ^ 2 *
        ‖literalCollisionSideWeight B N H w r l χ‖ ^ 2 ≤
      (levelTotientRatio r.val * levelTotientRatio l.val) ^ 2 * V ^ 2 *
        ‖primitiveBaseSlotSource Q B N H ⟨r, χ⟩‖ ^ 2 := by
  have hcoeff : ‖literalCoefficient r l w‖ ≤
      V / (l.val.totient : ℝ) := by
    have h := literalCoefficient_norm_le_div_totient r l w V
      (fun _h => hw)
    rw [if_pos hactive] at h
    exact h
  have hpref :
      ‖(r.val : ℂ) / (r.val.totient : ℂ)‖ = levelTotientRatio r.val := by
    unfold levelTotientRatio
    rw [norm_div, Complex.norm_natCast, Complex.norm_natCast]
  have hphi : (l.val.totient : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.totient_pos.mpr
      (Nat.pos_of_ne_zero (NeZero.ne l.val))))
  have hnorm :
      (l.val : ℝ) * ‖literalCollisionSideWeight B N H w r l χ‖ ≤
        levelTotientRatio r.val * levelTotientRatio l.val * V *
          ‖primitiveBaseSlotSource Q B N H ⟨r, χ⟩‖ := by
    unfold literalCollisionSideWeight
    rw [norm_mul, norm_mul, hpref]
    have hratio : 0 ≤ levelTotientRatio r.val :=
      levelTotientRatio_nonneg r.val
    have hsrc :
        0 ≤ ‖primitiveBaseSlotSource Q B N H ⟨r, χ⟩‖ := norm_nonneg _
    have hinner :
        levelTotientRatio r.val * ‖literalCoefficient r l w‖ *
            ‖primitiveBaseSlotSource Q B N H ⟨r, χ⟩‖ ≤
          levelTotientRatio r.val * (V / (l.val.totient : ℝ)) *
            ‖primitiveBaseSlotSource Q B N H ⟨r, χ⟩‖ := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hcoeff hratio) hsrc
    calc
      (l.val : ℝ) *
          (levelTotientRatio r.val * ‖literalCoefficient r l w‖ *
            ‖primitiveBaseSlotSource Q B N H ⟨r, χ⟩‖) ≤
        (l.val : ℝ) *
          (levelTotientRatio r.val *
            (V / (l.val.totient : ℝ)) *
            ‖primitiveBaseSlotSource Q B N H ⟨r, χ⟩‖) := by
          exact mul_le_mul_of_nonneg_left hinner (by positivity)
      _ = levelTotientRatio r.val * levelTotientRatio l.val * V *
          ‖primitiveBaseSlotSource Q B N H ⟨r, χ⟩‖ := by
        unfold levelTotientRatio
        field_simp [hphi]
  calc
    (l.val : ℝ) ^ 2 *
        ‖literalCollisionSideWeight B N H w r l χ‖ ^ 2 =
      ((l.val : ℝ) *
        ‖literalCollisionSideWeight B N H w r l χ‖) ^ 2 := by ring
    _ ≤ (levelTotientRatio r.val * levelTotientRatio l.val * V *
          ‖primitiveBaseSlotSource Q B N H ⟨r, χ⟩‖) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hnorm 2
    _ = (levelTotientRatio r.val * levelTotientRatio l.val) ^ 2 * V ^ 2 *
        ‖primitiveBaseSlotSource Q B N H ⟨r, χ⟩‖ ^ 2 := by ring

/-- The collision-energy majorant after both complement levels have been
absorbed into their local totient ratios. -/
noncomputable def collisionLiteralTotientRatioEnvelopeEnergy
    (Q B : ℕ) (H V : ℝ)
    (r s : PositiveLevel Q) : ℝ :=
  ∑ N ∈ blockCarrier B,
    ∑ ψ : {ψ : DirichletCharacter ℂ s.val // ψ.IsPrimitive},
      ∑ χ : {χ : DirichletCharacter ℂ r.val // χ.IsPrimitive},
        ∑ k ∈ activeComplementCarrier s,
          ∑ l ∈ (activeComplementCarrier r).filter
              (fun l => r.val * l.val = s.val * k.val),
            (levelTotientRatio r.val * levelTotientRatio l.val *
              levelTotientRatio s.val * levelTotientRatio k.val) ^ 2 *
              V ^ 4 *
              ‖primitiveBaseSlotSource Q B N H ⟨r, χ⟩‖ ^ 2 *
              ‖primitiveBaseSlotSource Q B N H ⟨s, ψ⟩‖ ^ 2

/-- Global input-norm control converts the fully factored collision energy to
the totient-ratio envelope without changing any carrier. -/
theorem collisionLiteralFactoredEnvelopeEnergy_le_totientRatioEnvelope
    (Q B : ℕ) (H V : ℝ) (w : ℕ → ℂ)
    (r s : PositiveLevel Q)
    (hw : ∀ n, ‖w n‖ ≤ V) :
    collisionLiteralFactoredEnvelopeEnergy Q B H w r s ≤
      collisionLiteralTotientRatioEnvelopeEnergy Q B H V r s := by
  unfold collisionLiteralFactoredEnvelopeEnergy
    collisionLiteralTotientRatioEnvelopeEnergy
  apply Finset.sum_le_sum
  intro N _hN
  apply Finset.sum_le_sum
  intro ψ _hψ
  apply Finset.sum_le_sum
  intro χ _hχ
  apply Finset.sum_le_sum
  intro k hk
  have hkactive := (Finset.mem_filter.mp hk).2
  apply Finset.sum_le_sum
  intro l hl
  have hlactive := (Finset.mem_filter.mp (Finset.mem_filter.mp hl).1).2
  have hlbound :=
    complement_sq_mul_literalCollisionSideWeight_norm_sq_le
      B N H w r l χ V hlactive (hw _)
  have hkbound :=
    complement_sq_mul_literalCollisionSideWeight_norm_sq_le
      B N H w s k ψ V hkactive (hw _)
  have hleft :
      ((l.val : ℝ) * (k.val : ℝ)) ^ 2 *
          ‖literalCollisionSideWeight B N H w r l χ‖ ^ 2 *
          ‖literalCollisionSideWeight B N H w s k ψ‖ ^ 2 =
        ((l.val : ℝ) ^ 2 *
          ‖literalCollisionSideWeight B N H w r l χ‖ ^ 2) *
        ((k.val : ℝ) ^ 2 *
          ‖literalCollisionSideWeight B N H w s k ψ‖ ^ 2) := by ring
  rw [hleft]
  calc
    _ ≤ ((levelTotientRatio r.val * levelTotientRatio l.val) ^ 2 * V ^ 2 *
          ‖primitiveBaseSlotSource Q B N H ⟨r, χ⟩‖ ^ 2) *
        ((levelTotientRatio s.val * levelTotientRatio k.val) ^ 2 * V ^ 2 *
          ‖primitiveBaseSlotSource Q B N H ⟨s, ψ⟩‖ ^ 2) := by
      exact mul_le_mul hlbound hkbound (by positivity) (by positivity)
    _ = (levelTotientRatio r.val * levelTotientRatio l.val *
          levelTotientRatio s.val * levelTotientRatio k.val) ^ 2 *
        V ^ 4 *
        ‖primitiveBaseSlotSource Q B N H ⟨r, χ⟩‖ ^ 2 *
        ‖primitiveBaseSlotSource Q B N H ⟨s, ψ⟩‖ ^ 2 := by ring

end GoldbachCircleMethodCollisionTotientRatioEnvelopeV18556
