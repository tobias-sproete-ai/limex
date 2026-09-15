import GoldbachCircleMethodCollisionTotientRatioEnvelopeV18556

/-!
# Goldbach V1.8.557: common-denominator totient-ratio collapse

On the unchanged collision carrier `r*l = s*k`, the two pairs of local
totient ratios are each exactly the ratio of their common product modulus.
Consequently the four local factors in V1.8.556 collapse to the fourth
power of one common-denominator ratio.  This is an exact finite identity;
it supplies no analytic bound for that remaining ratio.
-/

set_option autoImplicit false

open scoped BigOperators Classical ComplexConjugate

namespace GoldbachCircleMethodCollisionCommonDenominatorTotientRatioV18557

open GoldbachCircleMethodActualCompanionCompleteDiagonalV18204
open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodCanonicalCoupledFirstMarginalAggregationV18378
open GoldbachCircleMethodCollisionLiteralWeightFactorizationV18555
open GoldbachCircleMethodCollisionTotientRatioEnvelopeV18556
open GoldbachCircleMethodLogCutoffPresieveBindingV18120
open GoldbachCircleMethodPairwiseActiveCostAggregationV18318
open GoldbachCircleMethodPrimitiveBaseSlotEnergyV18474

/-- The totient ratio is multiplicative on positive coprime inputs. -/
theorem levelTotientRatio_mul_of_coprime
    (a b : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) (hcop : Nat.Coprime a b) :
    levelTotientRatio a * levelTotientRatio b =
      levelTotientRatio (a * b) := by
  have hphia : (a.totient : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.totient_pos.mpr (Nat.pos_of_ne_zero ha)))
  have hphib : (b.totient : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.totient_pos.mpr (Nat.pos_of_ne_zero hb)))
  unfold levelTotientRatio
  rw [Nat.totient_mul hcop]
  push_cast
  field_simp [hphia, hphib]

/-- On a genuine product-denominator collision, all four local ratios are
one common modulus ratio to the fourth power after squaring. -/
theorem collision_local_totient_product_sq_eq_common_fourth
    {Q : ℕ} (r s k l : PositiveLevel Q)
    (hkactive : s.val * k.val ≤ Q ∧ Nat.Coprime s.val k.val)
    (hlactive : r.val * l.val ≤ Q ∧ Nat.Coprime r.val l.val)
    (hcollision : r.val * l.val = s.val * k.val) :
    (levelTotientRatio r.val * levelTotientRatio l.val *
        levelTotientRatio s.val * levelTotientRatio k.val) ^ 2 =
      levelTotientRatio (r.val * l.val) ^ 4 := by
  have hrl := levelTotientRatio_mul_of_coprime r.val l.val
    (NeZero.ne r.val) (NeZero.ne l.val) hlactive.2
  have hsk := levelTotientRatio_mul_of_coprime s.val k.val
    (NeZero.ne s.val) (NeZero.ne k.val) hkactive.2
  calc
    (levelTotientRatio r.val * levelTotientRatio l.val *
        levelTotientRatio s.val * levelTotientRatio k.val) ^ 2 =
      ((levelTotientRatio r.val * levelTotientRatio l.val) *
        (levelTotientRatio s.val * levelTotientRatio k.val)) ^ 2 := by ring
    _ = (levelTotientRatio (r.val * l.val) *
          levelTotientRatio (s.val * k.val)) ^ 2 := by rw [hrl, hsk]
    _ = (levelTotientRatio (r.val * l.val) *
          levelTotientRatio (r.val * l.val)) ^ 2 := by rw [← hcollision]
    _ = levelTotientRatio (r.val * l.val) ^ 4 := by ring

/-- The V1.8.556 envelope rewritten with one common denominator on every
collision fiber. -/
noncomputable def collisionCommonDenominatorRatioEnvelopeEnergy
    (Q B : ℕ) (H V : ℝ) (r s : PositiveLevel Q) : ℝ :=
  ∑ N ∈ blockCarrier B,
    ∑ ψ : {ψ : DirichletCharacter ℂ s.val // ψ.IsPrimitive},
      ∑ χ : {χ : DirichletCharacter ℂ r.val // χ.IsPrimitive},
        ∑ k ∈ activeComplementCarrier s,
          ∑ l ∈ (activeComplementCarrier r).filter
              (fun l => r.val * l.val = s.val * k.val),
            levelTotientRatio (r.val * l.val) ^ 4 * V ^ 4 *
              ‖primitiveBaseSlotSource Q B N H ⟨r, χ⟩‖ ^ 2 *
              ‖primitiveBaseSlotSource Q B N H ⟨s, ψ⟩‖ ^ 2

/-- Exact carrier-preserving collapse of the local-ratio envelope to the
common-denominator form. -/
theorem collisionLiteralTotientRatioEnvelopeEnergy_eq_commonDenominator
    (Q B : ℕ) (H V : ℝ) (r s : PositiveLevel Q) :
    collisionLiteralTotientRatioEnvelopeEnergy Q B H V r s =
      collisionCommonDenominatorRatioEnvelopeEnergy Q B H V r s := by
  unfold collisionLiteralTotientRatioEnvelopeEnergy
    collisionCommonDenominatorRatioEnvelopeEnergy
  apply Finset.sum_congr rfl
  intro N _hN
  apply Finset.sum_congr rfl
  intro ψ _hψ
  apply Finset.sum_congr rfl
  intro χ _hχ
  apply Finset.sum_congr rfl
  intro k hk
  have hkactive := (Finset.mem_filter.mp hk).2
  apply Finset.sum_congr rfl
  intro l hl
  have hlmem := Finset.mem_filter.mp hl
  have hlactive := (Finset.mem_filter.mp hlmem.1).2
  rw [collision_local_totient_product_sq_eq_common_fourth
    r s k l hkactive hlactive hlmem.2]

end GoldbachCircleMethodCollisionCommonDenominatorTotientRatioV18557
