import GoldbachCircleMethodCollisionCommonDenominatorTransferV18558

/-!
# Goldbach V1.8.559: one-dimensional collision-denominator energy

Every fixed outer complement `k` has at most one compatible `l`.  After the
common-denominator collapse of V1.8.557, the remaining inner `l`-sum can
therefore be removed without introducing any multiplicity.  The collision
energy is reduced to one genuine admitted complement carrier.
-/

set_option autoImplicit false

open scoped BigOperators Classical ComplexConjugate

namespace GoldbachCircleMethodCollisionOneDimensionalDenominatorEnergyV18559

open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodCollisionCommonDenominatorTotientRatioV18557
open GoldbachCircleMethodCollisionFiberSparsityV18548
open GoldbachCircleMethodCollisionTotientRatioEnvelopeV18556
open GoldbachCircleMethodLogCutoffPresieveBindingV18120
open GoldbachCircleMethodPairwiseActiveCostAggregationV18318
open GoldbachCircleMethodPrimitiveBaseSlotEnergyV18474

/-- One-dimensional envelope after eliminating the subsingleton collision
fiber.  The remaining arithmetic weight is evaluated on `s*k`. -/
noncomputable def collisionOneDimensionalDenominatorRatioEnvelopeEnergy
    (Q B : ℕ) (H V : ℝ) (r s : PositiveLevel Q) : ℝ :=
  ∑ N ∈ blockCarrier B,
    ∑ ψ : {ψ : DirichletCharacter ℂ s.val // ψ.IsPrimitive},
      ∑ χ : {χ : DirichletCharacter ℂ r.val // χ.IsPrimitive},
        ∑ k ∈ activeComplementCarrier s,
          levelTotientRatio (s.val * k.val) ^ 4 * V ^ 4 *
            ‖primitiveBaseSlotSource Q B N H ⟨r, χ⟩‖ ^ 2 *
            ‖primitiveBaseSlotSource Q B N H ⟨s, ψ⟩‖ ^ 2

/-- A common-denominator fiber contributes at most its single outer `k`
weight; no extra carrier cardinality is paid. -/
theorem collision_common_denominator_fiber_le_single_outer_weight
    {Q : ℕ} (B N : ℕ) (H V : ℝ)
    (r s k : PositiveLevel Q)
    (χ : {χ : DirichletCharacter ℂ r.val // χ.IsPrimitive})
    (ψ : {ψ : DirichletCharacter ℂ s.val // ψ.IsPrimitive}) :
    (∑ l ∈ (activeComplementCarrier r).filter
        (fun l => r.val * l.val = s.val * k.val),
      levelTotientRatio (r.val * l.val) ^ 4 * V ^ 4 *
        ‖primitiveBaseSlotSource Q B N H ⟨r, χ⟩‖ ^ 2 *
        ‖primitiveBaseSlotSource Q B N H ⟨s, ψ⟩‖ ^ 2) ≤
      levelTotientRatio (s.val * k.val) ^ 4 * V ^ 4 *
        ‖primitiveBaseSlotSource Q B N H ⟨r, χ⟩‖ ^ 2 *
        ‖primitiveBaseSlotSource Q B N H ⟨s, ψ⟩‖ ^ 2 := by
  let F := (activeComplementCarrier r).filter
    (fun l => r.val * l.val = s.val * k.val)
  let A := levelTotientRatio (s.val * k.val) ^ 4 * V ^ 4 *
    ‖primitiveBaseSlotSource Q B N H ⟨r, χ⟩‖ ^ 2 *
    ‖primitiveBaseSlotSource Q B N H ⟨s, ψ⟩‖ ^ 2
  have hrewrite :
      (∑ l ∈ F,
        levelTotientRatio (r.val * l.val) ^ 4 * V ^ 4 *
          ‖primitiveBaseSlotSource Q B N H ⟨r, χ⟩‖ ^ 2 *
          ‖primitiveBaseSlotSource Q B N H ⟨s, ψ⟩‖ ^ 2) =
        ∑ _l ∈ F, A := by
    apply Finset.sum_congr rfl
    intro l hl
    have hcollision := (Finset.mem_filter.mp hl).2
    dsimp only [A]
    rw [hcollision]
  have hcard : ((F.card : ℕ) : ℝ) ≤ 1 := by
    exact_mod_cast collisionComplementFiber_card_le_one r s k
  have hA : 0 ≤ A := by
    dsimp only [A]
    positivity
  change (∑ l ∈ F,
      levelTotientRatio (r.val * l.val) ^ 4 * V ^ 4 *
        ‖primitiveBaseSlotSource Q B N H ⟨r, χ⟩‖ ^ 2 *
        ‖primitiveBaseSlotSource Q B N H ⟨s, ψ⟩‖ ^ 2) ≤ A
  rw [hrewrite]
  calc
    (∑ _l ∈ F, A) = (F.card : ℝ) * A := by simp
    _ ≤ 1 * A := mul_le_mul_of_nonneg_right hcard hA
    _ = A := one_mul A

/-- The full common-denominator collision envelope loses no more than the
one-dimensional admitted `k` carrier. -/
theorem collisionCommonDenominatorRatioEnvelopeEnergy_le_oneDimensional
    (Q B : ℕ) (H V : ℝ) (r s : PositiveLevel Q) :
    collisionCommonDenominatorRatioEnvelopeEnergy Q B H V r s ≤
      collisionOneDimensionalDenominatorRatioEnvelopeEnergy Q B H V r s := by
  unfold collisionCommonDenominatorRatioEnvelopeEnergy
    collisionOneDimensionalDenominatorRatioEnvelopeEnergy
  apply Finset.sum_le_sum
  intro N _hN
  apply Finset.sum_le_sum
  intro ψ _hψ
  apply Finset.sum_le_sum
  intro χ _hχ
  apply Finset.sum_le_sum
  intro k _hk
  exact collision_common_denominator_fiber_le_single_outer_weight
    B N H V r s k χ ψ

end GoldbachCircleMethodCollisionOneDimensionalDenominatorEnergyV18559
