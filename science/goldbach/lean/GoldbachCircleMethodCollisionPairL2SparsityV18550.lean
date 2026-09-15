import GoldbachCircleMethodCollisionPairCountV18549

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodCollisionPairL2SparsityV18550

open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodPairwiseActiveCostAggregationV18318
open GoldbachCircleMethodCollisionFiberSparsityV18548
open GoldbachCircleMethodCollisionPairCountV18549
open GoldbachCircleMethodCanonicalCoupledFirstMarginalAggregationV18378

/-- Exact squared energy of coefficients on the product-denominator collision
carrier. -/
noncomputable def collisionPairEnergy {Q : ℕ}
    (r s : PositiveLevel Q)
    (a : PositiveLevel Q → PositiveLevel Q → ℝ) : ℝ :=
  ∑ k ∈ activeComplementCarrier s,
    ∑ l ∈ (activeComplementCarrier r).filter
        (fun l => r.val * l.val = s.val * k.val),
      (a k l) ^ 2

/-- Exact aggregate of coefficients on the same collision carrier. -/
noncomputable def collisionPairAggregate {Q : ℕ}
    (r s : PositiveLevel Q)
    (a : PositiveLevel Q → PositiveLevel Q → ℝ) : ℝ :=
  ∑ k ∈ activeComplementCarrier s,
    ∑ l ∈ (activeComplementCarrier r).filter
        (fun l => r.val * l.val = s.val * k.val),
      a k l

/-- A subsingleton collision fiber costs no multiplicity in squared energy. -/
theorem collisionFiberAggregate_sq_le_energy {Q : ℕ}
    (r s k : PositiveLevel Q)
    (a : PositiveLevel Q → PositiveLevel Q → ℝ) :
    (∑ l ∈ (activeComplementCarrier r).filter
        (fun l => r.val * l.val = s.val * k.val), a k l) ^ 2 ≤
      ∑ l ∈ (activeComplementCarrier r).filter
        (fun l => r.val * l.val = s.val * k.val), (a k l) ^ 2 := by
  let F := (activeComplementCarrier r).filter
    (fun l => r.val * l.val = s.val * k.val)
  have hcs := sq_sum_le_card_mul_sum_sq
    (s := F) (f := fun l => a k l)
  have hcard : (F.card : ℝ) ≤ 1 := by
    exact_mod_cast collisionComplementFiber_card_le_one r s k
  have henergy : 0 ≤ ∑ l ∈ F, (a k l) ^ 2 := by positivity
  calc
    (∑ l ∈ F, a k l) ^ 2 ≤ (F.card : ℝ) * ∑ l ∈ F, (a k l) ^ 2 := hcs
    _ ≤ 1 * ∑ l ∈ F, (a k l) ^ 2 :=
      mul_le_mul_of_nonneg_right hcard henergy
    _ = ∑ l ∈ F, (a k l) ^ 2 := one_mul _

/-- Product-denominator sparsity improves the naive `Q^2` pair loss to one
factor `Q`.  This is a finite L2 reduction only; it supplies no decay for the
weighted literal atoms. -/
theorem collisionPairAggregate_sq_le_cutoff_mul_energy {Q : ℕ}
    (r s : PositiveLevel Q)
    (a : PositiveLevel Q → PositiveLevel Q → ℝ) :
    (collisionPairAggregate r s a) ^ 2 ≤
      (Q : ℝ) * collisionPairEnergy r s a := by
  unfold collisionPairAggregate collisionPairEnergy
  let S := activeComplementCarrier s
  let g : PositiveLevel Q → ℝ := fun k =>
    ∑ l ∈ (activeComplementCarrier r).filter
        (fun l => r.val * l.val = s.val * k.val), a k l
  have houter := sq_sum_le_card_mul_sum_sq (s := S) (f := g)
  have hinner : ∑ k ∈ S, (g k) ^ 2 ≤
      ∑ k ∈ S, ∑ l ∈ (activeComplementCarrier r).filter
        (fun l => r.val * l.val = s.val * k.val), (a k l) ^ 2 := by
    apply Finset.sum_le_sum
    intro k hk
    exact collisionFiberAggregate_sq_le_energy r s k a
  have hcard : (S.card : ℝ) ≤ (Q : ℝ) := by
    exact_mod_cast activeComplementCarrier_card_le_cutoff s
  have hsum_nonneg : 0 ≤ ∑ k ∈ S, (g k) ^ 2 := by positivity
  have henergy_nonneg : 0 ≤
      ∑ k ∈ S, ∑ l ∈ (activeComplementCarrier r).filter
        (fun l => r.val * l.val = s.val * k.val), (a k l) ^ 2 := by positivity
  calc
    (∑ k ∈ S, g k) ^ 2 ≤ (S.card : ℝ) * ∑ k ∈ S, (g k) ^ 2 := houter
    _ ≤ (S.card : ℝ) *
        (∑ k ∈ S, ∑ l ∈ (activeComplementCarrier r).filter
          (fun l => r.val * l.val = s.val * k.val), (a k l) ^ 2) :=
      mul_le_mul_of_nonneg_left hinner (by positivity)
    _ ≤ (Q : ℝ) *
        (∑ k ∈ S, ∑ l ∈ (activeComplementCarrier r).filter
          (fun l => r.val * l.val = s.val * k.val), (a k l) ^ 2) :=
      mul_le_mul_of_nonneg_right hcard henergy_nonneg

end GoldbachCircleMethodCollisionPairL2SparsityV18550
