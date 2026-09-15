import GoldbachCircleMethodCollisionFiberSparsityV18548
import GoldbachCircleMethodCanonicalCoupledFirstMarginalAggregationV18378

/-!
# Goldbach V1.8.549: aggregate collision-pair count

The subsingleton fibers from V1.8.548 are summed over the genuine admitted
complement carrier.  Consequently the number of product-denominator
collisions is at most one full complement-carrier cardinality, hence at most
`Q`.  This counts indices only; it does not bound the character or source
weights attached to those indices.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodCollisionPairCountV18549

open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodPairwiseActiveCostAggregationV18318
open GoldbachCircleMethodCollisionFiberSparsityV18548
open GoldbachCircleMethodCanonicalCoupledFirstMarginalAggregationV18378

/-- Collision multiplicity in the exact loop order used by V1.8.547. -/
def collisionComplementPairCount {Q : ℕ}
    (r s : PositiveLevel Q) : ℕ :=
  ∑ k ∈ activeComplementCarrier s,
    ((activeComplementCarrier r).filter
      (fun l => r.val * l.val = s.val * k.val)).card

/-- Summing subsingleton collision fibers loses only one admitted carrier. -/
theorem collisionComplementPairCount_le_carrier_card
    {Q : ℕ} (r s : PositiveLevel Q) :
    collisionComplementPairCount r s ≤ (activeComplementCarrier s).card := by
  unfold collisionComplementPairCount
  calc
    _ ≤ ∑ k ∈ activeComplementCarrier s, 1 :=
      Finset.sum_le_sum (fun k _hk => collisionComplementFiber_card_le_one r s k)
    _ = (activeComplementCarrier s).card := by simp

/-- The admitted product-denominator collision count is bounded by the global
cutoff.  No analytic size estimate for the corresponding summands is used. -/
theorem collisionComplementPairCount_le_cutoff
    {Q : ℕ} (r s : PositiveLevel Q) :
    collisionComplementPairCount r s ≤ Q :=
  (collisionComplementPairCount_le_carrier_card r s).trans
    (activeComplementCarrier_card_le_cutoff s)

end GoldbachCircleMethodCollisionPairCountV18549
