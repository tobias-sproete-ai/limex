import GoldbachCircleMethodCrossDenominatorCollisionPartitionV18547

/-!
# Goldbach V1.8.548: collision-fiber sparsity

For fixed outer conductors `r`, `s` and fixed complementary denominator `k`,
the product-denominator collision equation `r*l = s*k` admits at most one
complementary denominator `l`.  This is a finite arithmetic sparsity result;
it does not estimate the remaining collision summand and does not assert a
Goldbach conclusion.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodCollisionFiberSparsityV18548

open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodPairwiseActiveCostAggregationV18318

/-- At fixed `r`, `s`, and `k`, multiplication by the positive conductor `r`
makes the collision fiber in `l` subsingleton. -/
theorem collisionComplementFiber_card_le_one
    {Q : ℕ} (r s k : PositiveLevel Q) :
    ((activeComplementCarrier r).filter
      (fun l => r.val * l.val = s.val * k.val)).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro l hl l' hl'
  have hlprod := (Finset.mem_filter.mp hl).2
  have hl'prod := (Finset.mem_filter.mp hl').2
  apply Subtype.ext
  exact Nat.eq_of_mul_eq_mul_left (NeZero.pos r.val)
    (hlprod.trans hl'prod.symm)

/-- The symmetric fixed-`l` collision fiber in `k` is also subsingleton. -/
theorem collisionComplementFiber_symm_card_le_one
    {Q : ℕ} (r s l : PositiveLevel Q) :
    ((activeComplementCarrier s).filter
      (fun k => r.val * l.val = s.val * k.val)).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro k hk k' hk'
  have hkprod := (Finset.mem_filter.mp hk).2
  have hk'prod := (Finset.mem_filter.mp hk').2
  apply Subtype.ext
  exact Nat.eq_of_mul_eq_mul_left (NeZero.pos s.val)
    (hkprod.symm.trans hk'prod)

end GoldbachCircleMethodCollisionFiberSparsityV18548
