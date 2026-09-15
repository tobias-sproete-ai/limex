import GoldbachCircleMethodCanonicalCoupledSecondMarginalSourceBindingV18391

/-!
# Goldbach V1.8.392: classification of the uncancelled low product levels

The complement of the off-divisor condition `2 < r*l` inside the genuine
coupled support contains only the three positive ordered pairs

`(1,1)`, `(1,2)`, `(2,1)`.

Consequently the low-frequency coupled diagonal vanishes identically for
every active conductor `r >= 3`.  This is a finite carrier classification;
it does not assign a sign to the three surviving channels.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodCoupledSecondLowFrequencyClassificationV18392

open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodCanonicalCoupledSecondMarginalSourceBindingV18391
open GoldbachCircleMethodPairwiseActiveCostAggregationV18318

/-- Every positive coupled pair with product at most two is one of the three
explicit ordered low-frequency pairs. -/
theorem low_product_pair_classification {Q : ℕ}
    (r l : PositiveLevel Q)
    (hlow : l ∈ (activeComplementCarrier r).filter
      (fun l => ¬ 2 < r.val * l.val)) :
    (r.val = 1 ∧ (l.val = 1 ∨ l.val = 2)) ∨
      (r.val = 2 ∧ l.val = 1) := by
  have hactive := (Finset.mem_filter.mp hlow).1
  have hprod : r.val * l.val ≤ 2 := by
    have hn := (Finset.mem_filter.mp hlow).2
    omega
  have hrpos : 1 ≤ r.val := (Finset.mem_Icc.mp r.property).1
  have hlpos : 1 ≤ l.val := (Finset.mem_Icc.mp l.property).1
  have hrleprod : r.val ≤ r.val * l.val := by
    simpa only [mul_one] using Nat.mul_le_mul_left r.val hlpos
  have hlleprod : l.val ≤ r.val * l.val := by
    simpa only [one_mul] using Nat.mul_le_mul_right l.val hrpos
  have hrle : r.val ≤ 2 := hrleprod.trans hprod
  have hlle : l.val ≤ 2 := hlleprod.trans hprod
  interval_cases hr : r.val <;> interval_cases hlv : l.val <;>
    simp_all [activeComplementCarrier, Nat.Coprime]

/-- For active conductor at least three, the low-frequency diagonal is empty
and hence identically zero. -/
theorem lowFrequencyCoupledDiagonalAtNat_eq_zero_of_three_le {Q : ℕ}
    (r : PositiveLevel Q) (hr : 3 ≤ r.val)
    (v w : ℕ → ℂ) (N : ℕ) :
    lowFrequencyCoupledDiagonalAtNat r v w N = 0 := by
  unfold lowFrequencyCoupledDiagonalAtNat
  apply Finset.sum_eq_zero
  intro l hl
  have hclass := low_product_pair_classification r l hl
  omega

/-- The entire low-frequency target contribution vanishes for every active
conductor at least three. -/
theorem lowFrequencyCoupledSecondMarginalTargetSum_eq_zero_of_three_le
    {Q : ℕ} (r : PositiveLevel Q) (hr : 3 ≤ r.val)
    (v w : ℕ → ℂ) (B A T : ℕ) (b : ℝ) :
    lowFrequencyCoupledSecondMarginalTargetSum r v w B A T b = 0 := by
  unfold lowFrequencyCoupledSecondMarginalTargetSum
  apply Finset.sum_eq_zero
  intro i _hi
  rw [lowFrequencyCoupledDiagonalAtNat_eq_zero_of_three_le r hr,
    mul_zero, smul_zero]

end GoldbachCircleMethodCoupledSecondLowFrequencyClassificationV18392
