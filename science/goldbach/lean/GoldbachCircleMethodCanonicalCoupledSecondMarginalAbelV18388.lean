import GoldbachCircleMethodCanonicalQuadraticBranchVariationV18387
import GoldbachCircleMethodCoupledSecondMarginalPairwiseRemainderV18384
import GoldbachCircleMethodCanonicalFirstMarginalAbelBoundV18371

/-!
# Goldbach V1.8.388: canonical Abel bound for the coupled second marginal

The pairwise Ramanujan-prefix bound from V1.8.384 is transported through the
exact source-derived quadratic target weight.  On either parity-compatible
branch, one active/companion level pair costs at most

`(r*l) * phi(r) * phi(l) * B * (3 + 4*b)`.

No common LCM, level aggregation, source normalization, reserve absorption,
or Goldbach conclusion is used.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodCanonicalCoupledSecondMarginalAbelV18388

open GoldbachCircleMethodCanonicalFirstMarginalAbelBoundV18371
open GoldbachCircleMethodCanonicalQuadraticBranchVariationV18387
open GoldbachCircleMethodCanonicalTargetQuadraticWeightBindingV18385
open GoldbachCircleMethodCanonicalTargetWeightPiecewiseGeometryV18368
open GoldbachCircleMethodCoupledSecondMarginalPairwiseRemainderV18384
open GoldbachCircleMethodFiniteResiduePrefixV1866

/-- Canonically weighted coupled second Ramanujan marginal for one coprime
active/companion pair. -/
noncomputable def canonicalCoupledSecondMarginalTargetSum
    (r l : ℕ) [NeZero r] [NeZero l]
    (B A T : ℕ) (b : ℝ) : ℂ :=
  ∑ i ∈ Finset.range T,
    canonicalTargetQuadraticWeight B (A + 2 * i) b •
      (unitCharacterSum r ((A + 2 * i : ℕ) : ZMod r) *
        unitCharacterSum l ((A + 2 * i : ℕ) : ZMod l))

/-- One growing branch: pairwise prefix boundary times the exact terminal
height-plus-variation budget. -/
theorem canonical_coupled_second_marginal_growing_branch_norm_le
    (r l : ℕ) [NeZero r] [NeZero l]
    (hcop : Nat.Coprime r l) (hprod : 2 < r * l)
    (B A T : ℕ) (b : ℝ) (hb : 0 ≤ b)
    (hB : 2 ≤ B) (hBA : B ≤ A)
    (hNonempty : 2 * (B / 2 + 1) ≤ A)
    (hT : 1 ≤ T)
    (hLast : A + 2 * (T - 1) ≤ blockPairTurningTarget B) :
    ‖canonicalCoupledSecondMarginalTargetSum r l B A T b‖ ≤
      (((r * l : ℕ) : ℝ) *
        ((r.totient : ℝ) * (l.totient : ℝ))) *
          ((B : ℝ) * (3 + 4 * b)) := by
  unfold canonicalCoupledSecondMarginalTargetSum
  have hBound := weighted_complex_sum_norm_le_of_prefix_bound_general
    (fun i =>
      unitCharacterSum r ((A + 2 * i : ℕ) : ZMod r) *
        unitCharacterSum l ((A + 2 * i : ℕ) : ZMod l))
    (fun i => canonicalTargetQuadraticWeight B (A + 2 * i) b)
    T
    (((r * l : ℕ) : ℝ) * ((r.totient : ℝ) * (l.totient : ℝ)))
    B ((B : ℝ) * (2 + 4 * b)) (by positivity) hT
    (fun k _hk => coupled_second_marginal_prefix_norm_le
      r l hcop hprod A k)
    (by
      have hmem := canonicalTargetQuadraticWeight_mem_Icc
        B (A + 2 * (T - 1)) b hb
      rw [abs_of_nonneg hmem.1]
      exact hmem.2)
    (canonicalTargetQuadraticWeight_growing_branch_variation_le
      B A T b hB hBA hb hNonempty hLast)
  calc
    _ ≤ (((r * l : ℕ) : ℝ) *
        ((r.totient : ℝ) * (l.totient : ℝ))) *
          ((B : ℝ) + (B : ℝ) * (2 + 4 * b)) := hBound
    _ = (((r * l : ℕ) : ℝ) *
        ((r.totient : ℝ) * (l.totient : ℝ))) *
          ((B : ℝ) * (3 + 4 * b)) := by ring

/-- Matching shrinking-branch estimate. -/
theorem canonical_coupled_second_marginal_shrinking_branch_norm_le
    (r l : ℕ) [NeZero r] [NeZero l]
    (hcop : Nat.Coprime r l) (hprod : 2 < r * l)
    (B A T : ℕ) (b : ℝ) (hb : 0 ≤ b)
    (hB : 2 ≤ B) (hBA : B ≤ A)
    (hTurn : blockPairTurningTarget B ≤ A)
    (hT : 1 ≤ T)
    (hLast : A + 2 * (T - 1) ≤ 2 * B) :
    ‖canonicalCoupledSecondMarginalTargetSum r l B A T b‖ ≤
      (((r * l : ℕ) : ℝ) *
        ((r.totient : ℝ) * (l.totient : ℝ))) *
          ((B : ℝ) * (3 + 4 * b)) := by
  unfold canonicalCoupledSecondMarginalTargetSum
  have hBound := weighted_complex_sum_norm_le_of_prefix_bound_general
    (fun i =>
      unitCharacterSum r ((A + 2 * i : ℕ) : ZMod r) *
        unitCharacterSum l ((A + 2 * i : ℕ) : ZMod l))
    (fun i => canonicalTargetQuadraticWeight B (A + 2 * i) b)
    T
    (((r * l : ℕ) : ℝ) * ((r.totient : ℝ) * (l.totient : ℝ)))
    B ((B : ℝ) * (2 + 4 * b)) (by positivity) hT
    (fun k _hk => coupled_second_marginal_prefix_norm_le
      r l hcop hprod A k)
    (by
      have hmem := canonicalTargetQuadraticWeight_mem_Icc
        B (A + 2 * (T - 1)) b hb
      rw [abs_of_nonneg hmem.1]
      exact hmem.2)
    (canonicalTargetQuadraticWeight_shrinking_branch_variation_le
      B A T b hB hBA hb hTurn hLast)
  calc
    _ ≤ (((r * l : ℕ) : ℝ) *
        ((r.totient : ℝ) * (l.totient : ℝ))) *
          ((B : ℝ) + (B : ℝ) * (2 + 4 * b)) := hBound
    _ = (((r * l : ℕ) : ℝ) *
        ((r.totient : ℝ) * (l.totient : ℝ))) *
          ((B : ℝ) * (3 + 4 * b)) := by ring

end GoldbachCircleMethodCanonicalCoupledSecondMarginalAbelV18388
