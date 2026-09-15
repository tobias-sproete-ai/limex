import GoldbachCircleMethodCoupledFirstMarginalPairwiseRemainderV18375

/-!
# Goldbach V1.8.376: canonical Abel bound for one coupled companion level

The pairwise-period prefix bound of V1.8.375 is transported through the exact
canonical target weight.  On either monotone target branch the boundary cost
for one companion level is at most

`4 * B * (r*l) * phi(l)`.

This theorem remains before the `mu(l)^2 / phi(l)^2` source normalization and
before summation over companion levels.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodCanonicalCoupledFirstMarginalAbelV18376

open GoldbachCircleMethodCanonicalFirstMarginalAbelBoundV18371
open GoldbachCircleMethodCanonicalTargetLinearWeightBindingV18367
open GoldbachCircleMethodCanonicalTargetWeightPiecewiseGeometryV18368
open GoldbachCircleMethodCanonicalTargetWeightBranchVariationV18370
open GoldbachCircleMethodCoupledFirstMarginalPairwiseRemainderV18375
open GoldbachCircleMethodFiniteResiduePrefixV1866

/-- Canonically weighted coupled first marginal for one active/companion pair. -/
noncomputable def canonicalCoupledFirstMarginalTargetSum
    (r l : ℕ) [NeZero r] [NeZero l]
    (chi : DirichletCharacter ℂ r)
    (B A T : ℕ) (b : ℝ) : ℂ :=
  ∑ i ∈ Finset.range T,
    canonicalTargetLinearWeight B (A + 2 * i) b •
      ((((ArithmeticFunction.moebius r : ℤ) : ℂ) *
          chi ((A + 2 * i : ℕ) : ZMod r)) *
        unitCharacterSum l ((A + 2 * i : ℕ) : ZMod l))

/-- One growing target branch costs one pairwise boundary times the exact
canonical height-plus-variation budget `4*B`. -/
theorem canonical_coupled_first_marginal_growing_branch_norm_le
    (r l : ℕ) [NeZero r] [NeZero l]
    (hcop : Nat.Coprime r l)
    (chi : DirichletCharacter ℂ r) (hne : chi ≠ 1)
    (h2 : Nat.Coprime 2 r)
    (B A T : ℕ) (b : ℝ) (hb : 0 ≤ b)
    (hB : 1 ≤ B) (hBA : B ≤ A)
    (hNonempty : 2 * (B / 2 + 1) ≤ A)
    (hT : 1 ≤ T)
    (hLast : A + 2 * (T - 1) ≤ blockPairTurningTarget B) :
    ‖canonicalCoupledFirstMarginalTargetSum r l chi B A T b‖ ≤
      (((r * l : ℕ) : ℝ) * (l.totient : ℝ)) * (4 * B) := by
  unfold canonicalCoupledFirstMarginalTargetSum
  have hBound := weighted_complex_sum_norm_le_of_prefix_bound_general
    (fun i =>
      (((ArithmeticFunction.moebius r : ℤ) : ℂ) *
          chi ((A + 2 * i : ℕ) : ZMod r)) *
        unitCharacterSum l ((A + 2 * i : ℕ) : ZMod l))
    (fun i => canonicalTargetLinearWeight B (A + 2 * i) b)
    T (((r * l : ℕ) : ℝ) * (l.totient : ℝ)) (2 * B) (2 * B)
    (by positivity) hT
    (fun k _hk => coupled_first_marginal_prefix_norm_le
      r l hcop chi hne A k h2)
    (by
      have hmem := canonicalTargetLinearWeight_mem_Icc
        B (A + 2 * (T - 1)) b hb (by omega)
      rw [abs_of_nonneg hmem.1]
      exact hmem.2)
    (canonicalTargetLinearWeight_growing_branch_variation_le
      B A T b hb hB hBA hNonempty hT hLast)
  calc
    _ ≤ (((r * l : ℕ) : ℝ) * (l.totient : ℝ)) *
        ((2 : ℝ) * B + 2 * B) := hBound
    _ = (((r * l : ℕ) : ℝ) * (l.totient : ℝ)) * (4 * B) := by ring

/-- The matching shrinking-branch estimate. -/
theorem canonical_coupled_first_marginal_shrinking_branch_norm_le
    (r l : ℕ) [NeZero r] [NeZero l]
    (hcop : Nat.Coprime r l)
    (chi : DirichletCharacter ℂ r) (hne : chi ≠ 1)
    (h2 : Nat.Coprime 2 r)
    (B A T : ℕ) (b : ℝ) (hb : 0 ≤ b)
    (hB : 1 ≤ B) (hBA : B ≤ A)
    (hTurn : blockPairTurningTarget B ≤ A)
    (hT : 1 ≤ T)
    (hLast : A + 2 * (T - 1) ≤ 2 * B) :
    ‖canonicalCoupledFirstMarginalTargetSum r l chi B A T b‖ ≤
      (((r * l : ℕ) : ℝ) * (l.totient : ℝ)) * (4 * B) := by
  unfold canonicalCoupledFirstMarginalTargetSum
  have hBound := weighted_complex_sum_norm_le_of_prefix_bound_general
    (fun i =>
      (((ArithmeticFunction.moebius r : ℤ) : ℂ) *
          chi ((A + 2 * i : ℕ) : ZMod r)) *
        unitCharacterSum l ((A + 2 * i : ℕ) : ZMod l))
    (fun i => canonicalTargetLinearWeight B (A + 2 * i) b)
    T (((r * l : ℕ) : ℝ) * (l.totient : ℝ)) (2 * B) (2 * B)
    (by positivity) hT
    (fun k _hk => coupled_first_marginal_prefix_norm_le
      r l hcop chi hne A k h2)
    (by
      have hmem := canonicalTargetLinearWeight_mem_Icc
        B (A + 2 * (T - 1)) b hb (by omega)
      rw [abs_of_nonneg hmem.1]
      exact hmem.2)
    (canonicalTargetLinearWeight_shrinking_branch_variation_le
      B A T b hb hB hBA hTurn hT hLast)
  calc
    _ ≤ (((r * l : ℕ) : ℝ) * (l.totient : ℝ)) *
        ((2 : ℝ) * B + 2 * B) := hBound
    _ = (((r * l : ℕ) : ℝ) * (l.totient : ℝ)) * (4 * B) := by ring

end GoldbachCircleMethodCanonicalCoupledFirstMarginalAbelV18376
