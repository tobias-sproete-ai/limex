import GoldbachCircleMethodActualCrossLiteralBlockExpansionV18546

/-!
# Goldbach V1.8.547: cross-denominator collision partition

The exact literal block expansion is split into the product-denominator
collision family `r*l = s*k` and its complement.  Only the complementary
family is eligible for V1.8.542--544 orthogonality.  The collision family is
retained literally and no estimate for either branch is asserted.
-/

set_option autoImplicit false

open scoped BigOperators Classical ComplexConjugate

namespace GoldbachCircleMethodCrossDenominatorCollisionPartitionV18547

open GoldbachCircleMethodActualCrossLiteralBlockExpansionV18546
open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodLiteralCrossWeightFactorizationV18545
open GoldbachCircleMethodLogCutoffPresieveBindingV18120
open GoldbachCircleMethodPairwiseActiveCostAggregationV18318

/-- Literal collision branch where the two ambient atom denominators agree. -/
noncomputable def collisionLiteralCrossBlockCorrelation
    (Q B : ℕ) (H : ℝ) (w : ℕ → ℂ)
    (r s : PositiveLevel Q) : ℝ :=
  ∑ N ∈ blockCarrier B,
    ∑ ψ : {ψ : DirichletCharacter ℂ s.val // ψ.IsPrimitive},
      ∑ k ∈ activeComplementCarrier s,
        ∑ χ : {χ : DirichletCharacter ℂ r.val // χ.IsPrimitive},
          ∑ l ∈ (activeComplementCarrier r).filter
              (fun l => r.val * l.val = s.val * k.val),
            (literalCrossAtom r s l k χ ψ N *
              literalCrossWeight B N H w r s l k χ ψ).re

/-- Literal noncollision branch where complete-period atom orthogonality is
available before the target-dependent weight is inserted. -/
noncomputable def separatedLiteralCrossBlockCorrelation
    (Q B : ℕ) (H : ℝ) (w : ℕ → ℂ)
    (r s : PositiveLevel Q) : ℝ :=
  ∑ N ∈ blockCarrier B,
    ∑ ψ : {ψ : DirichletCharacter ℂ s.val // ψ.IsPrimitive},
      ∑ k ∈ activeComplementCarrier s,
        ∑ χ : {χ : DirichletCharacter ℂ r.val // χ.IsPrimitive},
          ∑ l ∈ (activeComplementCarrier r).filter
              (fun l => r.val * l.val ≠ s.val * k.val),
            (literalCrossAtom r s l k χ ψ N *
              literalCrossWeight B N H w r s l k χ ψ).re

/-- Exact, exhaustive, disjoint split of the actual literal cross block into
collision and noncollision product denominators. -/
theorem literalCrossBlockCorrelation_eq_collision_add_separated
    (Q B : ℕ) (H : ℝ) (w : ℕ → ℂ)
    (r s : PositiveLevel Q) :
    literalCrossBlockCorrelation Q B H w r s =
      collisionLiteralCrossBlockCorrelation Q B H w r s +
        separatedLiteralCrossBlockCorrelation Q B H w r s := by
  unfold literalCrossBlockCorrelation collisionLiteralCrossBlockCorrelation
    separatedLiteralCrossBlockCorrelation
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro N _hN
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro ψ _hψ
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _hk
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro χ _hχ
  exact (Finset.sum_filter_add_sum_filter_not
    (activeComplementCarrier r)
    (fun l => r.val * l.val = s.val * k.val)
    (fun l => (literalCrossAtom r s l k χ ψ N *
      literalCrossWeight B N H w r s l k χ ψ).re)).symm

end GoldbachCircleMethodCrossDenominatorCollisionPartitionV18547
