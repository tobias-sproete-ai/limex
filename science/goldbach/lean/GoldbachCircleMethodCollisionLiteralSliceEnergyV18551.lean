import GoldbachCircleMethodCollisionPairL2SparsityV18550
import GoldbachCircleMethodCrossDenominatorCollisionPartitionV18547

/-!
# Goldbach V1.8.551: literal collision-slice energy

The abstract one-carrier collision gain of V1.8.550 is instantiated with the
actual real part of the weighted literal cross atom.  The genuine collision
block is then reindexed as a sum of fixed-character slices.  This is an exact
finite bridge: it introduces no pointwise bound and no analytic decay.
-/

set_option autoImplicit false

open scoped BigOperators Classical ComplexConjugate

namespace GoldbachCircleMethodCollisionLiteralSliceEnergyV18551

open GoldbachCircleMethodActualCrossLiteralBlockExpansionV18546
open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodCanonicalCoupledFirstMarginalAggregationV18378
open GoldbachCircleMethodCollisionPairL2SparsityV18550
open GoldbachCircleMethodCrossDenominatorCollisionPartitionV18547
open GoldbachCircleMethodLiteralCrossWeightFactorizationV18545
open GoldbachCircleMethodLogCutoffPresieveBindingV18120
open GoldbachCircleMethodPairwiseActiveCostAggregationV18318

/-- Actual weighted collision slice at fixed target and primitive-character
pair. -/
noncomputable def collisionLiteralSlice
    {Q : ℕ} (B N : ℕ) (H : ℝ) (w : ℕ → ℂ)
    (r s : PositiveLevel Q)
    (χ : {χ : DirichletCharacter ℂ r.val // χ.IsPrimitive})
    (ψ : {ψ : DirichletCharacter ℂ s.val // ψ.IsPrimitive}) : ℝ :=
  ∑ k ∈ activeComplementCarrier s,
    ∑ l ∈ (activeComplementCarrier r).filter
        (fun l => r.val * l.val = s.val * k.val),
      (literalCrossAtom r s l k χ ψ N *
        literalCrossWeight B N H w r s l k χ ψ).re

/-- Exact squared coefficient energy on the same literal collision slice. -/
noncomputable def collisionLiteralSliceEnergy
    {Q : ℕ} (B N : ℕ) (H : ℝ) (w : ℕ → ℂ)
    (r s : PositiveLevel Q)
    (χ : {χ : DirichletCharacter ℂ r.val // χ.IsPrimitive})
    (ψ : {ψ : DirichletCharacter ℂ s.val // ψ.IsPrimitive}) : ℝ :=
  ∑ k ∈ activeComplementCarrier s,
    ∑ l ∈ (activeComplementCarrier r).filter
        (fun l => r.val * l.val = s.val * k.val),
      ((literalCrossAtom r s l k χ ψ N *
        literalCrossWeight B N H w r s l k χ ψ).re) ^ 2

/-- The actual fixed-character collision slice loses only one factor `Q` in
finite L2. -/
theorem collisionLiteralSlice_sq_le_cutoff_mul_energy
    {Q : ℕ} (B N : ℕ) (H : ℝ) (w : ℕ → ℂ)
    (r s : PositiveLevel Q)
    (χ : {χ : DirichletCharacter ℂ r.val // χ.IsPrimitive})
    (ψ : {ψ : DirichletCharacter ℂ s.val // ψ.IsPrimitive}) :
    (collisionLiteralSlice B N H w r s χ ψ) ^ 2 ≤
      (Q : ℝ) * collisionLiteralSliceEnergy B N H w r s χ ψ := by
  exact collisionPairAggregate_sq_le_cutoff_mul_energy r s
    (fun k l => (literalCrossAtom r s l k χ ψ N *
      literalCrossWeight B N H w r s l k χ ψ).re)

/-- Exact loop interchange: the genuine collision block is the sum of its
fixed primitive-character slices. -/
theorem collisionLiteralCrossBlockCorrelation_eq_sum_slices
    (Q B : ℕ) (H : ℝ) (w : ℕ → ℂ)
    (r s : PositiveLevel Q) :
    collisionLiteralCrossBlockCorrelation Q B H w r s =
      ∑ N ∈ blockCarrier B,
        ∑ ψ : {ψ : DirichletCharacter ℂ s.val // ψ.IsPrimitive},
          ∑ χ : {χ : DirichletCharacter ℂ r.val // χ.IsPrimitive},
            collisionLiteralSlice B N H w r s χ ψ := by
  unfold collisionLiteralCrossBlockCorrelation collisionLiteralSlice
  apply Finset.sum_congr rfl
  intro N _hN
  apply Finset.sum_congr rfl
  intro ψ _hψ
  rw [Finset.sum_comm]

end GoldbachCircleMethodCollisionLiteralSliceEnergyV18551
