import GoldbachCircleMethodCollisionLiteralAtomEnvelopeV18554

/-!
# Goldbach V1.8.555: collision literal-weight factorization

The target-dependent cross weight is split into its two genuine conductor
sides.  Its squared norm therefore factorizes exactly into a product of two
one-sided squared norms.  This exposes the next analytic interface without
replacing either the literal coefficient or the primitive base-slot source.
-/

set_option autoImplicit false

open scoped BigOperators Classical ComplexConjugate

namespace GoldbachCircleMethodCollisionLiteralWeightFactorizationV18555

open GoldbachCircleMethodActualCompanionCompleteDiagonalV18204
open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodCanonicalCoupledFirstMarginalAggregationV18378
open GoldbachCircleMethodCollisionLiteralAtomEnvelopeV18554
open GoldbachCircleMethodLiteralCrossWeightFactorizationV18545
open GoldbachCircleMethodLiteralExpansionWithoutCommonPeriodV18321
open GoldbachCircleMethodPairwiseActiveCostAggregationV18318
open GoldbachCircleMethodPrimitiveBaseSlotEnergyV18474

/-- One genuine conductor-side factor of the literal collision weight. -/
noncomputable def literalCollisionSideWeight
    {Q : ℕ} (B N : ℕ) (H : ℝ) (w : ℕ → ℂ)
    (r l : PositiveLevel Q)
    (χ : {χ : DirichletCharacter ℂ r.val // χ.IsPrimitive}) : ℂ :=
  (((r.val : ℂ) / (r.val.totient : ℂ)) * literalCoefficient r l w) *
    primitiveBaseSlotSource Q B N H ⟨r, χ⟩

/-- The two-sided target weight is definitionally the conjugated left side
times the right side. -/
theorem literalCrossWeight_eq_star_side_mul_side
    {Q : ℕ} (B N : ℕ) (H : ℝ) (w : ℕ → ℂ)
    (r s l k : PositiveLevel Q)
    (χ : {χ : DirichletCharacter ℂ r.val // χ.IsPrimitive})
    (ψ : {ψ : DirichletCharacter ℂ s.val // ψ.IsPrimitive}) :
    literalCrossWeight B N H w r s l k χ ψ =
      star (literalCollisionSideWeight B N H w r l χ) *
        literalCollisionSideWeight B N H w s k ψ := by
  unfold literalCrossWeight literalCollisionSideWeight
  simp only [star_mul]

/-- Exact squared-norm product law for the genuine literal cross weight. -/
theorem literalCrossWeight_norm_sq_eq_side_product
    {Q : ℕ} (B N : ℕ) (H : ℝ) (w : ℕ → ℂ)
    (r s l k : PositiveLevel Q)
    (χ : {χ : DirichletCharacter ℂ r.val // χ.IsPrimitive})
    (ψ : {ψ : DirichletCharacter ℂ s.val // ψ.IsPrimitive}) :
    ‖literalCrossWeight B N H w r s l k χ ψ‖ ^ 2 =
      ‖literalCollisionSideWeight B N H w r l χ‖ ^ 2 *
        ‖literalCollisionSideWeight B N H w s k ψ‖ ^ 2 := by
  rw [literalCrossWeight_eq_star_side_mul_side, norm_mul, norm_star]
  ring

/-- Fully factored atom-envelope energy on the unchanged collision carrier. -/
noncomputable def collisionLiteralFactoredEnvelopeEnergy
    (Q B : ℕ) (H : ℝ) (w : ℕ → ℂ)
    (r s : PositiveLevel Q) : ℝ :=
  ∑ N ∈ GoldbachCircleMethodLogCutoffPresieveBindingV18120.blockCarrier B,
    ∑ ψ : {ψ : DirichletCharacter ℂ s.val // ψ.IsPrimitive},
      ∑ χ : {χ : DirichletCharacter ℂ r.val // χ.IsPrimitive},
        ∑ k ∈ activeComplementCarrier s,
          ∑ l ∈ (activeComplementCarrier r).filter
              (fun l => r.val * l.val = s.val * k.val),
            ((l.val : ℝ) * (k.val : ℝ)) ^ 2 *
              ‖literalCollisionSideWeight B N H w r l χ‖ ^ 2 *
              ‖literalCollisionSideWeight B N H w s k ψ‖ ^ 2

/-- No information is lost when the two-sided weight is replaced by its exact
one-sided factorization. -/
theorem collisionLiteralAtomEnvelopeEnergy_eq_factored
    (Q B : ℕ) (H : ℝ) (w : ℕ → ℂ)
    (r s : PositiveLevel Q) :
    collisionLiteralAtomEnvelopeEnergy Q B H w r s =
      collisionLiteralFactoredEnvelopeEnergy Q B H w r s := by
  unfold collisionLiteralAtomEnvelopeEnergy
    collisionLiteralFactoredEnvelopeEnergy
  apply Finset.sum_congr rfl
  intro N _hN
  apply Finset.sum_congr rfl
  intro ψ _hψ
  apply Finset.sum_congr rfl
  intro χ _hχ
  apply Finset.sum_congr rfl
  intro k _hk
  apply Finset.sum_congr rfl
  intro l _hl
  rw [literalCrossWeight_norm_sq_eq_side_product]
  ring

end GoldbachCircleMethodCollisionLiteralWeightFactorizationV18555
