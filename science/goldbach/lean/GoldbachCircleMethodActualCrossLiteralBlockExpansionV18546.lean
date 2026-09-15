import GoldbachCircleMethodLiteralCrossWeightFactorizationV18545

/-!
# Goldbach V1.8.546: actual cross-conductor literal block expansion

The genuine V1.8.541 conductor-pair block correlation is expanded into every
primitive-character and admitted complementary-denominator pair.  Each term
is then written using the exact atom/weight split of V1.8.545.  Conductors of
level one are excluded explicitly because the nonprincipal channel is zero
there.  No cancellation or estimate is asserted.
-/

set_option autoImplicit false

open scoped BigOperators Classical ComplexConjugate

namespace GoldbachCircleMethodActualCrossLiteralBlockExpansionV18546

open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodCrossConductorBlockPairReindexV18541
open GoldbachCircleMethodLiteralCrossWeightFactorizationV18545
open GoldbachCircleMethodLiteralExpansionWithoutCommonPeriodV18321
open GoldbachCircleMethodLogCutoffPresieveBindingV18120
open GoldbachCircleMethodNonprincipalConductorAlignedCorrelationV18527
open GoldbachCircleMethodPairwiseActiveCostAggregationV18318
open GoldbachCircleMethodPrimitiveBaseSlotEnergyV18474

/-- Literal target-first expansion for one distinct nonprincipal conductor
pair over the unchanged dyadic block. -/
noncomputable def literalCrossBlockCorrelation
    (Q B : ℕ) (H : ℝ) (w : ℕ → ℂ)
    (r s : PositiveLevel Q) : ℝ :=
  ∑ N ∈ blockCarrier B,
    ∑ ψ : {ψ : DirichletCharacter ℂ s.val // ψ.IsPrimitive},
      ∑ k ∈ activeComplementCarrier s,
        ∑ χ : {χ : DirichletCharacter ℂ r.val // χ.IsPrimitive},
          ∑ l ∈ activeComplementCarrier r,
            (literalCrossAtom r s l k χ ψ N *
              literalCrossWeight B N H w r s l k χ ψ).re

/-- Complex expansion at one target before taking real parts. -/
theorem nonprincipal_conductor_pair_target_eq_literal_sum
    (Q B N : ℕ) (H : ℝ) (w : ℕ → ℂ)
    (r s : PositiveLevel Q)
    (hr : r.val ≠ 1) (hs : s.val ≠ 1) :
    star (nonprincipalConductorCorrelation Q B N H w r) *
        nonprincipalConductorCorrelation Q B N H w s =
      ∑ ψ : {ψ : DirichletCharacter ℂ s.val // ψ.IsPrimitive},
        ∑ k ∈ activeComplementCarrier s,
          ∑ χ : {χ : DirichletCharacter ℂ r.val // χ.IsPrimitive},
            ∑ l ∈ activeComplementCarrier r,
              literalCrossAtom r s l k χ ψ N *
                literalCrossWeight B N H w r s l k χ ψ := by
  rw [nonprincipalConductorCorrelation, if_neg hr,
    nonprincipalConductorCorrelation, if_neg hs]
  simp_rw [windowCoefficient_eq_activeLiteralSum]
  simp only [star_sum, star_mul, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ψ _hψ
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro χ _hχ
  apply Finset.sum_congr rfl
  intro l hl
  simpa only [star_mul] using
    (active_literal_source_cross_eq_atom_mul_weight B N H w r s l k χ ψ)

/-- The actual block correlation equals its literal atom/weight expansion.
This closes the binding edge from V1.8.541 to the fluctuation interface but
does not bound the exposed weights. -/
theorem conductorPairBlockCorrelation_eq_literalCrossBlockCorrelation
    (Q B : ℕ) (H : ℝ) (w : ℕ → ℂ)
    (r s : PositiveLevel Q)
    (hr : r.val ≠ 1) (hs : s.val ≠ 1) :
    conductorPairBlockCorrelation Q B H w r s =
      literalCrossBlockCorrelation Q B H w r s := by
  unfold conductorPairBlockCorrelation literalCrossBlockCorrelation
  apply Finset.sum_congr rfl
  intro N _hN
  have h := congrArg Complex.re
    (nonprincipal_conductor_pair_target_eq_literal_sum
      Q B N H w r s hr hs)
  simpa only [GoldbachCircleMethodCrossConductorPairExpansionV18540.re_fintype_sum,
    GoldbachCircleMethodCrossConductorBlockPairReindexV18541.re_finset_sum] using h

end GoldbachCircleMethodActualCrossLiteralBlockExpansionV18546
