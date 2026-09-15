import GoldbachCircleMethodWeightedCrossDenominatorFluctuationEnergyV18544
import GoldbachCircleMethodCrossConductorBlockPairReindexV18541
import GoldbachCircleMethodLiteralExpansionWithoutCommonPeriodV18321

/-!
# Goldbach V1.8.545: literal cross atom/weight factorization

One literal cross-conductor summand is split exactly into its periodic
twisted-Ramanujan atom and its target-dependent scalar weight.  The latter
contains both primitive base-slot sources and therefore carries the entire
fluctuation obligation exposed by V1.8.544.  This is an identity, not an
estimate.
-/

set_option autoImplicit false

open scoped BigOperators Classical ComplexConjugate

namespace GoldbachCircleMethodLiteralCrossWeightFactorizationV18545

open GoldbachCircleMethodActualCompanionCompleteDiagonalV18204
open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodLiteralExpansionWithoutCommonPeriodV18321
open GoldbachCircleMethodPrincipalActivePairwisePeriodV18316
open GoldbachCircleMethodPrimitiveBaseSlotEnergyV18474
open GoldbachCircleMethodPrimitiveRamanujanProjectionV18103
open GoldbachCircleMethodPrimitiveTwistedRamanujanSupportV18208

/-- The periodic part of one ordered cross-conductor literal pair. -/
noncomputable def literalCrossAtom
    {Q : ℕ} (r s l k : PositiveLevel Q)
    (χ : {χ : DirichletCharacter ℂ r.val // χ.IsPrimitive})
    (ψ : {ψ : DirichletCharacter ℂ s.val // ψ.IsPrimitive})
    (N : ℕ) : ℂ :=
  star (twistedRamanujan r.val l.val χ.val
    (N : ZMod (r.val * l.val))) *
  twistedRamanujan s.val k.val ψ.val
    (N : ZMod (s.val * k.val))

/-- The exact target-dependent scalar multiplying `literalCrossAtom`.  Both
primitive window sources remain visible and no regularity is assumed. -/
noncomputable def literalCrossWeight
    {Q : ℕ} (B N : ℕ) (H : ℝ) (w : ℕ → ℂ)
    (r s l k : PositiveLevel Q)
    (χ : {χ : DirichletCharacter ℂ r.val // χ.IsPrimitive})
    (ψ : {ψ : DirichletCharacter ℂ s.val // ψ.IsPrimitive}) : ℂ :=
  star ((((r.val : ℂ) / (r.val.totient : ℂ)) *
      literalCoefficient r l w) *
    primitiveBaseSlotSource Q B N H ⟨r, χ⟩) *
  ((((s.val : ℂ) / (s.val.totient : ℂ)) *
      literalCoefficient s k w) *
    primitiveBaseSlotSource Q B N H ⟨s, ψ⟩)

/-- Exact factorization of the genuine active-literal/source cross term.
The identity makes explicit why bare atom orthogonality alone cannot bound
the actual block residual. -/
theorem active_literal_source_cross_eq_atom_mul_weight
    {Q : ℕ} (B N : ℕ) (H : ℝ) (w : ℕ → ℂ)
    (r s l k : PositiveLevel Q)
    (χ : {χ : DirichletCharacter ℂ r.val // χ.IsPrimitive})
    (ψ : {ψ : DirichletCharacter ℂ s.val // ψ.IsPrimitive}) :
    star (activeTwistedLiteralTerm r l χ w
        (N : ZMod (r.val * l.val)) *
      primitiveBaseSlotSource Q B N H ⟨r, χ⟩) *
      (activeTwistedLiteralTerm s k ψ w
        (N : ZMod (s.val * k.val)) *
      primitiveBaseSlotSource Q B N H ⟨s, ψ⟩) =
    literalCrossAtom r s l k χ ψ N *
      literalCrossWeight B N H w r s l k χ ψ := by
  unfold activeTwistedLiteralTerm literalCrossAtom literalCrossWeight
  simp only [star_mul]
  ring

end GoldbachCircleMethodLiteralCrossWeightFactorizationV18545
