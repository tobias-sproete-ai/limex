import GoldbachCircleMethodActivePrincipalPairwisePeriodV18320

/-!
# Goldbach V1.8.321: literal expansion without a common period

The natural-input principal companion and active window coefficient are
expanded into their literal denominator terms before any completion.  These
are definitional finite identities and therefore require no global LCM.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodLiteralExpansionWithoutCommonPeriodV18321

open GoldbachCircleMethodActualCompanionCompleteDiagonalV18204
open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodFiniteCompanionBindingV18118
open GoldbachCircleMethodFiniteResiduePrefixV1866
open GoldbachCircleMethodPairwiseActiveCostAggregationV18318
open GoldbachCircleMethodPrincipalActivePairwisePeriodV18316
open GoldbachCircleMethodPrincipalWindowBoundaryV18121
open GoldbachCircleMethodPrimitiveTwistedRamanujanSupportV18208

/-- Literal natural-input expansion of the actual finite companion. -/
theorem finiteCompanion_eq_literalSum {Q : ℕ}
    (r : PositiveLevel Q) (n : ℕ) (w : ℕ → ℂ) :
    finiteCompanion r n w =
      ∑ l : PositiveLevel Q, literalCoefficient r l w *
        unitCharacterSum l.val (n : ZMod l.val) := by
  unfold finiteCompanion literalCoefficient
  apply Finset.sum_congr rfl
  intro l _hl
  split_ifs <;> ring

/-- The active window coefficient is exactly the sum of its admitted literal
twisted terms.  Terms outside the coupled/coprime carrier vanish by
definition; no period completion is used. -/
theorem windowCoefficient_eq_activeLiteralSum {Q : ℕ}
    (r : PositiveLevel Q)
    (chi : {χ : DirichletCharacter ℂ r.val // χ.IsPrimitive})
    (n : ℕ) (w : ℕ → ℂ) :
    windowCoefficient r n w chi =
      ∑ l ∈ activeComplementCarrier r,
        activeTwistedLiteralTerm r l chi w
          (n : ZMod (r.val * l.val)) := by
  unfold windowCoefficient finiteCompanion activeTwistedLiteralTerm
    twistedRamanujan literalCoefficient activeComplementCarrier
  rw [Finset.mul_sum]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro l _hl
  by_cases hsupp : r.val * l.val ≤ Q ∧ Nat.Coprime r.val l.val
  · simp only [map_natCast]
    rw [if_pos ⟨hsupp.1, hsupp.2⟩,
      if_pos ⟨hsupp.1, hsupp.2⟩,
      if_pos ⟨hsupp.1, hsupp.2⟩]
    ring
  · simp only [hsupp, if_false, mul_zero]

end GoldbachCircleMethodLiteralExpansionWithoutCommonPeriodV18321
