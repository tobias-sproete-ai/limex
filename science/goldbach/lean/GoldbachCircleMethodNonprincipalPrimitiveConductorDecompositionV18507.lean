import GoldbachCircleMethodHybridCenteredWitnessTransferV18506

/-!
# Goldbach V1.8.507: nonprincipal primitive conductor decomposition

The remaining hard source channel is reindexed exactly by conductor.  The
conductor-one atom is removed explicitly; no Vaughan, Bombieri--Vinogradov,
or large-sieve estimate is inferred from this algebraic identity.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodNonprincipalPrimitiveConductorDecompositionV18507

open GoldbachCircleMethodActualPrimitiveSourceNormalizationV18470
open GoldbachCircleMethodActualWindowInputEnergyV18469
open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodFiniteWindowConvolutionV18119
open GoldbachCircleMethodHybridCenteredCorrelationEnergyV18501
open GoldbachCircleMethodHybridCenteredSourceSplitV18500
open GoldbachCircleMethodLogCutoffPresieveBindingV18120
open GoldbachCircleMethodPrimitiveBaseSlotEnergyV18474

/-- Exact conductor reindexing of the nonprincipal primitive source energy.
The sole level-one conductor is represented by a literal zero summand. -/
theorem nonprincipalPrimitiveSourceEnergy_eq_sum_raw_except_one
    (Q B N : ℕ) (H : ℝ) :
    nonprincipalPrimitiveSourceEnergy Q B N H =
      ∑ q : PositiveLevel Q,
        if q.val = 1 then 0 else rawPrimitiveSourceEnergy q.val B N H := by
  unfold nonprincipalPrimitiveSourceEnergy nonprincipalPrimitiveSlotSource
    primitiveBaseSlotSource rawPrimitiveSourceEnergy
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro q _hq
  by_cases hqOne : q.val = 1
  · simp [hqOne]
  · rw [if_neg hqOne]
    simp only [hqOne, if_false]
    rw [← Finset.sum_subtype
      (Finset.univ.filter
        (fun chi : DirichletCharacter ℂ q.val => chi.IsPrimitive))
      (by simp)
      (fun chi =>
        ‖(2 * (H : ℂ))⁻¹ *
          ∑ U ∈ centeredWindow (blockCarrier B) N H,
            blockInput B U * star (chi (U : ZMod q.val))‖ ^ 2)]
    apply Finset.sum_congr rfl
    intro chi _hchi
    apply congrArg (fun z : ℂ => ‖(2 * (H : ℂ))⁻¹ * z‖ ^ 2)
    change (∑ U ∈ actualWindowCarrier B N H,
        blockInput B U * star (chi (U : ZMod q.val))) =
      ∑ i : ↑(actualWindowCarrier B N H),
        blockInput B i.val * star (chi (i.val : ZMod q.val))
    rw [Finset.sum_subtype]
    intro x
    rfl

/-- Removing the principal conductor cannot increase the nonnegative source
energy.  This comparison is exact at slot level and introduces no analytic
cancellation claim. -/
theorem nonprincipalPrimitiveSourceEnergy_le_primitiveBaseSourceEnergy
    (Q B N : ℕ) (H : ℝ) :
    nonprincipalPrimitiveSourceEnergy Q B N H ≤
      primitiveBaseSourceEnergy Q B N H := by
  unfold nonprincipalPrimitiveSourceEnergy nonprincipalPrimitiveSlotSource
    primitiveBaseSourceEnergy
  apply Finset.sum_le_sum
  intro t _ht
  by_cases hprincipal : t.1.val = 1
  · simp [hprincipal]
  · simp [hprincipal]

end GoldbachCircleMethodNonprincipalPrimitiveConductorDecompositionV18507
