import GoldbachCircleMethodActualPrimitiveSourceEnergyV18473

/-!
# Goldbach V1.8.474: primitive base-slot energy

The fixed-conductor estimates are reassembled on the literal `CharacterSlot`
carrier.  This module treats only the von-Mangoldt/character base term; the
principal subtraction and the exceptional correction remain separate.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodPrimitiveBaseSlotEnergyV18474

open GoldbachCircleMethodActiveExceptionalCenteringV18129
open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodFiniteWindowConvolutionV18119
open GoldbachCircleMethodLogCutoffPresieveBindingV18120
open GoldbachCircleMethodActualWindowInputEnergyV18469
open GoldbachCircleMethodActualPrimitiveSourceNormalizationV18470
open GoldbachCircleMethodActualPrimitiveSourceEnergyV18473

noncomputable def primitiveBaseSlotSource
    (Q B N : ℕ) (H : ℝ) (t : CharacterSlot Q) : ℂ :=
  (2 * (H : ℂ))⁻¹ *
    ∑ U ∈ centeredWindow (blockCarrier B) N H,
      blockInput B U * star (t.2.val (U : ZMod t.1.val))

noncomputable def primitiveBaseSourceEnergy
    (Q B N : ℕ) (H : ℝ) : ℝ :=
  ∑ t : CharacterSlot Q, ‖primitiveBaseSlotSource Q B N H t‖ ^ 2

/-- The sigma carrier is exactly the sum of the fixed-conductor energies. -/
theorem primitiveBaseSourceEnergy_eq_sum_raw
    (Q B N : ℕ) (H : ℝ) :
    primitiveBaseSourceEnergy Q B N H =
      ∑ q : PositiveLevel Q, rawPrimitiveSourceEnergy q.val B N H := by
  unfold primitiveBaseSourceEnergy primitiveBaseSlotSource rawPrimitiveSourceEnergy
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro q _hq
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

/-- Exact finite conductor-sum bound on the unadjusted primitive source. -/
theorem primitiveBaseSourceEnergy_le_level_sum
    (Q B N : ℕ) (H : ℝ) (hB : 2 ≤ B) (hH : 0 ≤ H) :
    primitiveBaseSourceEnergy Q B N H ≤
      ∑ q : PositiveLevel Q,
        ‖(2 * (H : ℂ))⁻¹‖ ^ 2 *
          ((q.val.totient : ℝ) *
            (((B + 1) / q.val + 1 : ℕ) : ℝ) *
              ((2 * H + 1) * (Real.log (B : ℝ)) ^ 2)) := by
  rw [primitiveBaseSourceEnergy_eq_sum_raw]
  apply Finset.sum_le_sum
  intro q _hq
  exact rawPrimitiveSourceEnergy_le_actual_budget q.val B N H hB hH

end GoldbachCircleMethodPrimitiveBaseSlotEnergyV18474
