import GoldbachCircleMethodWindowSpanResidueMultiplicityV18476

/-!
# Goldbach V1.8.477: sharp actual-window character energy

The character collision estimate now uses the actual window span
`2*floor(H)`, replacing the intentionally coarse whole-block range bound.
-/

set_option autoImplicit false
set_option maxHeartbeats 1800000

open scoped BigOperators Classical

namespace GoldbachCircleMethodActualWindowCharacterEnergySharpV18477

open GoldbachCircleMethodFiniteCarrierStarCharacterEnergyV18467
open GoldbachCircleMethodResidueCollisionEnergyV18463
open GoldbachCircleMethodActualWindowInputEnergyV18469
open GoldbachCircleMethodActualPrimitiveSourceNormalizationV18470
open GoldbachCircleMethodWindowSpanResidueMultiplicityV18476
open GoldbachCircleMethodLogCutoffPresieveBindingV18120
open GoldbachCircleMethodConcreteUnitIndexEnergyV18471
open GoldbachCircleMethodCharacterEnergyPullbackV18472

theorem concrete_actualWindow_unit_fiber_card_le_span
    (q B N : ℕ) [NeZero q] (H : ℝ) (hH : 0 ≤ H)
    (u : (ZMod q)ˣ) :
    Fintype.card {i : ConcreteUnitIndex q (actualWindowCarrier B N H) //
      concreteUnitResidue q (actualWindowCarrier B N H) i = u} ≤
      (2 * ⌊H⌋₊) / q + 1 := by
  let e :
      {i : ConcreteUnitIndex q (actualWindowCarrier B N H) //
          concreteUnitResidue q (actualWindowCarrier B N H) i = u} ≃
        {j : NaturalUnitIndex q (actualWindowCarrier B N H) //
          naturalUnitResidue q (actualWindowCarrier B N H) j = u} :=
    { toFun := fun i =>
        ⟨concreteUnitIndexEquiv q (actualWindowCarrier B N H) i.val, by
          rw [concreteUnitResidue_compatible]
          exact i.property⟩
      invFun := fun j =>
        ⟨(concreteUnitIndexEquiv q (actualWindowCarrier B N H)).symm j.val, by
          calc
            concreteUnitResidue q (actualWindowCarrier B N H)
                ((concreteUnitIndexEquiv q
                  (actualWindowCarrier B N H)).symm j.val) =
                naturalUnitResidue q (actualWindowCarrier B N H) j.val := by
              rw [← concreteUnitResidue_compatible,
                (concreteUnitIndexEquiv q
                  (actualWindowCarrier B N H)).apply_symm_apply]
            _ = u := j.property⟩
      left_inv := by
        intro i
        apply Subtype.ext
        exact (concreteUnitIndexEquiv q
          (actualWindowCarrier B N H)).symm_apply_apply i.val
      right_inv := by
        intro j
        apply Subtype.ext
        exact (concreteUnitIndexEquiv q
          (actualWindowCarrier B N H)).apply_symm_apply j.val }
  rw [Fintype.card_congr e]
  exact actualWindow_unit_fiber_card_le_span q B N H hH u

/-- Sharp character-energy estimate on the literal centered-window carrier. -/
theorem actualWindow_conjugateCharacterEnergy_le_span
    (q B N : ℕ) [NeZero q] (H : ℝ) (hH : 0 ≤ H)
    (a : ↑(actualWindowCarrier B N H) → ℂ)
    (P : DirichletCharacter ℂ q → Prop) [DecidablePred P] :
    conjugateCharacterEnergy q (actualWindowCarrier B N H) a P ≤
      (q.totient : ℝ) * (((2 * ⌊H⌋₊) / q + 1 : ℕ) : ℝ) *
        ∑ i : ↑(actualWindowCarrier B N H), ‖a i‖ ^ 2 := by
  calc
    conjugateCharacterEnergy q (actualWindowCarrier B N H) a P =
        concreteRetainedStarEnergy q (actualWindowCarrier B N H) a P :=
      ((conjugateCharacterEnergy_eq_full q
          (actualWindowCarrier B N H) a P).trans
        (starredFullResidueEnergy_eq_retained q
          (actualWindowCarrier B N H) a P)).trans
        (retainedStarEnergy_eq_concrete q
          (actualWindowCarrier B N H) a P)
    _ ≤ (q.totient : ℝ) * (((2 * ⌊H⌋₊) / q + 1 : ℕ) : ℝ) *
        ∑ i : ConcreteUnitIndex q (actualWindowCarrier B N H),
          ‖star (a i.index)‖ ^ 2 := by
      unfold concreteRetainedStarEnergy
      exact filtered_character_energy_le_totient_mul_collision q
        (concreteUnitResidue q (actualWindowCarrier B N H))
        (fun i : ConcreteUnitIndex q (actualWindowCarrier B N H) =>
          star (a i.index))
        ((2 * ⌊H⌋₊) / q + 1)
        (concrete_actualWindow_unit_fiber_card_le_span q B N H hH) P
    _ ≤ (q.totient : ℝ) * (((2 * ⌊H⌋₊) / q + 1 : ℕ) : ℝ) *
        ∑ i : ↑(actualWindowCarrier B N H), ‖a i‖ ^ 2 := by
      have hK : 0 ≤ (q.totient : ℝ) *
          (((2 * ⌊H⌋₊) / q + 1 : ℕ) : ℝ) := by
        positivity
      exact mul_le_mul_of_nonneg_left
        (concrete_coefficient_energy_le_full q
          (actualWindowCarrier B N H) a) hK

/-- Exactly normalized fixed-conductor source bound with sharp window span. -/
theorem rawPrimitiveSourceEnergy_le_span_budget
    (q B N : ℕ) [NeZero q] (H : ℝ)
    (hB : 2 ≤ B) (hH : 0 ≤ H) :
    rawPrimitiveSourceEnergy q B N H ≤
      ‖(2 * (H : ℂ))⁻¹‖ ^ 2 *
        ((q.totient : ℝ) * (((2 * ⌊H⌋₊) / q + 1 : ℕ) : ℝ) *
          ((2 * H + 1) * (Real.log (B : ℝ)) ^ 2)) := by
  rw [rawPrimitiveSourceEnergy_eq]
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  exact (actualWindow_conjugateCharacterEnergy_le_span q B N H hH
    (fun i => blockInput B i.val)
    (fun chi : DirichletCharacter ℂ q => chi.IsPrimitive)).trans
      (mul_le_mul_of_nonneg_left
        (actual_window_blockInput_energy_le B N H hB hH) (by positivity))

end GoldbachCircleMethodActualWindowCharacterEnergySharpV18477
