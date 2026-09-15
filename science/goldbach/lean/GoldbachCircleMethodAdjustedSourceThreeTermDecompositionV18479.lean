import GoldbachCircleMethodPrimitiveBaseSpanEnvelopeV18478

/-!
# Goldbach V1.8.479: adjusted-source three-term decomposition

The literal adjusted source is separated into its primitive base, principal
subtraction, and exceptional power correction.  A finite three-term norm
inequality keeps the three budgets independent.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodAdjustedSourceThreeTermDecompositionV18479

open GoldbachCircleMethodActiveExceptionalCenteringV18129
open GoldbachCircleMethodFiniteWindowConvolutionV18119
open GoldbachCircleMethodLogCutoffPresieveBindingV18120
open GoldbachCircleMethodExceptionalWeightBoundaryV18128
open GoldbachCircleMethodAdjustedCharacterSlotL2AdapterV18449
open GoldbachCircleMethodPrimitiveBaseSlotEnergyV18474

noncomputable def principalSlotSource
    (Q B N : ℕ) (H : ℝ) (t : CharacterSlot Q) : ℂ :=
  (2 * (H : ℂ))⁻¹ *
    ∑ _U ∈ centeredWindow (blockCarrier B) N H,
      -(if t.1.val = 1 then 1 else 0)

noncomputable def exceptionalPowerSlotSource
    (Q B N : ℕ) (H b : ℝ) (e t : CharacterSlot Q) : ℂ :=
  (2 * (H : ℂ))⁻¹ *
    ∑ U ∈ centeredWindow (blockCarrier B) N H,
      if t = e then (powerWeight b U : ℂ) else 0

noncomputable def principalSourceEnergy
    (Q B N : ℕ) (H : ℝ) : ℝ :=
  ∑ t : CharacterSlot Q, ‖principalSlotSource Q B N H t‖ ^ 2

noncomputable def exceptionalPowerSourceEnergy
    (Q B N : ℕ) (H b : ℝ) (e : CharacterSlot Q) : ℝ :=
  ∑ t : CharacterSlot Q, ‖exceptionalPowerSlotSource Q B N H b e t‖ ^ 2

theorem adjustedSlotSource_eq_three_terms
    (Q B N : ℕ) (H b : ℝ) (e t : CharacterSlot Q) :
    adjustedSlotSource Q B N H b (blockInput B) e t =
      primitiveBaseSlotSource Q B N H t +
        principalSlotSource Q B N H t +
          exceptionalPowerSlotSource Q B N H b e t := by
  unfold adjustedSlotSource primitiveBaseSlotSource principalSlotSource
    exceptionalPowerSlotSource
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_neg_distrib]
  ring

theorem norm_add_add_sq_le_three
    (x y z : ℂ) :
    ‖x + y + z‖ ^ 2 ≤ 3 * (‖x‖ ^ 2 + ‖y‖ ^ 2 + ‖z‖ ^ 2) := by
  have htri : ‖x + y + z‖ ≤ ‖x‖ + ‖y‖ + ‖z‖ := by
    have hxy := norm_add_le x y
    have hxyz := norm_add_le (x + y) z
    linarith
  have hsq : ‖x + y + z‖ ^ 2 ≤ (‖x‖ + ‖y‖ + ‖z‖) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr htri
  nlinarith [sq_nonneg (‖x‖ - ‖y‖), sq_nonneg (‖x‖ - ‖z‖),
    sq_nonneg (‖y‖ - ‖z‖)]

/-- The adjusted source energy is bounded by three independently auditable
energies; no term is hidden in an asymptotic remainder. -/
theorem adjustedSourceEnergy_le_three_budgets
    (Q B N : ℕ) (H b : ℝ) (e : CharacterSlot Q) :
    adjustedSourceEnergy Q B N H b (blockInput B) e ≤
      3 * (primitiveBaseSourceEnergy Q B N H +
        principalSourceEnergy Q B N H +
          exceptionalPowerSourceEnergy Q B N H b e) := by
  unfold adjustedSourceEnergy primitiveBaseSourceEnergy principalSourceEnergy
    exceptionalPowerSourceEnergy
  calc
    (∑ t : CharacterSlot Q,
        ‖adjustedSlotSource Q B N H b (blockInput B) e t‖ ^ 2) ≤
        ∑ t : CharacterSlot Q,
          3 * (‖primitiveBaseSlotSource Q B N H t‖ ^ 2 +
            ‖principalSlotSource Q B N H t‖ ^ 2 +
              ‖exceptionalPowerSlotSource Q B N H b e t‖ ^ 2) := by
      apply Finset.sum_le_sum
      intro t _ht
      rw [adjustedSlotSource_eq_three_terms]
      exact norm_add_add_sq_le_three _ _ _
    _ = _ := by
      rw [← Finset.mul_sum]
      congr 1
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib]

end GoldbachCircleMethodAdjustedSourceThreeTermDecompositionV18479
