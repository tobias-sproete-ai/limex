import GoldbachCircleMethodSparseCorrectionCorrelationSplitV18482

/-!
# Goldbach V1.8.483: principal support-energy split

The principal subtraction is supported only on the conductor-one slots. Its
correlation is therefore paired with a restricted coefficient energy rather
than the full character-family energy.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodPrincipalSupportEnergySplitV18483

open GoldbachCircleMethodActiveExceptionalCenteringV18129
open GoldbachCircleMethodAdjustedCharacterSlotL2AdapterV18449
open GoldbachCircleMethodFiniteCompanionBindingV18118
open GoldbachCircleMethodLogCutoffPresieveBindingV18120
open GoldbachCircleMethodPrincipalWindowBoundaryV18121
open GoldbachCircleMethodPrimitiveBaseSlotEnergyV18474
open GoldbachCircleMethodAdjustedSourceThreeTermDecompositionV18479
open GoldbachCircleMethodPrincipalExceptionalSourceEnergyV18480
open GoldbachCircleMethodSparseCorrectionCorrelationSplitV18482

/-- Coefficient energy restricted to the actual support of the principal
subtraction. -/
noncomputable def principalCoefficientEnergy
    (Q N : ℕ) (w : ℕ → ℂ) : ℝ :=
  ∑ t : CharacterSlot Q,
    if t.1.val = 1 then ‖windowCoefficient t.1 N w t.2‖ ^ 2 else 0

theorem principalCorrelation_eq_restricted
    (Q B N : ℕ) (H : ℝ) (w : ℕ → ℂ) :
    principalCorrelation Q B N H w =
      ∑ t : CharacterSlot Q,
        (if t.1.val = 1 then windowCoefficient t.1 N w t.2 else 0) *
          principalSlotSource Q B N H t := by
  unfold principalCorrelation
  apply Finset.sum_congr rfl
  intro t _ht
  by_cases hlevel : t.1.val = 1
  · simp [hlevel]
  · rw [principalSlotSource_eq_zero_of_level_ne_one Q B N H t hlevel]
    simp [hlevel]

theorem principalCorrelation_sq_le_restricted_energy_product
    (Q B N : ℕ) (H : ℝ) (w : ℕ → ℂ) :
    ‖principalCorrelation Q B N H w‖ ^ 2 ≤
      principalCoefficientEnergy Q N w * principalSourceEnergy Q B N H := by
  rw [principalCorrelation_eq_restricted]
  have htriangle :
      ‖∑ t : CharacterSlot Q,
          (if t.1.val = 1 then windowCoefficient t.1 N w t.2 else 0) *
            principalSlotSource Q B N H t‖ ≤
        ∑ t : CharacterSlot Q,
          ‖if t.1.val = 1 then windowCoefficient t.1 N w t.2 else 0‖ *
            ‖principalSlotSource Q B N H t‖ := by
    calc
      _ ≤ ∑ t : CharacterSlot Q,
          ‖(if t.1.val = 1 then windowCoefficient t.1 N w t.2 else 0) *
            principalSlotSource Q B N H t‖ := norm_sum_le _ _
      _ = _ := by
        apply Finset.sum_congr rfl
        intro t _ht
        rw [norm_mul]
  have hleft : 0 ≤ ‖∑ t : CharacterSlot Q,
      (if t.1.val = 1 then windowCoefficient t.1 N w t.2 else 0) *
        principalSlotSource Q B N H t‖ := norm_nonneg _
  have hright : 0 ≤ ∑ t : CharacterSlot Q,
      ‖if t.1.val = 1 then windowCoefficient t.1 N w t.2 else 0‖ *
        ‖principalSlotSource Q B N H t‖ := by positivity
  have hsq := (sq_le_sq₀ hleft hright).mpr htriangle
  apply hsq.trans
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun t : CharacterSlot Q =>
      ‖if t.1.val = 1 then windowCoefficient t.1 N w t.2 else 0‖)
    (fun t : CharacterSlot Q => ‖principalSlotSource Q B N H t‖)
  apply hcs.trans_eq
  unfold principalCoefficientEnergy principalSourceEnergy
  congr 1
  apply Finset.sum_congr rfl
  intro t _ht
  by_cases hlevel : t.1.val = 1 <;> simp [hlevel]

theorem principalCorrelation_sq_le_restricted_coefficient
    (Q B N : ℕ) (H : ℝ) (w : ℕ → ℂ) (hH : 1 ≤ H) :
    ‖principalCorrelation Q B N H w‖ ^ 2 ≤
      (9 / 4 : ℝ) * principalCoefficientEnergy Q N w := by
  have hsource := principalSourceEnergy_le_nine_fourths Q B N H hH
  have hcoefficient : 0 ≤ principalCoefficientEnergy Q N w := by
    unfold principalCoefficientEnergy
    exact Finset.sum_nonneg fun t _ht => by split_ifs <;> positivity
  calc
    ‖principalCorrelation Q B N H w‖ ^ 2 ≤
        principalCoefficientEnergy Q N w * principalSourceEnergy Q B N H :=
      principalCorrelation_sq_le_restricted_energy_product Q B N H w
    _ ≤ principalCoefficientEnergy Q N w * ((9 : ℝ) / 4) :=
      mul_le_mul_of_nonneg_left hsource hcoefficient
    _ = (9 / 4 : ℝ) * principalCoefficientEnergy Q N w := by ring

/-- Fully sparse three-channel correction bound. Only the primitive base
retains the full family-energy product. -/
theorem adjustedCenteredError_sq_le_support_separated
    (Q B N : ℕ) (H b : ℝ) (w : ℕ → ℂ)
    (hH : 1 ≤ H) (hb : 0 ≤ b) (e : CharacterSlot Q) :
    ‖adjustedCenteredError Q B N H b (blockInput B) w e‖ ^ 2 ≤
      3 * (adjustedCoefficientEnergy Q N w *
          primitiveBaseSourceEnergy Q B N H +
        (9 / 4 : ℝ) * principalCoefficientEnergy Q N w +
        (9 / 4 : ℝ) * ‖windowCoefficient e.1 N w e.2‖ ^ 2) := by
  calc
    ‖adjustedCenteredError Q B N H b (blockInput B) w e‖ ^ 2 ≤
      3 * (adjustedCoefficientEnergy Q N w *
          primitiveBaseSourceEnergy Q B N H +
        ‖principalCorrelation Q B N H w‖ ^ 2 +
        (9 / 4 : ℝ) * ‖windowCoefficient e.1 N w e.2‖ ^ 2) :=
      adjustedCenteredError_sq_le_sparse_three_channel
        Q B N H b w hH hb e
    _ ≤ 3 * (adjustedCoefficientEnergy Q N w *
          primitiveBaseSourceEnergy Q B N H +
        (9 / 4 : ℝ) * principalCoefficientEnergy Q N w +
        (9 / 4 : ℝ) * ‖windowCoefficient e.1 N w e.2‖ ^ 2) := by
      gcongr
      exact principalCorrelation_sq_le_restricted_coefficient Q B N H w hH

end GoldbachCircleMethodPrincipalSupportEnergySplitV18483
