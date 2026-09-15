import GoldbachCircleMethodAdjustedSourceSpanEnvelopeV18481

/-!
# Goldbach V1.8.482: sparse correction correlation split

The adjusted character correlation is split before applying family-wide
Cauchy--Schwarz. Thus the one-level principal subtraction and one-slot
exceptional correction are not multiplied by the full character-family
energy. This removes an artificial conductor-cardinality loss.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodSparseCorrectionCorrelationSplitV18482

open GoldbachCircleMethodActiveExceptionalCenteringV18129
open GoldbachCircleMethodAdjustedCharacterSlotL2AdapterV18449
open GoldbachCircleMethodFiniteCompanionBindingV18118
open GoldbachCircleMethodFiniteWindowConvolutionV18119
open GoldbachCircleMethodLogCutoffPresieveBindingV18120
open GoldbachCircleMethodPrincipalWindowBoundaryV18121
open GoldbachCircleMethodPrimitiveBaseSlotEnergyV18474
open GoldbachCircleMethodAdjustedSourceThreeTermDecompositionV18479
open GoldbachCircleMethodPrincipalExceptionalSourceEnergyV18480

noncomputable def primitiveBaseCorrelation
    (Q B N : ℕ) (H : ℝ) (w : ℕ → ℂ) : ℂ :=
  ∑ t : CharacterSlot Q,
    windowCoefficient t.1 N w t.2 * primitiveBaseSlotSource Q B N H t

noncomputable def principalCorrelation
    (Q B N : ℕ) (H : ℝ) (w : ℕ → ℂ) : ℂ :=
  ∑ t : CharacterSlot Q,
    windowCoefficient t.1 N w t.2 * principalSlotSource Q B N H t

noncomputable def exceptionalPowerCorrelation
    (Q B N : ℕ) (H b : ℝ) (w : ℕ → ℂ)
    (e : CharacterSlot Q) : ℂ :=
  ∑ t : CharacterSlot Q,
    windowCoefficient t.1 N w t.2 *
      exceptionalPowerSlotSource Q B N H b e t

theorem adjustedCenteredError_eq_three_correlations
    (Q B N : ℕ) (H b : ℝ) (w : ℕ → ℂ) (e : CharacterSlot Q) :
    adjustedCenteredError Q B N H b (blockInput B) w e =
      primitiveBaseCorrelation Q B N H w +
        principalCorrelation Q B N H w +
          exceptionalPowerCorrelation Q B N H b w e := by
  change (∑ t : CharacterSlot Q,
      windowCoefficient t.1 N w t.2 *
        adjustedSlotSource Q B N H b (blockInput B) e t) = _
  simp_rw [adjustedSlotSource_eq_three_terms]
  unfold primitiveBaseCorrelation principalCorrelation exceptionalPowerCorrelation
  simp only [mul_add, Finset.sum_add_distrib]

theorem primitiveBaseCorrelation_sq_le_energy_product
    (Q B N : ℕ) (H : ℝ) (w : ℕ → ℂ) :
    ‖primitiveBaseCorrelation Q B N H w‖ ^ 2 ≤
      adjustedCoefficientEnergy Q N w * primitiveBaseSourceEnergy Q B N H := by
  have htriangle :
      ‖primitiveBaseCorrelation Q B N H w‖ ≤
        ∑ t : CharacterSlot Q,
          ‖windowCoefficient t.1 N w t.2‖ *
            ‖primitiveBaseSlotSource Q B N H t‖ := by
    unfold primitiveBaseCorrelation
    calc
      ‖∑ t : CharacterSlot Q,
          windowCoefficient t.1 N w t.2 *
            primitiveBaseSlotSource Q B N H t‖ ≤
          ∑ t : CharacterSlot Q,
            ‖windowCoefficient t.1 N w t.2 *
              primitiveBaseSlotSource Q B N H t‖ := norm_sum_le _ _
      _ = _ := by
        apply Finset.sum_congr rfl
        intro t _ht
        rw [norm_mul]
  have hleft : 0 ≤ ‖primitiveBaseCorrelation Q B N H w‖ := norm_nonneg _
  have hright : 0 ≤ ∑ t : CharacterSlot Q,
      ‖windowCoefficient t.1 N w t.2‖ *
        ‖primitiveBaseSlotSource Q B N H t‖ := by positivity
  have hsq := (sq_le_sq₀ hleft hright).mpr htriangle
  apply hsq.trans
  unfold adjustedCoefficientEnergy primitiveBaseSourceEnergy
  exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun t : CharacterSlot Q => ‖windowCoefficient t.1 N w t.2‖)
    (fun t : CharacterSlot Q => ‖primitiveBaseSlotSource Q B N H t‖)

theorem exceptionalPowerCorrelation_eq_single
    (Q B N : ℕ) (H b : ℝ) (w : ℕ → ℂ) (e : CharacterSlot Q) :
    exceptionalPowerCorrelation Q B N H b w e =
      windowCoefficient e.1 N w e.2 *
        exceptionalPowerSlotSource Q B N H b e e := by
  unfold exceptionalPowerCorrelation
  rw [Finset.sum_eq_single e]
  · intro t _ht hte
    rw [exceptionalPowerSlotSource_eq_zero_of_ne Q B N H b e t hte]
    simp
  · simp

theorem exceptionalPowerCorrelation_sq_le_single_coefficient
    (Q B N : ℕ) (H b : ℝ) (w : ℕ → ℂ)
    (hH : 1 ≤ H) (hb : 0 ≤ b) (e : CharacterSlot Q) :
    ‖exceptionalPowerCorrelation Q B N H b w e‖ ^ 2 ≤
      (9 / 4 : ℝ) * ‖windowCoefficient e.1 N w e.2‖ ^ 2 := by
  rw [exceptionalPowerCorrelation_eq_single]
  rw [norm_mul, mul_pow]
  have hsource := exceptionalPowerSlotSource_norm_le_three_halves
    Q B N H b hH hb e e
  have hsourceSq :
      ‖exceptionalPowerSlotSource Q B N H b e e‖ ^ 2 ≤ (9 : ℝ) / 4 := by
    nlinarith [norm_nonneg (exceptionalPowerSlotSource Q B N H b e e)]
  nlinarith [sq_nonneg ‖windowCoefficient e.1 N w e.2‖]

/-- Three-channel correction bound with the sparse exceptional term already
reduced to its single actual coefficient. The principal correlation remains
separate for the next one-level support reduction. -/
theorem adjustedCenteredError_sq_le_sparse_three_channel
    (Q B N : ℕ) (H b : ℝ) (w : ℕ → ℂ)
    (hH : 1 ≤ H) (hb : 0 ≤ b) (e : CharacterSlot Q) :
    ‖adjustedCenteredError Q B N H b (blockInput B) w e‖ ^ 2 ≤
      3 * (adjustedCoefficientEnergy Q N w *
          primitiveBaseSourceEnergy Q B N H +
        ‖principalCorrelation Q B N H w‖ ^ 2 +
        (9 / 4 : ℝ) * ‖windowCoefficient e.1 N w e.2‖ ^ 2) := by
  rw [adjustedCenteredError_eq_three_correlations]
  calc
    ‖primitiveBaseCorrelation Q B N H w +
        principalCorrelation Q B N H w +
          exceptionalPowerCorrelation Q B N H b w e‖ ^ 2 ≤
      3 * (‖primitiveBaseCorrelation Q B N H w‖ ^ 2 +
        ‖principalCorrelation Q B N H w‖ ^ 2 +
          ‖exceptionalPowerCorrelation Q B N H b w e‖ ^ 2) :=
        norm_add_add_sq_le_three _ _ _
    _ ≤ 3 * (adjustedCoefficientEnergy Q N w *
          primitiveBaseSourceEnergy Q B N H +
        ‖principalCorrelation Q B N H w‖ ^ 2 +
        (9 / 4 : ℝ) * ‖windowCoefficient e.1 N w e.2‖ ^ 2) := by
      gcongr
      · exact primitiveBaseCorrelation_sq_le_energy_product Q B N H w
      · exact exceptionalPowerCorrelation_sq_le_single_coefficient
          Q B N H b w hH hb e

end GoldbachCircleMethodSparseCorrectionCorrelationSplitV18482
