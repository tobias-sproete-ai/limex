import GoldbachCircleMethodExceptionalSourceBlockDecayV18523
import GoldbachCircleMethodHybridCenteredCorrelationEnergyV18501

/-!
# Goldbach V1.8.524: exceptional-correlation block decay

The exact one-slot correlation is combined with V1.8.523.  The resulting
pointwise hybrid estimate retains `((B : ℝ) / 2)^(-2*b)` instead of the
uniform `9/4` exceptional correction used by V1.8.501.  This is a local
source-side sharpening only.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodExceptionalCorrelationBlockDecayV18524

open GoldbachCircleMethodActiveExceptionalCenteringV18129
open GoldbachCircleMethodAdjustedCharacterSlotL2AdapterV18449
open GoldbachCircleMethodAdjustedSourceThreeTermDecompositionV18479
open GoldbachCircleMethodExceptionalSourceBlockDecayV18523
open GoldbachCircleMethodFiniteCompanionBindingV18118
open GoldbachCircleMethodHybridCenteredCorrelationEnergyV18501
open GoldbachCircleMethodHybridCenteredSourceSplitV18500
open GoldbachCircleMethodLogCutoffPresieveBindingV18120
open GoldbachCircleMethodPrincipalExceptionalSourceEnergyV18480
open GoldbachCircleMethodPrincipalWindowBoundaryV18121
open GoldbachCircleMethodSparseCorrectionCorrelationSplitV18482

/-- The selected exceptional correlation inherits the true squared dyadic
decay of its one source slot. -/
theorem exceptionalPowerCorrelation_sq_le_block_decay
    (Q B N : ℕ) (H b : ℝ) (w : ℕ → ℂ)
    (hB : 2 ≤ B) (hH : 1 ≤ H) (hb : 0 ≤ b) (e : CharacterSlot Q) :
    ‖exceptionalPowerCorrelation Q B N H b w e‖ ^ 2 ≤
      ((9 / 4 : ℝ) * ((B : ℝ) / 2) ^ (-2 * b)) *
        ‖windowCoefficient e.1 N w e.2‖ ^ 2 := by
  rw [exceptionalPowerCorrelation_eq_single, norm_mul, mul_pow]
  have hsource := exceptionalPowerSourceEnergy_le_block_decay
    Q B N H b hB hH hb e
  unfold exceptionalPowerSourceEnergy at hsource
  rw [Finset.sum_eq_single e] at hsource
  · nlinarith [sq_nonneg ‖windowCoefficient e.1 N w e.2‖]
  · intro t _ht hte
    rw [exceptionalPowerSlotSource_eq_zero_of_ne Q B N H b e t hte]
    norm_num
  · simp

/-- Hybrid three-channel energy with the exceptional exponent preserved. -/
theorem adjustedCenteredError_sq_le_hybrid_block_decay
    (Q B N : ℕ) (H b : ℝ) (w : ℕ → ℂ)
    (hB : 2 ≤ B) (hH : 1 ≤ H) (hb : 0 ≤ b) (e : CharacterSlot Q) :
    ‖adjustedCenteredError Q B N H b (blockInput B) w e‖ ^ 2 ≤
      3 * (centeredPrincipalCoefficientEnergy Q N w *
            centeredPrincipalSourceEnergy Q B N H +
          nonprincipalCoefficientEnergy Q N w *
            nonprincipalPrimitiveSourceEnergy Q B N H +
          ((9 / 4 : ℝ) * ((B : ℝ) / 2) ^ (-2 * b)) *
            ‖windowCoefficient e.1 N w e.2‖ ^ 2) := by
  rw [adjustedCenteredError_eq_hybrid_correlations]
  calc
    _ ≤ 3 * (‖centeredPrincipalCorrelation Q B N H w‖ ^ 2 +
          ‖nonprincipalPrimitiveCorrelation Q B N H w‖ ^ 2 +
          ‖exceptionalPowerCorrelation Q B N H b w e‖ ^ 2) :=
      norm_add_add_sq_le_three _ _ _
    _ ≤ _ := by
      gcongr
      · exact centeredPrincipalCorrelation_sq_le Q B N H w
      · exact nonprincipalPrimitiveCorrelation_sq_le Q B N H w
      · exact exceptionalPowerCorrelation_sq_le_block_decay
          Q B N H b w hB hH hb e

end GoldbachCircleMethodExceptionalCorrelationBlockDecayV18524
