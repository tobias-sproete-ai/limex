import GoldbachCircleMethodCharacterEnergyPullbackV18472

/-!
# Goldbach V1.8.473: actual primitive-source energy

The fixed-modulus character collision estimate is instantiated on the literal
centered dyadic window.  The exact `1/(2H)` normalization is then restored.
No distribution hypothesis or asymptotic estimate is introduced.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodActualPrimitiveSourceEnergyV18473

open GoldbachCircleMethodFiniteCarrierStarCharacterEnergyV18467
open GoldbachCircleMethodActualWindowInputEnergyV18469
open GoldbachCircleMethodActualPrimitiveSourceNormalizationV18470
open GoldbachCircleMethodCharacterEnergyPullbackV18472
open GoldbachCircleMethodLogCutoffPresieveBindingV18120

/-- The primitive-character energy on the actual centered window is bounded by
the literal residue-collision factor and the verified window-input budget. -/
theorem actualWindow_conjugateCharacterEnergy_le
    (q B N : ℕ) [NeZero q] (H : ℝ) (hB : 2 ≤ B) (hH : 0 ≤ H) :
    conjugateCharacterEnergy q (actualWindowCarrier B N H)
        (fun i => blockInput B i.val)
        (fun chi : DirichletCharacter ℂ q => chi.IsPrimitive) ≤
      (q.totient : ℝ) * (((B + 1) / q + 1 : ℕ) : ℝ) *
        ((2 * H + 1) * (Real.log (B : ℝ)) ^ 2) := by
  have hchar := conjugateCharacterEnergy_le q (B + 1)
    (actualWindowCarrier B N H)
    (fun n hn => actualWindowCarrier_mem_lt_succ B N n H hn)
    (fun i => blockInput B i.val)
    (fun chi : DirichletCharacter ℂ q => chi.IsPrimitive)
  have hK : 0 ≤ (q.totient : ℝ) * (((B + 1) / q + 1 : ℕ) : ℝ) := by
    positivity
  exact hchar.trans (mul_le_mul_of_nonneg_left
    (actual_window_blockInput_energy_le B N H hB hH) hK)

/-- Closed fixed-modulus bound for the exactly normalized primitive source. -/
theorem rawPrimitiveSourceEnergy_le_actual_budget
    (q B N : ℕ) [NeZero q] (H : ℝ) (hB : 2 ≤ B) (hH : 0 ≤ H) :
    rawPrimitiveSourceEnergy q B N H ≤
      ‖(2 * (H : ℂ))⁻¹‖ ^ 2 *
        ((q.totient : ℝ) * (((B + 1) / q + 1 : ℕ) : ℝ) *
          ((2 * H + 1) * (Real.log (B : ℝ)) ^ 2)) := by
  rw [rawPrimitiveSourceEnergy_eq]
  exact mul_le_mul_of_nonneg_left
    (actualWindow_conjugateCharacterEnergy_le q B N H hB hH)
    (sq_nonneg _)

end GoldbachCircleMethodActualPrimitiveSourceEnergyV18473
