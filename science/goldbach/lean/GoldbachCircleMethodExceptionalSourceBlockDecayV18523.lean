import GoldbachCircleMethodPrincipalExceptionalSourceEnergyV18480

/-!
# Goldbach V1.8.523: exceptional-source block decay

V1.8.480 used only `|U^(-b)| ≤ 1` and therefore paid a uniform `9/4`
source-energy cost for the selected exceptional slot.  This append-only
successor retains the actual dyadic lower bound `B/2 < U` and exposes the
resulting `((B : ℝ) / 2)^(-2*b)` decay.  No uniform lower bound on `b` and
no Goldbach conclusion are asserted.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodExceptionalSourceBlockDecayV18523

open GoldbachCircleMethodActiveExceptionalCenteringV18129
open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodExceptionalWeightBoundaryV18128
open GoldbachCircleMethodFiniteWindowConvolutionV18119
open GoldbachCircleMethodLogCutoffPresieveBindingV18120
open GoldbachCircleMethodPrincipalExceptionalSourceEnergyV18480
open GoldbachCircleMethodAdjustedSourceThreeTermDecompositionV18479

/-- On the dyadic block `(B/2,B]`, the exceptional power weight retains its
actual negative-power decay instead of being replaced by one. -/
theorem power_weight_abs_le_block_decay
    (B U : ℕ) (hB : 2 ≤ B) (b : ℝ) (hb : 0 ≤ b)
    (hU : U ∈ blockCarrier B) :
    |powerWeight b U| ≤ ((B : ℝ) / 2) ^ (-b) := by
  have hbase : 0 < (B : ℝ) / 2 := by
    exact div_pos (by exact_mod_cast (show 0 < B by omega)) (by norm_num)
  have hBU : (B : ℝ) / 2 ≤ (U : ℝ) := by
    have hlt : B / 2 < U := (Finset.mem_Ioc.mp hU).1
    have hnat : B ≤ 2 * U := by omega
    have hnat' : (B : ℝ) ≤ 2 * (U : ℝ) := by exact_mod_cast hnat
    linarith
  unfold powerWeight
  rw [abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg U) _)]
  exact Real.rpow_le_rpow_of_nonpos hbase hBU (by linarith)

/-- The normalized selected-slot source inherits the same block decay. -/
theorem exceptionalPowerSlotSource_norm_le_block_decay
    (Q B N : ℕ) (H b : ℝ) (hB : 2 ≤ B) (hH : 1 ≤ H) (hb : 0 ≤ b)
    (e t : CharacterSlot Q) :
    ‖exceptionalPowerSlotSource Q B N H b e t‖ ≤
      (3 / 2 : ℝ) * ((B : ℝ) / 2) ^ (-b) := by
  have hdecay : 0 ≤ ((B : ℝ) / 2) ^ (-b) :=
    Real.rpow_nonneg (by positivity) _
  unfold exceptionalPowerSlotSource
  rw [norm_mul]
  calc
    ‖(2 * (H : ℂ))⁻¹‖ *
        ‖∑ U ∈ centeredWindow (blockCarrier B) N H,
          if t = e then (powerWeight b U : ℂ) else 0‖ ≤
        ‖(2 * (H : ℂ))⁻¹‖ *
          ∑ U ∈ centeredWindow (blockCarrier B) N H,
            ‖if t = e then (powerWeight b U : ℂ) else 0‖ := by
      gcongr
      exact norm_sum_le _ _
    _ ≤ ‖(2 * (H : ℂ))⁻¹‖ *
        (((centeredWindow (blockCarrier B) N H).card : ℝ) *
          ((B : ℝ) / 2) ^ (-b)) := by
      gcongr
      calc
        (∑ U ∈ centeredWindow (blockCarrier B) N H,
            ‖if t = e then (powerWeight b U : ℂ) else 0‖) ≤
            ∑ _U ∈ centeredWindow (blockCarrier B) N H,
              ((B : ℝ) / 2) ^ (-b) := by
          apply Finset.sum_le_sum
          intro U hU
          split_ifs
          · rw [Complex.norm_real, Real.norm_eq_abs]
            exact power_weight_abs_le_block_decay B U hB b hb
              (Finset.filter_subset _ _ hU)
          · simpa using hdecay
        _ = ((centeredWindow (blockCarrier B) N H).card : ℝ) *
              ((B : ℝ) / 2) ^ (-b) := by
          rw [Finset.sum_const, nsmul_eq_mul]
    _ = (‖(2 * (H : ℂ))⁻¹‖ *
          ((centeredWindow (blockCarrier B) N H).card : ℝ)) *
            ((B : ℝ) / 2) ^ (-b) := by ring
    _ ≤ (3 / 2 : ℝ) * ((B : ℝ) / 2) ^ (-b) := by
      exact mul_le_mul_of_nonneg_right
        (normalized_centeredWindow_card_le_three_halves
          (blockCarrier B) N H hH) hdecay

/-- The one-slot exceptional source energy has the explicit squared decay
lost in V1.8.480. -/
theorem exceptionalPowerSourceEnergy_le_block_decay
    (Q B N : ℕ) (H b : ℝ) (hB : 2 ≤ B) (hH : 1 ≤ H) (hb : 0 ≤ b)
    (e : CharacterSlot Q) :
    exceptionalPowerSourceEnergy Q B N H b e ≤
      (9 / 4 : ℝ) * ((B : ℝ) / 2) ^ (-2 * b) := by
  have hnorm := exceptionalPowerSlotSource_norm_le_block_decay
    Q B N H b hB hH hb e e
  have hbase : 0 < (B : ℝ) / 2 := by positivity
  have hpow :
      (((B : ℝ) / 2) ^ (-b)) ^ 2 =
        ((B : ℝ) / 2) ^ (-2 * b) := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul hbase.le]
    congr 1
    ring
  unfold exceptionalPowerSourceEnergy
  rw [Finset.sum_eq_single e]
  · rw [← hpow]
    nlinarith [norm_nonneg (exceptionalPowerSlotSource Q B N H b e e)]
  · intro t _ht hte
    rw [exceptionalPowerSlotSource_eq_zero_of_ne Q B N H b e t hte]
    norm_num
  · simp

end GoldbachCircleMethodExceptionalSourceBlockDecayV18523
