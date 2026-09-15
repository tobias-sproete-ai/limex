import GoldbachCircleMethodCanonicalAbelPairwiseBoundV18332
import GoldbachCircleMethodAdmittedRhoPrincipalBudgetV18235
import GoldbachCircleMethodCanonicalBumpResidualMomentsV18222

/-!
# Goldbach V1.8.333: admitted canonical Abel absorption

The fixed admission threshold is strong enough for a `1344*R^8 < B` budget.
Together with the canonical bump bound and `Q=floor(R^2)`, this absorbs the
entire variable four-channel pairwise error below `B/56`.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodAdmittedCanonicalAbelAbsorptionV18333

open GoldbachCircleMethodActiveExceptionalCenteringV18129
open GoldbachCircleMethodActiveResidualExactDecompositionV18251
open GoldbachCircleMethodActualMultiplierScaleV18135
open GoldbachCircleMethodAdmittedRhoPrincipalBudgetV18235
open GoldbachCircleMethodBlockPairCarrierV18227
open GoldbachCircleMethodCanonicalAbelPairwiseBoundV18332
open GoldbachCircleMethodCanonicalBumpPrincipalFloorV18220
open GoldbachCircleMethodCanonicalBumpResidualMomentsV18222
open GoldbachCircleMethodLogCutoffPresieveBindingV18120
open GoldbachCircleMethodPowerWeightAbelIntervalV18331
open GoldbachCircleMethodPrincipalWindowBoundaryV18121
open GoldbachCircleMethodResidualScaleAdmissionV18196

theorem canonical_logWeight_norm_le_one (R : ℝ) (n : ℕ) :
    ‖logWeight R canonicalLogBump n‖ ≤ 1 :=
  log_weight_norm_le R canonicalLogBump 1 abs_canonicalLogBump_le_one n

/-- Strengthening of the fixed admitted eighth-power budget to the exact
constant needed by the Abel error reserve. -/
theorem admitted_scale_eighth_power_budget_1344
    (rho : ℝ) (hrho : 0 < rho) (hrhoUpper : rho ≤ (1 : ℝ) / 10000)
    (B : ℕ) (hB : blockThreshold rho ≤ B) :
    1344 * ((B : ℝ) ^ rho) ^ 8 < (B : ℝ) := by
  obtain ⟨_hB6, _hR2, _hlower, hupper⟩ :=
    actual_scale_admission rho hrho hrhoUpper B hB
  have hBOne : (1 : ℝ) ≤ B := by exact_mod_cast (show 1 ≤ B by omega)
  have hB0 : (0 : ℝ) ≤ B := le_trans zero_le_one hBOne
  have hR8 : ((B : ℝ) ^ rho) ^ 8 ≤ Real.sqrt (B : ℝ) := by
    calc
      ((B : ℝ) ^ rho) ^ 8 ≤
          ((B : ℝ) ^ ((1 : ℝ) / 10000)) ^ 8 :=
        pow_le_pow_left₀ (Real.rpow_nonneg hB0 rho) hupper 8
      _ = (B : ℝ) ^ ((1 : ℝ) / 1250) := by
        rw [← Real.rpow_mul_natCast hB0]
        norm_num
      _ ≤ (B : ℝ) ^ ((1 : ℝ) / 2) :=
        Real.rpow_le_rpow_of_exponent_le hBOne (by norm_num)
      _ = Real.sqrt (B : ℝ) := by rw [Real.sqrt_eq_rpow]
  have hThresholdLarge :=
    logThreshold_ge_one_hundred_million rho hrho hrhoUpper
  have hExpThreshold : Real.exp (logThreshold rho) ≤ (B : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hB)
  have hExpLarge : Real.exp (100000000 : ℝ) ≤
      Real.exp (logThreshold rho) := Real.exp_le_exp.mpr hThresholdLarge
  have hSquareExp : (1806336 : ℝ) < Real.exp (100000000 : ℝ) := by
    have h := Real.add_one_lt_exp (show (100000000 : ℝ) ≠ 0 by norm_num)
    linarith
  have hBbig : (1806336 : ℝ) < (B : ℝ) :=
    hSquareExp.trans_le (hExpLarge.trans hExpThreshold)
  have hsqrt : (1344 : ℝ) < Real.sqrt (B : ℝ) := by
    rw [Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 1344)]
    have hsquare : (1344 : ℝ) ^ 2 = 1806336 := by norm_num
    rwa [hsquare]
  have hsqrtPos : 0 < Real.sqrt (B : ℝ) :=
    Real.sqrt_pos.2 (lt_of_lt_of_le zero_lt_one hBOne)
  have hsquare : (Real.sqrt (B : ℝ)) ^ 2 = (B : ℝ) :=
    Real.sq_sqrt hB0
  calc
    1344 * ((B : ℝ) ^ rho) ^ 8 ≤
        1344 * Real.sqrt (B : ℝ) := by
      exact mul_le_mul_of_nonneg_left hR8 (by norm_num)
    _ < Real.sqrt (B : ℝ) * Real.sqrt (B : ℝ) :=
      mul_lt_mul_of_pos_right hsqrt hsqrtPos
    _ = (B : ℝ) := by nlinarith

/-- The literal quartic cutoff cost is strictly below half of the `B/28`
reserve at every admitted scale. -/
theorem admitted_pairwise_quartic_cost_lt
    (rho : ℝ) (hrho : 0 < rho) (hrhoUpper : rho ≤ (1 : ℝ) / 10000)
    (B : ℕ) (hB : blockThreshold rho ≤ B) :
    24 * (⌊((B : ℝ) ^ rho) ^ 2⌋₊ : ℝ) ^ 4 < (B : ℝ) / 56 := by
  let R : ℝ := (B : ℝ) ^ rho
  have hQ : (⌊R ^ 2⌋₊ : ℝ) ≤ R ^ 2 := Nat.floor_le (sq_nonneg R)
  have hQ4 : (⌊R ^ 2⌋₊ : ℝ) ^ 4 ≤ R ^ 8 := by
    calc
      (⌊R ^ 2⌋₊ : ℝ) ^ 4 ≤ (R ^ 2) ^ 4 := by
        gcongr
      _ = R ^ 8 := by ring
  have hstrong := admitted_scale_eighth_power_budget_1344
    rho hrho hrhoUpper B hB
  have hdiv :
      (1344 * ((B : ℝ) ^ rho) ^ 8) / 56 < (B : ℝ) / 56 :=
    (div_lt_div_iff_of_pos_right (show (0 : ℝ) < 56 by norm_num)).2 hstrong
  have h24R : 24 * R ^ 8 < (B : ℝ) / 56 := by
    convert hdiv using 1
    all_goals dsimp [R]
    all_goals ring
  exact (mul_le_mul_of_nonneg_left hQ4 (by norm_num)).trans_lt h24R

/-- Substantive canonical endpoint: the actual adjusted convolution differs
from its variable arithmetic mean by less than `B/56`. -/
theorem canonicalAdjustedModelAt_sub_variableMean_norm_lt_half_reserve
    (B N : ℕ) (rho b : ℝ)
    (e : CharacterSlot ⌊((B : ℝ) ^ rho) ^ 2⌋₊)
    (hInv : e.2.val⁻¹ = e.2.val)
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (hB2 : 2 ≤ B) (hBN : B ≤ N)
    (hInterval : blockPairLower B N ≤ blockPairUpper B N)
    (hrho : 0 < rho) (hrhoUpper : rho ≤ (1 : ℝ) / 10000)
    (hScale : blockThreshold rho ≤ B) :
    let A := blockPairLower B N
    let T := blockPairUpper B N - blockPairLower B N + 1
    ‖canonicalAdjustedModelAt B rho b e (N : ℤ) -
        powerPairwiseVariableMean
          (log_cutoff_contains_one ((B : ℝ) ^ rho)
            (one_lt_power_of_admitted rho hrho hrhoUpper B hScale))
          e.1 e.2
          (logWeight ((B : ℝ) ^ rho) canonicalLogBump)
          (logWeight ((B : ℝ) ^ rho) canonicalLogBump)
          b N A T‖ < (B : ℝ) / 56 := by
  dsimp only
  have hR := one_lt_power_of_admitted rho hrho hrhoUpper B hScale
  have hbound := canonicalAdjustedModelAt_abel_centered_norm_le
    B N rho b e hInv hb0 hb1 hB2 hBN hInterval hR 1 (by norm_num)
    (canonical_logWeight_norm_le_one ((B : ℝ) ^ rho))
  have hbound' :
      ‖canonicalAdjustedModelAt B rho b e (N : ℤ) -
          powerPairwiseVariableMean
            (log_cutoff_contains_one ((B : ℝ) ^ rho) hR)
            e.1 e.2
            (logWeight ((B : ℝ) ^ rho) canonicalLogBump)
            (logWeight ((B : ℝ) ^ rho) canonicalLogBump)
            b N (blockPairLower B N)
              (blockPairUpper B N - blockPairLower B N + 1)‖ ≤
        24 * (⌊((B : ℝ) ^ rho) ^ 2⌋₊ : ℝ) ^ 4 := by
    simpa only [one_pow, mul_one] using hbound
  exact hbound'.trans_lt
    (admitted_pairwise_quartic_cost_lt rho hrho hrhoUpper B hScale)

end GoldbachCircleMethodAdmittedCanonicalAbelAbsorptionV18333
