import GoldbachCircleMethodPrincipalRemainderExponentAbsorptionV18234
import GoldbachCircleMethodResidualScaleAdmissionV18196

/-!
# Goldbach V1.8.235: admitted rho principal budget

The scale condition left explicit in V1.8.234 is discharged using the existing
V1.8.196 admission contract.  No new threshold convention is introduced.
The threshold remains extremely large and is not presented as computationally
practical or as a finite verification range.
-/

set_option autoImplicit false

namespace GoldbachCircleMethodAdmittedRhoPrincipalBudgetV18235

open GoldbachCircleMethodResidualScaleAdmissionV18196
open GoldbachCircleMethodPrincipalRemainderExponentAbsorptionV18234
open GoldbachCircleMethodTwoSourceScaleCoverV18232
open GoldbachCircleMethodTwoScaleEvenBlockDefectReserveV1833
open GoldbachCircleMethodActualResidualExactDecompositionV18225
open GoldbachCircleMethodFiniteResiduePrefixV1866
open GoldbachCircleMethodBoundedConductorReindexV18117

/-- The existing admitted power-scale corridor is strong enough to imply the
eighth-power budget required by V1.8.234. -/
theorem admitted_scale_eighth_power_budget
    (rho : ℝ) (hrho : 0 < rho) (hrhoUpper : rho ≤ (1 : ℝ) / 10000)
    (B : ℕ) (hB : blockThreshold rho ≤ B) :
    128 * ((B : ℝ) ^ rho) ^ 8 < (B : ℝ) := by
  obtain ⟨hB6, _hR2, _hlower, hupper⟩ :=
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
  have h16384Exp : (16384 : ℝ) < Real.exp (100000000 : ℝ) := by
    have h := Real.add_one_lt_exp (show (100000000 : ℝ) ≠ 0 by norm_num)
    linarith
  have hBbig : (16384 : ℝ) < (B : ℝ) :=
    h16384Exp.trans_le (hExpLarge.trans hExpThreshold)
  have hsqrt : (128 : ℝ) < Real.sqrt (B : ℝ) := by
    rw [Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 128)]
    have h128sq : (128 : ℝ) ^ 2 = 16384 := by norm_num
    rw [h128sq]
    exact hBbig
  have hsqrtPos : 0 < Real.sqrt (B : ℝ) :=
    Real.sqrt_pos.2 (lt_of_lt_of_le zero_lt_one hBOne)
  have hsquare : (Real.sqrt (B : ℝ)) ^ 2 = (B : ℝ) :=
    Real.sq_sqrt hB0
  calc
    128 * ((B : ℝ) ^ rho) ^ 8 ≤ 128 * Real.sqrt (B : ℝ) := by
      exact mul_le_mul_of_nonneg_left hR8 (by norm_num)
    _ < Real.sqrt (B : ℝ) * Real.sqrt (B : ℝ) :=
      mul_lt_mul_of_pos_right hsqrt hsqrtPos
    _ = (B : ℝ) := by nlinarith

/-- The concrete source-scale floor is positive at every scale admitted by the
existing V1.8.196 threshold. -/
theorem sourceScaleFloor_pos_of_admitted_scale
    (rho : ℝ) (hrho : 0 < rho) (hrhoUpper : rho ≤ (1 : ℝ) / 10000)
    (B : ℕ) (hB : blockThreshold rho ≤ B) :
    0 < GoldbachCircleMethodTwoSourceScalePrincipalReserveV18233.sourceScaleFloor
      B rho := by
  have hBbig : (16384 : ℝ) < (B : ℝ) := by
    have hThresholdLarge :=
      logThreshold_ge_one_hundred_million rho hrho hrhoUpper
    have hExpThreshold : Real.exp (logThreshold rho) ≤ (B : ℝ) :=
      (Nat.le_ceil _).trans (by exact_mod_cast hB)
    have hExpLarge : Real.exp (100000000 : ℝ) ≤
        Real.exp (logThreshold rho) := Real.exp_le_exp.mpr hThresholdLarge
    have h := Real.add_one_lt_exp (show (100000000 : ℝ) ≠ 0 by norm_num)
    linarith
  apply sourceScaleFloor_pos_of_eighth_power_budget B rho
  · exact_mod_cast (show (16 : ℝ) ≤ B by linarith)
  · exact admitted_scale_eighth_power_budget rho hrho hrhoUpper B hB

/-- At admitted lower and upper source scales, the actual supported principal
model is positive on one covering scale for every dyadic even target. -/
theorem evenTargetBlock_principal_positive_of_admitted_source_scales
    {K : ℕ} [NeZero K]
    (M N : ℕ) (rho : ℝ) (hM : 37 ≤ M)
    (hN : N ∈ evenTargetBlock M)
    (hrho : 0 < rho) (hrhoUpper : rho ≤ (1 : ℝ) / 10000)
    (hLow : blockThreshold rho ≤ lowerSourceScale M)
    (hHigh : blockThreshold rho ≤ upperSourceScale M)
    (hKLow : ∀ q : PositiveLevel
        ⌊((lowerSourceScale M : ℝ) ^ rho) ^ 2⌋₊, q.val ∣ K)
    (hKHigh : ∀ q : PositiveLevel
        ⌊((upperSourceScale M : ℝ) ^ rho) ^ 2⌋₊, q.val ∣ K) :
    0 < (canonicalPrincipalModelAt
          (lowerSourceScale M) rho (N : ℤ)).re ∨
      0 < (canonicalPrincipalModelAt
          (upperSourceScale M) rho (N : ℤ)).re := by
  apply evenTargetBlock_principal_positive_of_two_eighth_power_budgets (K := K)
    M N rho hM hN
  · exact one_lt_power_of_admitted rho hrho hrhoUpper
      (lowerSourceScale M) hLow
  · exact one_lt_power_of_admitted rho hrho hrhoUpper
      (upperSourceScale M) hHigh
  · exact hKLow
  · exact hKHigh
  · exact admitted_scale_eighth_power_budget rho hrho hrhoUpper
      (lowerSourceScale M) hLow
  · exact admitted_scale_eighth_power_budget rho hrho hrhoUpper
      (upperSourceScale M) hHigh

end GoldbachCircleMethodAdmittedRhoPrincipalBudgetV18235
