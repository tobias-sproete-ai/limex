import GoldbachCircleMethodAdmittedRhoPrincipalBudgetV18235

/-!
# Goldbach V1.8.236: quantitative admitted principal reserve

V1.8.235 proves positivity after the finite-interval remainder is absorbed.
This module retains an explicit linear fraction of the source scale.  That
quantitative margin is required before any Chebyshev or exceptional-set
transfer can be honest.
-/

set_option autoImplicit false

namespace GoldbachCircleMethodQuantitativeAdmittedPrincipalReserveV18236

open GoldbachCircleMethodAdmittedRhoPrincipalBudgetV18235
open GoldbachCircleMethodResidualScaleAdmissionV18196
open GoldbachCircleMethodPrincipalRemainderExponentAbsorptionV18234
open GoldbachCircleMethodTwoSourceScalePrincipalReserveV18233
open GoldbachCircleMethodTwoSourceScaleCoverV18232
open GoldbachCircleMethodTwoScaleEvenBlockDefectReserveV1833
open GoldbachCircleMethodActualResidualExactDecompositionV18225
open GoldbachCircleMethodFiniteResiduePrefixV1866
open GoldbachCircleMethodBoundedConductorReindexV18117

/-- The existing admitted corridor also absorbs the finite-interval cost with
the stronger constant needed to retain half of the coarse linear reserve. -/
theorem admitted_scale_two_fifty_six_eighth_power_budget
    (rho : ℝ) (hrho : 0 < rho) (hrhoUpper : rho ≤ (1 : ℝ) / 10000)
    (B : ℕ) (hB : blockThreshold rho ≤ B) :
    256 * ((B : ℝ) ^ rho) ^ 8 < (B : ℝ) := by
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
  have h65536Exp : (65536 : ℝ) < Real.exp (100000000 : ℝ) := by
    have h := Real.add_one_lt_exp (show (100000000 : ℝ) ≠ 0 by norm_num)
    linarith
  have hBbig : (65536 : ℝ) < (B : ℝ) :=
    h65536Exp.trans_le (hExpLarge.trans hExpThreshold)
  have hsqrt : (256 : ℝ) < Real.sqrt (B : ℝ) := by
    rw [Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 256)]
    have h256sq : (256 : ℝ) ^ 2 = 65536 := by norm_num
    rw [h256sq]
    exact hBbig
  have hsqrtPos : 0 < Real.sqrt (B : ℝ) :=
    Real.sqrt_pos.2 (lt_of_lt_of_le zero_lt_one hBOne)
  calc
    256 * ((B : ℝ) ^ rho) ^ 8 ≤ 256 * Real.sqrt (B : ℝ) := by
      exact mul_le_mul_of_nonneg_left hR8 (by norm_num)
    _ < Real.sqrt (B : ℝ) * Real.sqrt (B : ℝ) :=
      mul_lt_mul_of_pos_right hsqrt hsqrtPos
    _ = (B : ℝ) := by rw [Real.mul_self_sqrt hB0]

/-- Under the stronger explicit budget, the concrete supported-model floor
retains more than `B/128`, not merely a positive epsilon. -/
theorem sourceScaleFloor_gt_one_twenty_eighth
    (B : ℕ) (rho : ℝ) (hB : 16 ≤ B)
    (hScale : 256 * ((B : ℝ) ^ rho) ^ 8 < (B : ℝ)) :
    (B : ℝ) / 128 < sourceScaleFloor B rho := by
  let t : ℕ := linearPairReserve B
  let Q : ℕ := ⌊((B : ℝ) ^ rho) ^ 2⌋₊
  have hQ8 : (Q : ℝ) ^ 4 ≤ ((B : ℝ) ^ rho) ^ 8 :=
    floor_cutoff_quartic_le_rpow_eighth B rho
  have hcost : 2 * (Q : ℝ) ^ 4 < (B : ℝ) / 128 := by
    nlinarith
  have ht : (B : ℝ) / 16 ≤ (t : ℝ) :=
    cast_linearPairReserve_ge_sixteenth B hB
  have htPos : 0 < (t : ℝ) := by
    have : (0 : ℝ) < (B : ℝ) / 16 := by positivity
    linarith
  have hkappa := one_fourth_lt_two_sub_exp_pi_sq_div_twentyFour
  have hreserve : (B : ℝ) / 64 <
      (t : ℝ) * (2 - Real.exp (Real.pi ^ 2 / 24)) := by
    calc
      (B : ℝ) / 64 = ((B : ℝ) / 16) * ((1 : ℝ) / 4) := by ring
      _ ≤ (t : ℝ) * ((1 : ℝ) / 4) := by
        exact mul_le_mul_of_nonneg_right ht (by norm_num)
      _ < (t : ℝ) * (2 - Real.exp (Real.pi ^ 2 / 24)) :=
        mul_lt_mul_of_pos_left hkappa htPos
  unfold sourceScaleFloor
  change (B : ℝ) / 128 <
    (t : ℝ) * (2 - Real.exp (Real.pi ^ 2 / 24)) - 2 * (Q : ℝ) ^ 4
  linarith

/-- The quantitative floor is automatic at every scale admitted by V1.8.196. -/
theorem sourceScaleFloor_gt_one_twenty_eighth_of_admitted_scale
    (rho : ℝ) (hrho : 0 < rho) (hrhoUpper : rho ≤ (1 : ℝ) / 10000)
    (B : ℕ) (hB : blockThreshold rho ≤ B) :
    (B : ℝ) / 128 < sourceScaleFloor B rho := by
  have hBbig : (65536 : ℝ) < (B : ℝ) := by
    have hThresholdLarge :=
      logThreshold_ge_one_hundred_million rho hrho hrhoUpper
    have hExpThreshold : Real.exp (logThreshold rho) ≤ (B : ℝ) :=
      (Nat.le_ceil _).trans (by exact_mod_cast hB)
    have hExpLarge : Real.exp (100000000 : ℝ) ≤
        Real.exp (logThreshold rho) := Real.exp_le_exp.mpr hThresholdLarge
    have h := Real.add_one_lt_exp (show (100000000 : ℝ) ≠ 0 by norm_num)
    linarith
  apply sourceScaleFloor_gt_one_twenty_eighth B rho
  · exact_mod_cast (show (16 : ℝ) ≤ B by linarith)
  · exact admitted_scale_two_fifty_six_eighth_power_budget
      rho hrho hrhoUpper B hB

/-- Each of the two covering source scales is at least one quarter of the
dyadic target scale once `M >= 16`. -/
theorem target_scale_quarter_le_source_scales
    (M : ℕ) (hM : 16 ≤ M) :
    M ≤ 4 * lowerSourceScale M ∧ M ≤ 4 * upperSourceScale M := by
  simp only [lowerSourceScale, upperSourceScale]
  omega

/-- Final quantitative cover: every target in the historical dyadic block has
an actual supported principal model larger than `M/512` at one admitted
source scale.  This is a model reserve only; source errors are not controlled
here. -/
theorem evenTargetBlock_principal_gt_target_scale_over_five_twelve
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
    (M : ℝ) / 512 < (canonicalPrincipalModelAt
          (lowerSourceScale M) rho (N : ℤ)).re ∨
      (M : ℝ) / 512 < (canonicalPrincipalModelAt
          (upperSourceScale M) rho (N : ℤ)).re := by
  have hQuarter := target_scale_quarter_le_source_scales M (by omega)
  have hLowCast : (M : ℝ) / 512 ≤ (lowerSourceScale M : ℝ) / 128 := by
    have hReal : (M : ℝ) ≤ 4 * (lowerSourceScale M : ℝ) := by
      exact_mod_cast hQuarter.1
    linarith
  have hHighCast : (M : ℝ) / 512 ≤ (upperSourceScale M : ℝ) / 128 := by
    have hReal : (M : ℝ) ≤ 4 * (upperSourceScale M : ℝ) := by
      exact_mod_cast hQuarter.2
    linarith
  have hLowFloor := sourceScaleFloor_gt_one_twenty_eighth_of_admitted_scale
    rho hrho hrhoUpper (lowerSourceScale M) hLow
  have hHighFloor := sourceScaleFloor_gt_one_twenty_eighth_of_admitted_scale
    rho hrho hrhoUpper (upperSourceScale M) hHigh
  rcases evenTargetBlock_principal_floor_at_one_source_scale
      (K := K) M N rho (by omega) hN
      (one_lt_power_of_admitted rho hrho hrhoUpper (lowerSourceScale M) hLow)
      (one_lt_power_of_admitted rho hrho hrhoUpper (upperSourceScale M) hHigh)
      hKLow hKHigh with hAtLow | hAtHigh
  · exact Or.inl (hLowCast.trans_lt (hLowFloor.trans_le hAtLow))
  · exact Or.inr (hHighCast.trans_lt (hHighFloor.trans_le hAtHigh))

end GoldbachCircleMethodQuantitativeAdmittedPrincipalReserveV18236
