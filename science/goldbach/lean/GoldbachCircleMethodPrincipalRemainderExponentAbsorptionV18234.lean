import GoldbachCircleMethodTwoSourceScalePrincipalReserveV18233

/-!
# Goldbach V1.8.234: principal remainder exponent absorption

This module turns the explicit V1.8.233 floor into a transparent scale test.
The finite denominator cutoff contributes at most the eighth power of the
real cutoff.  A coarse certified rational lower bound for the principal
constant then lets the one-eighth pair reserve absorb the quartic remainder.

No asymptotic scale admission theorem is claimed here; the remaining premise
`128 * R^8 < B` is displayed verbatim.
-/

set_option autoImplicit false

namespace GoldbachCircleMethodPrincipalRemainderExponentAbsorptionV18234

open GoldbachCircleMethodPositivePrincipalDiagonalV18221
open GoldbachCircleMethodTwoSourceScaleCoverV18232
open GoldbachCircleMethodTwoSourceScalePrincipalReserveV18233
open GoldbachCircleMethodActualResidualExactDecompositionV18225
open GoldbachCircleMethodFiniteResiduePrefixV1866
open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodTwoScaleEvenBlockDefectReserveV1833

/-- A conservative rational lower bound for the already positive finite
principal constant. -/
theorem one_fourth_lt_two_sub_exp_pi_sq_div_twentyFour :
    (1 : ℝ) / 4 < 2 - Real.exp (Real.pi ^ 2 / 24) := by
  have hpiSq : Real.pi ^ 2 < (3.15 : ℝ) ^ 2 := by
    nlinarith [Real.pi_pos, Real.pi_lt_d2]
  have hx : Real.pi ^ 2 / 24 < (3 : ℝ) / 7 := by
    nlinarith
  have hx0 : 0 ≤ Real.pi ^ 2 / 24 := by positivity
  have hx1 : Real.pi ^ 2 / 24 < 1 := hx.trans (by norm_num)
  have hexp := Real.exp_bound_div_one_sub_of_interval hx0 hx1
  have hfrac :
      1 / (1 - Real.pi ^ 2 / 24) < (7 : ℝ) / 4 := by
    rw [div_lt_iff₀ (by linarith)]
    nlinarith
  linarith

/-- The concrete natural reserve `floor(B/8)` is at least `B/16` once the
source scale is at least sixteen. -/
theorem cast_linearPairReserve_ge_sixteenth
    (B : ℕ) (hB : 16 ≤ B) :
    (B : ℝ) / 16 ≤ (linearPairReserve B : ℝ) := by
  have hNat : B ≤ 16 * (B / 8) := by omega
  have hReal : (B : ℝ) ≤ 16 * (B / 8 : ℕ) := by exact_mod_cast hNat
  simpa only [linearPairReserve] using (show
    (B : ℝ) / 16 ≤ (B / 8 : ℕ) by linarith)

/-- Flooring the squared real cutoff and then taking the fourth power costs at
most the eighth power of the real cutoff. -/
theorem floor_cutoff_quartic_le_rpow_eighth
    (B : ℕ) (rho : ℝ) :
    (⌊((B : ℝ) ^ rho) ^ 2⌋₊ : ℝ) ^ 4 ≤
      ((B : ℝ) ^ rho) ^ 8 := by
  let R : ℝ := (B : ℝ) ^ rho
  let Q : ℕ := ⌊R ^ 2⌋₊
  have hQ : (Q : ℝ) ≤ R ^ 2 := Nat.floor_le (sq_nonneg R)
  have hQ0 : 0 ≤ (Q : ℝ) := Nat.cast_nonneg Q
  change (Q : ℝ) ^ 4 ≤ R ^ 8
  calc
    (Q : ℝ) ^ 4 ≤ (R ^ 2) ^ 4 := pow_le_pow_left₀ hQ0 hQ 4
    _ = R ^ 8 := by ring

/-- The quartic finite-interval cost is strictly absorbed by the concrete
linear reserve under one explicit scale inequality. -/
theorem sourceScaleFloor_pos_of_eighth_power_budget
    (B : ℕ) (rho : ℝ) (hB : 16 ≤ B)
    (hScale : 128 * ((B : ℝ) ^ rho) ^ 8 < (B : ℝ)) :
    0 < sourceScaleFloor B rho := by
  let t : ℕ := linearPairReserve B
  let Q : ℕ := ⌊((B : ℝ) ^ rho) ^ 2⌋₊
  have hQ8 : (Q : ℝ) ^ 4 ≤ ((B : ℝ) ^ rho) ^ 8 :=
    floor_cutoff_quartic_le_rpow_eighth B rho
  have hcost : 2 * (Q : ℝ) ^ 4 < (B : ℝ) / 64 := by
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
  change 0 < (t : ℝ) * (2 - Real.exp (Real.pi ^ 2 / 24)) -
    2 * (Q : ℝ) ^ 4
  linarith

/-- Two explicit eighth-power scale budgets discharge the abstract positivity
premises of V1.8.233 on the complete dyadic target block. -/
theorem evenTargetBlock_principal_positive_of_two_eighth_power_budgets
    {K : ℕ} [NeZero K]
    (M N : ℕ) (rho : ℝ) (hM : 37 ≤ M)
    (hN : N ∈ evenTargetBlock M)
    (hRLow : 1 < (lowerSourceScale M : ℝ) ^ rho)
    (hRHigh : 1 < (upperSourceScale M : ℝ) ^ rho)
    (hKLow : ∀ q : PositiveLevel
        ⌊((lowerSourceScale M : ℝ) ^ rho) ^ 2⌋₊, q.val ∣ K)
    (hKHigh : ∀ q : PositiveLevel
        ⌊((upperSourceScale M : ℝ) ^ rho) ^ 2⌋₊, q.val ∣ K)
    (hScaleLow :
      128 * ((lowerSourceScale M : ℝ) ^ rho) ^ 8 <
        (lowerSourceScale M : ℝ))
    (hScaleHigh :
      128 * ((upperSourceScale M : ℝ) ^ rho) ^ 8 <
        (upperSourceScale M : ℝ)) :
    0 < (canonicalPrincipalModelAt
          (lowerSourceScale M) rho (N : ℤ)).re ∨
      0 < (canonicalPrincipalModelAt
          (upperSourceScale M) rho (N : ℤ)).re := by
  apply evenTargetBlock_principal_positive_at_one_source_scale
    M N rho (by omega) hN hRLow hRHigh hKLow hKHigh
  · exact sourceScaleFloor_pos_of_eighth_power_budget
      (lowerSourceScale M) rho (by simp only [lowerSourceScale]; omega) hScaleLow
  · exact sourceScaleFloor_pos_of_eighth_power_budget
      (upperSourceScale M) rho (by simp only [upperSourceScale]; omega) hScaleHigh

end GoldbachCircleMethodPrincipalRemainderExponentAbsorptionV18234
