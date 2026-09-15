import GoldbachCircleMethodCenteredPrincipalDecayInterfaceV18503

/-!
# Goldbach V1.8.504: centered-principal net exponent

The canonical conductor cutoff is inserted into the V1.8.503 principal
channel estimate.  This module records the exact exponent price: the squared
coefficient atom costs `4*rho`, hence source decay `sigma > 2*rho` leaves a
strictly negative net energy exponent.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodCenteredPrincipalNetExponentV18504

open GoldbachCircleMethodCenteredPrincipalDecayInterfaceV18503
open GoldbachCircleMethodHybridCenteredCorrelationEnergyV18501
open GoldbachCircleMethodLogCutoffPresieveBindingV18120
open GoldbachCircleMethodPrincipalWindowBoundaryV18121
open GoldbachCircleMethodCanonicalBumpPrincipalFloorV18220

noncomputable def centeredPrincipalCutoff (B : ℕ) (rho : ℝ) : ℕ :=
  ⌊((B : ℝ) ^ rho) ^ 2⌋₊

theorem centeredPrincipalCutoff_pos
    (B : ℕ) (hB : 3 ≤ B) (rho : ℝ) (hrho : 0 < rho) :
    1 ≤ centeredPrincipalCutoff B rho := by
  have hbase : (1 : ℝ) < (B : ℝ) := by exact_mod_cast (show 1 < B by omega)
  have hR : 1 < (B : ℝ) ^ rho := Real.one_lt_rpow hbase hrho
  exact log_cutoff_contains_one ((B : ℝ) ^ rho) hR

/-- Exact canonical cutoff cost, with no ceiling constant. -/
theorem centeredPrincipalCutoff_sq_le_rpow
    (B : ℕ) (hB : 1 ≤ B) (rho : ℝ) :
    (centeredPrincipalCutoff B rho : ℝ) ^ 2 ≤
      (B : ℝ) ^ (4 * rho) := by
  let R : ℝ := (B : ℝ) ^ rho
  let Q : ℕ := ⌊R ^ 2⌋₊
  have hB0 : (0 : ℝ) ≤ B := by positivity
  have hR0 : 0 ≤ R := by dsimp [R]; positivity
  have hQ : (Q : ℝ) ≤ R ^ 2 := Nat.floor_le (sq_nonneg R)
  have hQ0 : 0 ≤ (Q : ℝ) := Nat.cast_nonneg Q
  change (Q : ℝ) ^ 2 ≤ (B : ℝ) ^ (4 * rho)
  calc
    (Q : ℝ) ^ 2 ≤ (R ^ 2) ^ 2 := pow_le_pow_left₀ hQ0 hQ 2
    _ = R ^ 4 := by ring
    _ = (B : ℝ) ^ (4 * rho) := by
      dsimp [R]
      rw [← Real.rpow_mul_natCast hB0]
      congr 1
      norm_num
      ring

/-- The repaired principal channel at the canonical cutoff has the explicit
net exponent `4*rho - 2*sigma`. -/
theorem canonical_centeredPrincipalCorrelation_sq_le_net_power
    (C rho sigma : ℝ) (hC : 0 ≤ C) (hrho : 0 < rho)
    (hestimate : CenteredPrincipalDiscrepancyEstimate C rho sigma)
    (B N : ℕ) (hB : 3 ≤ B) (hN : N ∈ blockCarrier B) :
    ‖centeredPrincipalCorrelation (centeredPrincipalCutoff B rho) B N
        (centeredPrincipalScale B rho)
        (logWeight ((B : ℝ) ^ rho) canonicalLogBump)‖ ^ 2 ≤
      C ^ 2 * (B : ℝ) ^ (4 * rho - 2 * sigma) := by
  let Q := centeredPrincipalCutoff B rho
  have hQ : 1 ≤ Q := centeredPrincipalCutoff_pos B hB rho hrho
  have hraw := centeredPrincipalCorrelation_sq_le_of_discrepancy_estimate
    C rho sigma hC hestimate Q B N hQ hB hN
  have hcut : (Q : ℝ) ^ 2 ≤ (B : ℝ) ^ (4 * rho) :=
    centeredPrincipalCutoff_sq_le_rpow B (by omega) rho
  have hBpos : (0 : ℝ) < B := by exact_mod_cast (show 0 < B by omega)
  have hnegativePower : (B : ℝ) ^ (-2 * sigma) =
      ((B : ℝ) ^ (-sigma)) ^ 2 := by
    rw [show -2 * sigma = -sigma * (2 : ℝ) by ring,
      Real.rpow_mul hBpos.le, Real.rpow_two]
  calc
    ‖centeredPrincipalCorrelation Q B N
        (centeredPrincipalScale B rho)
        (logWeight ((B : ℝ) ^ rho) canonicalLogBump)‖ ^ 2 ≤
      (Q : ℝ) ^ 2 * (C * (B : ℝ) ^ (-sigma)) ^ 2 := hraw
    _ ≤ (B : ℝ) ^ (4 * rho) *
        (C * (B : ℝ) ^ (-sigma)) ^ 2 :=
      mul_le_mul_of_nonneg_right hcut (sq_nonneg _)
    _ = C ^ 2 * ((B : ℝ) ^ (4 * rho) *
        (B : ℝ) ^ (-2 * sigma)) := by
      rw [hnegativePower]
      ring
    _ = C ^ 2 * (B : ℝ) ^ (4 * rho + (-2 * sigma)) := by
      rw [Real.rpow_add hBpos]
    _ = C ^ 2 * (B : ℝ) ^ (4 * rho - 2 * sigma) := by
      congr 2
      ring

/-- The exact threshold for a negative principal energy exponent. -/
theorem centeredPrincipalNetExponent_neg
    (rho sigma : ℝ) (hdecay : 2 * rho < sigma) :
    4 * rho - 2 * sigma < 0 := by
  linarith

end GoldbachCircleMethodCenteredPrincipalNetExponentV18504
