import GoldbachCircleMethodHybridCenteredChannelBudgetSplitV18510

/-!
# Goldbach V1.8.511: hybrid principal block exponent

The exact cutoff and target-cardinality costs are combined.  Under the
explicit centered-principal discrepancy estimate, the full principal block
has exponent `1 + 4*rho - 2*sigma`.  This closes only the principal channel.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodHybridPrincipalBlockExponentV18511

open GoldbachCircleMethodCenteredPrincipalDecayInterfaceV18503
open GoldbachCircleMethodCenteredPrincipalNetExponentV18504
open GoldbachCircleMethodHybridCenteredChannelBudgetSplitV18510

/-- The repaired principal block obeys its exact net power law. -/
theorem hybridPrincipalBlockBudget_le_net_power
    (C rho sigma : ℝ) (hC : 0 ≤ C) (hrho : 0 < rho)
    (hestimate : CenteredPrincipalDiscrepancyEstimate C rho sigma)
    (B : ℕ) (hB : 3 ≤ B) :
    hybridPrincipalBlockBudget B rho ≤
      C ^ 2 * (B : ℝ) ^ (1 + 4 * rho - 2 * sigma) := by
  have hraw := hybridPrincipalBlockBudget_le_explicit
    C rho sigma hC hrho hestimate B hB
  have hcut : (centeredPrincipalCutoff B rho : ℝ) ^ 2 ≤
      (B : ℝ) ^ (4 * rho) :=
    centeredPrincipalCutoff_sq_le_rpow B (by omega) rho
  have hBpos : (0 : ℝ) < B := by exact_mod_cast (show 0 < B by omega)
  have hnegativePower : (B : ℝ) ^ (-2 * sigma) =
      ((B : ℝ) ^ (-sigma)) ^ 2 := by
    rw [show -2 * sigma = -sigma * (2 : ℝ) by ring,
      Real.rpow_mul hBpos.le, Real.rpow_two]
  have hfirstCombine : (B : ℝ) * (B : ℝ) ^ (4 * rho) =
      (B : ℝ) ^ (1 + 4 * rho) := by
    calc
      (B : ℝ) * (B : ℝ) ^ (4 * rho) =
          (B : ℝ) ^ 1 * (B : ℝ) ^ (4 * rho) := by
        exact congrArg (fun x : ℝ => x * (B : ℝ) ^ (4 * rho))
          (Real.rpow_one (B : ℝ)).symm
      _ = (B : ℝ) ^ (1 + 4 * rho) :=
        (Real.rpow_add hBpos 1 (4 * rho)).symm
  have hcombine : (B : ℝ) *
      ((B : ℝ) ^ (4 * rho) * (B : ℝ) ^ (-2 * sigma)) =
      (B : ℝ) ^ (1 + 4 * rho - 2 * sigma) := by
    calc
      (B : ℝ) * ((B : ℝ) ^ (4 * rho) * (B : ℝ) ^ (-2 * sigma)) =
          ((B : ℝ) * (B : ℝ) ^ (4 * rho)) *
            (B : ℝ) ^ (-2 * sigma) := by ring
      _ = (B : ℝ) ^ (1 + 4 * rho) *
            (B : ℝ) ^ (-2 * sigma) := by rw [hfirstCombine]
      _ = (B : ℝ) ^ ((1 + 4 * rho) + (-2 * sigma)) :=
        (Real.rpow_add hBpos (1 + 4 * rho) (-2 * sigma)).symm
      _ = (B : ℝ) ^ (1 + 4 * rho - 2 * sigma) := by
        congr 1
        ring
  calc
    hybridPrincipalBlockBudget B rho ≤
      (B : ℝ) *
        ((centeredPrincipalCutoff B rho : ℝ) ^ 2 *
          (C * (B : ℝ) ^ (-sigma)) ^ 2) := hraw
    _ ≤ (B : ℝ) *
        ((B : ℝ) ^ (4 * rho) *
          (C * (B : ℝ) ^ (-sigma)) ^ 2) := by
      gcongr
    _ = C ^ 2 * ((B : ℝ) *
        ((B : ℝ) ^ (4 * rho) * (B : ℝ) ^ (-2 * sigma))) := by
      rw [hnegativePower]
      ring
    _ = C ^ 2 * (B : ℝ) ^ (1 + 4 * rho - 2 * sigma) := by
      rw [hcombine]

/-- Exact principal-channel margin required by the already verified actual
partner exponent. -/
theorem hybridPrincipalSourceGap
    (rho sigma eps eta : ℝ)
    (hmargin : 2 * rho + eps + eta < sigma) :
    (1 + 4 * rho - 2 * sigma) + 2 * (eps + eta) < 1 := by
  linarith

end GoldbachCircleMethodHybridPrincipalBlockExponentV18511
