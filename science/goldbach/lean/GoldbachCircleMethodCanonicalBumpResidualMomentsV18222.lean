import GoldbachCircleMethodPositivePrincipalDiagonalV18221
import GoldbachCircleMethodActualResidualMomentCompositionV18193

/-!
# V1.8.222: canonical-bump specialization of actual residual moments

The explicit V1.8.220 weight is now threaded through the already checked
V1.8.193 principal and active residual-moment theorems.  This removes every
generic bump regularity, support, size, and plateau premise.  The external
`RealVaughanEstimate` and the scale hypotheses remain explicit.

These are averaged `L²` bounds.  No pointwise residual sign is inferred.
-/

set_option autoImplicit false

open scoped BigOperators Classical ContDiff

namespace GoldbachCircleMethodCanonicalBumpResidualMomentsV18222

open GoldbachCircleMethodLogCutoffPresieveBindingV18120
open GoldbachCircleMethodActiveExceptionalCenteringV18129
open GoldbachCircleMethodActualInputModelResidualV18138
open GoldbachCircleMethodUncorrectedSupportedErrorConvolutionV18184
open GoldbachCircleMethodSupportedResidualParsevalV18190
open GoldbachCircleMethodSupportedModelErrorConvolutionV18182
open GoldbachCircleMethodRealApproximationMinorAdapterV1873
open GoldbachCircleMethodActualResidualMomentCompositionV18193
open GoldbachCircleMethodCanonicalBumpPrincipalFloorV18220

theorem canonicalLogBump_le_one (x : ℝ) :
    canonicalLogBump x ≤ 1 := by
  unfold canonicalLogBump
  exact mul_le_one₀ (Real.smoothTransition.le_one _)
    (Real.smoothTransition.nonneg _) (Real.smoothTransition.le_one _)

theorem abs_canonicalLogBump_le_one (x : ℝ) :
    |canonicalLogBump x| ≤ 1 := by
  rw [abs_of_nonneg (canonicalLogBump_nonneg x)]
  exact canonicalLogBump_le_one x

theorem canonicalLogBump_plateau {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    canonicalLogBump x = 1 := by
  rw [canonicalLogBump]
  rw [Real.smoothTransition.one_of_one_le (by linarith)]
  rw [Real.smoothTransition.one_of_one_le (by linarith)]
  norm_num

theorem canonicalLogBump_zero_above_two {x : ℝ} (hx : 2 < x) :
    canonicalLogBump x = 0 := by
  apply canonicalLogBump_zero_outside_Icc
  intro hmem
  exact (not_le_of_gt hx) hmem.2

/-- V1.8.193 principal residual moment for the one fixed admissible bump.
The only non-elementary input left in the interface is the displayed real
Vaughan estimate. -/
theorem canonical_principal_residual_moment_power_bound
    (C rho : ℝ) (hC : 0 ≤ C) (hV : RealVaughanEstimate C)
    (hrho : 0 < rho) :
    ∃ Crho : ℝ, 0 ≤ Crho ∧ ∀ (B : ℕ) (_hB : 6 ≤ B),
      ∀ (_hR2 : 2 ≤ (B : ℝ)^rho),
      Real.exp (Real.sqrt (Real.log (B : ℝ))) ≤ (B : ℝ)^rho →
      (B : ℝ)^rho ≤ (B : ℝ)^((1 : ℝ) / 10000) →
      (∑ k ∈ Finset.Icc (0 : ℤ) (2 * B : ℕ),
        ‖integerPairConvolution (blockCarrier B)
          (fun N => inputPrincipalResidual B N ((B : ℝ)^rho) (by linarith)
            canonicalLogBump)
          (fun N => blockInput B N +
            supportedPrincipalModel B N ((B : ℝ)^rho) canonicalLogBump) k‖^2) ≤
        Crho * (B : ℝ)^3 * ((B : ℝ)^rho)^(-(5 : ℝ) / 8) *
          (Real.log (B : ℝ))^2 := by
  exact actual_principal_residual_moment_power_bound
    canonicalLogBump_hasCompactSupport canonicalLogBump_contDiff
    (fun _ hx => canonicalLogBump_zero_above_two hx)
    C 1 rho hC hV (by norm_num)
    abs_canonicalLogBump_le_one
    (fun _ hx0 hx1 => canonicalLogBump_plateau hx0 hx1) hrho

/-- V1.8.193 active residual moment for the same fixed bump.  Uniformity in
the retained `b` and character slot is unchanged. -/
theorem canonical_active_residual_moment_power_bound
    (C rho : ℝ) (hC : 0 ≤ C) (hV : RealVaughanEstimate C)
    (hrho : 0 < rho) :
    ∃ Crho : ℝ, 0 ≤ Crho ∧ ∀ (B : ℕ) (_hB : 6 ≤ B),
      ∀ (_hR2 : 2 ≤ (B : ℝ)^rho),
      Real.exp (Real.sqrt (Real.log (B : ℝ))) ≤ (B : ℝ)^rho →
      (B : ℝ)^rho ≤ (B : ℝ)^((1 : ℝ) / 10000) →
      ∀ b : ℝ, 0 ≤ b → b ≤ 1 →
      ∀ e : CharacterSlot ⌊((B : ℝ)^rho)^2⌋₊,
      (∑ k ∈ Finset.Icc (0 : ℤ) (2 * B : ℕ),
        ‖integerPairConvolution (blockCarrier B)
          (fun N => inputActiveResidual B N ((B : ℝ)^rho) (by linarith)
            b canonicalLogBump e)
          (fun N => blockInput B N +
            supportedAdjustedModel B N ((B : ℝ)^rho) b canonicalLogBump e) k‖^2) ≤
        Crho * (B : ℝ)^3 * ((B : ℝ)^rho)^(-(5 : ℝ) / 8) *
          (Real.log (B : ℝ))^2 := by
  exact actual_active_residual_moment_power_bound
    canonicalLogBump_hasCompactSupport canonicalLogBump_contDiff
    (fun _ hx => canonicalLogBump_zero_above_two hx)
    C 1 rho hC hV (by norm_num)
    abs_canonicalLogBump_le_one
    (fun _ hx0 hx1 => canonicalLogBump_plateau hx0 hx1) hrho

end GoldbachCircleMethodCanonicalBumpResidualMomentsV18222
