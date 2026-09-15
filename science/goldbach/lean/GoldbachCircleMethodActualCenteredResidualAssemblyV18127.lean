import GoldbachCircleMethodExactPrincipalBoundaryCostV18126

set_option autoImplicit false
open scoped BigOperators Classical
open GoldbachCircleMethodFiniteCompanionBindingV18118
open GoldbachCircleMethodFiniteWindowConvolutionV18119
open GoldbachCircleMethodLogCutoffPresieveBindingV18120
open GoldbachCircleMethodPrincipalWindowBoundaryV18121
open GoldbachCircleMethodActualDiscrepancyScaleAbsorptionV18125
open GoldbachCircleMethodExactPrincipalBoundaryCostV18126

namespace GoldbachCircleMethodActualCenteredResidualAssemblyV18127

/-- Subtracts the ACTUAL principal companion and the ACTUAL centered operator. -/
noncomputable def actualCenteredResidual (B N : ℕ) (R : ℝ) (hR : 1 < R)
    (G : ℝ → ℝ) : ℂ :=
  normalizedWindowConvolution ⌊R^2⌋₊ N ((B : ℝ)/R^4)
    (blockCarrier B) (blockInput B) (logWeight R G) -
  finiteCompanion (oneLevel (log_cutoff_contains_one R hR)) N (logWeight R G) -
  centeredWindowError ⌊R^2⌋₊ N ((B : ℝ)/R^4)
    (blockCarrier B) (blockInput B) (logWeight R G)

/-- Algebraic identity binds both error terms; no averaging hypothesis is inserted. -/
theorem actual_centered_residual_eq (B N : ℕ) (R : ℝ) (hR : 1 < R)
    (G : ℝ → ℝ) :
    actualCenteredResidual B N R hR G =
      actualPrincipalBoundary B N R hR G + actualDiscrepancy B N R G := by
  unfold actualCenteredResidual actualPrincipalBoundary principalBoundary actualDiscrepancy
  rw [character_window_model_boundary_decomposition ⌊R^2⌋₊ N
    (log_cutoff_contains_one R hR) ((B : ℝ)/R^4)
    (blockCarrier B) (blockInput B) (logWeight R G)]
  ring

theorem actual_centered_residual_mass_le (B : ℕ) (hB : 2 ≤ B)
    (R : ℝ) (hR : 1 < R) (G : ℝ → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hG : ∀ x : ℝ, |G x| ≤ M)
    (hupper : R ≤ (B : ℝ)^((1 : ℝ)/10000)) :
    (∑ N ∈ blockCarrier B, ‖actualCenteredResidual B N R hR G‖) ≤
      (9/2)*M*(B : ℝ)/R := by
  calc
    _ ≤ ∑ N ∈ blockCarrier B,
        (‖actualPrincipalBoundary B N R hR G‖ + ‖actualDiscrepancy B N R G‖) := by
      apply Finset.sum_le_sum
      intro N _
      rw [actual_centered_residual_eq]
      exact norm_add_le _ _
    _ = _ + _ := Finset.sum_add_distrib
    _ ≤ (5/2)*M*(B : ℝ)/R + 2*M*(B : ℝ)/R :=
      add_le_add (actual_principal_boundary_mass_le_existing_range B hB R hR G M hM hG hupper)
        (actual_discrepancy_mass_le_existing_range B hB R hR G M hM hG hupper)
    _ = _ := by ring

noncomputable def actualCenteredResidualFourier (B : ℕ) (R : ℝ) (hR : 1 < R)
    (G : ℝ → ℝ) (x : UnitAddCircle) : ℂ :=
  ∑ N ∈ blockCarrier B, actualCenteredResidual B N R hR G * fourier (N : ℤ) x

theorem centered_residual_fourier_norm_le_mass (B : ℕ) (R : ℝ) (hR : 1 < R)
    (G : ℝ → ℝ) (x : UnitAddCircle) :
    ‖actualCenteredResidualFourier B R hR G x‖ ≤
      ∑ N ∈ blockCarrier B, ‖actualCenteredResidual B N R hR G‖ := by
  unfold actualCenteredResidualFourier
  calc
    _ ≤ ∑ N ∈ blockCarrier B, ‖actualCenteredResidual B N R hR G *
        fourier (N : ℤ) x‖ := norm_sum_le _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro N _
      simp [fourier_apply, Circle.norm_coe]

theorem centered_residual_fourier_bound (B : ℕ) (hB : 2 ≤ B)
    (R : ℝ) (hR : 1 < R) (G : ℝ → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hG : ∀ x : ℝ, |G x| ≤ M)
    (hupper : R ≤ (B : ℝ)^((1 : ℝ)/10000)) (x : UnitAddCircle) :
    ‖actualCenteredResidualFourier B R hR G x‖ ≤ (9/2)*M*(B : ℝ)/R :=
  (centered_residual_fourier_norm_le_mass B R hR G x).trans
    (actual_centered_residual_mass_le B hB R hR G M hM hG hupper)

theorem centered_residual_fourier_fits_target_budget (B : ℕ) (hB : 2 ≤ B)
    (R : ℝ) (hR : 1 < R) (G : ℝ → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hG : ∀ x : ℝ, |G x| ≤ M)
    (hupper : R ≤ (B : ℝ)^((1 : ℝ)/10000)) (x : UnitAddCircle) :
    ‖actualCenteredResidualFourier B R hR G x‖ ≤
      (9/2)*M*(B : ℝ)*R^(-(1 : ℝ)/3) := by
  apply (centered_residual_fourier_bound B hB R hR G M hM hG hupper x).trans
  rw [div_eq_mul_inv, ← Real.rpow_neg_one]
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hR.le (by norm_num)) (by positivity)

/-- Finite operator assembly; E is still explicitly present and unestimated. -/
theorem actual_window_fourier_model_identity (B : ℕ) (R : ℝ) (hR : 1 < R)
    (G : ℝ → ℝ) (x : UnitAddCircle) :
    (∑ N ∈ blockCarrier B,
      normalizedWindowConvolution ⌊R^2⌋₊ N ((B : ℝ)/R^4)
        (blockCarrier B) (blockInput B) (logWeight R G) * fourier (N : ℤ) x) =
    (∑ N ∈ blockCarrier B,
      finiteCompanion (oneLevel (log_cutoff_contains_one R hR)) N (logWeight R G) *
        fourier (N : ℤ) x) +
    (∑ N ∈ blockCarrier B,
      centeredWindowError ⌊R^2⌋₊ N ((B : ℝ)/R^4)
        (blockCarrier B) (blockInput B) (logWeight R G) * fourier (N : ℤ) x) +
    actualCenteredResidualFourier B R hR G x := by
  unfold actualCenteredResidualFourier actualCenteredResidual
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro N _
  ring

end GoldbachCircleMethodActualCenteredResidualAssemblyV18127

