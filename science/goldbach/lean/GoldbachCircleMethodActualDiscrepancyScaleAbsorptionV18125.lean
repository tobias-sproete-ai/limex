import GoldbachCircleMethodRemovedCharacterWindowNormV18124

set_option autoImplicit false
open scoped BigOperators Classical
open GoldbachCircleMethodFiniteWindowConvolutionV18119
open GoldbachCircleMethodLogCutoffPresieveBindingV18120
open GoldbachCircleMethodPrincipalWindowBoundaryV18121
open GoldbachCircleMethodRemovedConvolutionNormV18123
open GoldbachCircleMethodRemovedCharacterWindowNormV18124

namespace GoldbachCircleMethodActualDiscrepancyScaleAbsorptionV18125

/-- The original unpresieved discrepancy, not a free error variable. -/
noncomputable def actualDiscrepancy (B N : ℕ) (R : ℝ) (G : ℝ → ℝ) : ℂ :=
  normalizedWindowConvolution ⌊R^2⌋₊ N ((B : ℝ)/R^4)
    (blockCarrier B) (blockInput B) (logWeight R G) -
  characterWindowOperator ⌊R^2⌋₊ N ((B : ℝ)/R^4)
    (blockCarrier B) (blockInput B) (logWeight R G)

/-- Both removed-input costs are combined before any scale absorption. -/
theorem actual_discrepancy_mass_le (B : ℕ) (hB : 2 ≤ B)
    (R : ℝ) (hR : 1 < R) (G : ℝ → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hG : ∀ x : ℝ, |G x| ≤ M) :
    (∑ N ∈ blockCarrier B, ‖actualDiscrepancy B N R G‖) ≤
      M*R^16*Real.log (B : ℝ) := by
  have hlogB : 0 ≤ Real.log (B : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (le_trans (by decide : 1 ≤ 2) hB))
  have hpow : R^10 ≤ R^16 := pow_le_pow_right₀ hR.le (by decide)
  have hc := removed_convolution_mass_le B hB R hR G M hM hG
  have ht := removed_character_window_mass_le B hB R hR G M hM hG
  calc
    _ ≤ ∑ N ∈ blockCarrier B,
        (‖normalizedWindowConvolution ⌊R^2⌋₊ N ((B : ℝ)/R^4)
          (blockCarrier B) (removedInput ⌊R^2⌋₊ B) (logWeight R G)‖ +
         ‖characterWindowOperator ⌊R^2⌋₊ N ((B : ℝ)/R^4)
          (blockCarrier B) (removedInput ⌊R^2⌋₊ B) (logWeight R G)‖) := by
      apply Finset.sum_le_sum
      intro N _
      unfold actualDiscrepancy
      rw [actual_removed_input_discrepancy B N R G]
      exact norm_sub_le _ _
    _ = _ + _ := Finset.sum_add_distrib
    _ ≤ (M/2)*R^10*Real.log (B : ℝ) + (M/2)*R^16*Real.log (B : ℝ) :=
      add_le_add hc ht
    _ ≤ (M/2)*R^16*Real.log (B : ℝ) + (M/2)*R^16*Real.log (B : ℝ) := by
      exact add_le_add (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hpow (by positivity)) hlogB) le_rfl
    _ = _ := by ring

/-- Effective elementary absorption; no unspecified eventual threshold. -/
theorem coarse_scale_absorption (B R : ℝ) (hB : 0 < B) (hR : 0 < R)
    (hscale : R^34 ≤ B) :
    R^16*Real.log B ≤ 2*B/R := by
  have h17 : R^17 ≤ Real.sqrt B := by
    apply (Real.le_sqrt (by positivity) hB.le).mpr
    simpa only [← pow_mul] using hscale
  have hlog : Real.log B ≤ 2*Real.sqrt B := by
    have hh := Real.log_le_rpow_div hB.le (by norm_num : (0 : ℝ) < 1/2)
    rw [← Real.sqrt_eq_rpow] at hh
    linarith
  have hprod : R^17*Real.log B ≤ 2*B := by
    calc
      _ ≤ R^17*(2*Real.sqrt B) :=
        mul_le_mul_of_nonneg_left hlog (by positivity)
      _ ≤ Real.sqrt B*(2*Real.sqrt B) :=
        mul_le_mul_of_nonneg_right h17 (by positivity)
      _ = 2*B := by nlinarith [Real.sq_sqrt hB.le]
  apply (le_div_iff₀ hR).mpr
  calc
    _ = R^17*Real.log B := by ring
    _ ≤ _ := hprod

/-- The pre-existing upper range implies the explicit absorption condition. -/
theorem existing_upper_range_implies_scale (B R : ℝ) (hB : 1 ≤ B)
    (hR : 0 ≤ R) (hupper : R ≤ B^((1 : ℝ)/10000)) :
    R^34 ≤ B := by
  have hB0 : 0 ≤ B := le_trans zero_le_one hB
  calc
    _ ≤ (B^((1 : ℝ)/10000))^34 := pow_le_pow_left₀ hR hupper 34
    _ = B^((34 : ℝ)/10000) := by
      rw [← Real.rpow_mul_natCast hB0]
      congr 1
      norm_num
    _ ≤ B^(1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hB (by norm_num)
    _ = B := Real.rpow_one B

theorem actual_discrepancy_mass_le_under_scale (B : ℕ) (hB : 2 ≤ B)
    (R : ℝ) (hR : 1 < R) (G : ℝ → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hG : ∀ x : ℝ, |G x| ≤ M) (hscale : R^34 ≤ (B : ℝ)) :
    (∑ N ∈ blockCarrier B, ‖actualDiscrepancy B N R G‖) ≤
      2*M*(B : ℝ)/R := by
  apply (actual_discrepancy_mass_le B hB R hR G M hM hG).trans
  have hBpos : (0 : ℝ) < B := by exact_mod_cast (by omega : 0 < B)
  have hs := mul_le_mul_of_nonneg_left
    (coarse_scale_absorption (B : ℝ) R hBpos (lt_trans zero_lt_one hR) hscale) hM
  convert hs using 1 <;> ring

/-- Actual residual estimate in the already specified logarithmic-cutoff range. -/
theorem actual_discrepancy_mass_le_existing_range (B : ℕ) (hB : 2 ≤ B)
    (R : ℝ) (hR : 1 < R) (G : ℝ → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hG : ∀ x : ℝ, |G x| ≤ M)
    (hupper : R ≤ (B : ℝ)^((1 : ℝ)/10000)) :
    (∑ N ∈ blockCarrier B, ‖actualDiscrepancy B N R G‖) ≤
      2*M*(B : ℝ)/R := by
  apply actual_discrepancy_mass_le_under_scale B hB R hR G M hM hG
  exact existing_upper_range_implies_scale (B : ℝ) R
    (by exact_mod_cast (by omega : 1 ≤ B))
    (le_of_lt (lt_trans zero_lt_one hR)) hupper


/-- Fourier polynomial of the ACTUAL discrepancy restricted to the output block. -/
noncomputable def actualDiscrepancyFourier (B : ℕ) (R : ℝ) (G : ℝ → ℝ)
    (x : UnitAddCircle) : ℂ :=
  ∑ N ∈ blockCarrier B, actualDiscrepancy B N R G * fourier (N : ℤ) x

theorem discrepancy_fourier_norm_le_mass (B : ℕ) (R : ℝ) (G : ℝ → ℝ)
    (x : UnitAddCircle) :
    ‖actualDiscrepancyFourier B R G x‖ ≤
      ∑ N ∈ blockCarrier B, ‖actualDiscrepancy B N R G‖ := by
  unfold actualDiscrepancyFourier
  calc
    _ ≤ ∑ N ∈ blockCarrier B,
        ‖actualDiscrepancy B N R G * fourier (N : ℤ) x‖ := norm_sum_le _ _
    _ = _ := by simp [fourier_apply, Circle.norm_coe]

theorem discrepancy_fourier_bound_existing_range (B : ℕ) (hB : 2 ≤ B)
    (R : ℝ) (hR : 1 < R) (G : ℝ → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hG : ∀ x : ℝ, |G x| ≤ M)
    (hupper : R ≤ (B : ℝ)^((1 : ℝ)/10000)) (x : UnitAddCircle) :
    ‖actualDiscrepancyFourier B R G x‖ ≤ 2*M*(B : ℝ)/R :=
  (discrepancy_fourier_norm_le_mass B R G x).trans
    (actual_discrepancy_mass_le_existing_range B hB R hR G M hM hG hupper)

/-- This component fits the R^(-1/3) budget; other residuals are not included. -/
theorem discrepancy_fourier_fits_target_budget (B : ℕ) (hB : 2 ≤ B)
    (R : ℝ) (hR : 1 < R) (G : ℝ → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hG : ∀ x : ℝ, |G x| ≤ M)
    (hupper : R ≤ (B : ℝ)^((1 : ℝ)/10000)) (x : UnitAddCircle) :
    ‖actualDiscrepancyFourier B R G x‖ ≤ 2*M*(B : ℝ)*R^(-(1 : ℝ)/3) := by
  apply (discrepancy_fourier_bound_existing_range B hB R hR G M hM hG hupper x).trans
  rw [div_eq_mul_inv, ← Real.rpow_neg_one]
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hR.le (by norm_num)) (by positivity)


end GoldbachCircleMethodActualDiscrepancyScaleAbsorptionV18125
