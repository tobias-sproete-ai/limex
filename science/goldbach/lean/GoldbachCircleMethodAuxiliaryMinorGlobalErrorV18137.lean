import GoldbachCircleMethodActualBlockAuxiliaryMinorV18136

set_option autoImplicit false
open scoped BigOperators Classical
open GoldbachCircleMethodFourierIdentityV171
open GoldbachCircleMethodActualOutputTailBoundV18132
open GoldbachCircleMethodActualMultiplierScaleV18135
open GoldbachCircleMethodRealApproximationMinorAdapterV1873
open GoldbachCircleMethodActualBlockAuxiliaryMinorV18136

namespace GoldbachCircleMethodAuxiliaryMinorGlobalErrorV18137

theorem sqrt_tail_le (B R : ℝ) (hB : 0≤B) :
    Real.sqrt (2*B^2/R)≤2*B/Real.sqrt R := by
  rw [Real.sqrt_div (by positivity),Real.sqrt_mul (by norm_num : (0 : ℝ)≤2),
    Real.sqrt_sq hB]
  apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg R)
  exact mul_le_mul_of_nonneg_right (by norm_num : Real.sqrt 2≤2) hB

theorem upper_range_secondary_term (B R : ℝ) (hB : 1≤B) (hR : 0<R)
    (hupper : R≤B^((1 : ℝ)/10000)) :
    B^((4 : ℝ)/5)≤B/Real.sqrt R := by
  have hb : 0<B := lt_of_lt_of_le zero_lt_one hB
  have hs : Real.sqrt R≤B^((1 : ℝ)/5) := by
    calc
      _ = R^((1 : ℝ)/2) := Real.sqrt_eq_rpow R
      _ ≤ (B^((1 : ℝ)/10000))^((1 : ℝ)/2) := by gcongr
      _ = B^((1 : ℝ)/20000) := by rw [←Real.rpow_mul hb.le]; norm_num
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hB (by norm_num)
  apply (le_div_iff₀ (Real.sqrt_pos.mpr hR)).mpr
  calc
    _ ≤ B^((4 : ℝ)/5)*B^((1 : ℝ)/5) :=
      mul_le_mul_of_nonneg_left hs (Real.rpow_nonneg hb.le _)
    _ = B := by rw [←Real.rpow_add hb]; norm_num

/-- Explicit log absorption under the existing lower range.
The large constant is deliberate; no sharp-constant or practical-threshold claim. -/
theorem log_four_over_sqrt_bound (B R : ℝ) (hB : 1≤B) (hR : 1<R)
    (hlower : Real.exp (Real.sqrt (Real.log B))≤R) :
    (Real.log B)^4/Real.sqrt R≤(48 : ℝ)^8*R^(-(1 : ℝ)/3) := by
  have hr : 0<R := lt_trans zero_lt_one hR
  have hlogB : 0≤Real.log B := Real.log_nonneg hB
  have hlogR : 0≤Real.log R := Real.log_nonneg hR.le
  have hroot : Real.sqrt (Real.log B)≤Real.log R := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos _) hlower
  have hBsq : Real.log B≤(Real.log R)^2 := by
    simpa only [Real.sq_sqrt hlogB] using
      pow_le_pow_left₀ (Real.sqrt_nonneg _) hroot 2
  have hlog : Real.log R≤48*R^((1 : ℝ)/48) := by
    have h := Real.log_le_rpow_div hr.le (by norm_num : (0 : ℝ)<1/48)
    linarith
  have h8 : (Real.log B)^4≤(48 : ℝ)^8*R^((1 : ℝ)/6) := by
    calc
      _ ≤ ((Real.log R)^2)^4 := pow_le_pow_left₀ hlogB hBsq 4
      _ = (Real.log R)^8 := by ring
      _ ≤ (48*R^((1 : ℝ)/48))^8 := pow_le_pow_left₀ hlogR hlog 8
      _ = _ := by
        rw [mul_pow,←Real.rpow_mul_natCast hr.le]
        norm_num
  calc
    _ ≤ ((48 : ℝ)^8*R^((1 : ℝ)/6))/Real.sqrt R :=
      div_le_div_of_nonneg_right h8 (Real.sqrt_nonneg R)
    _ = (48 : ℝ)^8*R^(-(1 : ℝ)/3) := by
      rw [Real.sqrt_eq_rpow,mul_div_assoc,←Real.rpow_sub hr]
      norm_num

theorem upper_range_implies_R_le_B (B R : ℝ) (hB : 1≤B)
    (hupper : R≤B^((1 : ℝ)/10000)) : R≤B := by
  apply hupper.trans
  calc
    _ ≤ B^(1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hB (by norm_num)
    _ = B := Real.rpow_one B

theorem vaughan_block_envelope_absorption (B R C : ℝ) (hB : 1≤B)
    (hR : 1<R) (hC : 0≤C)
    (hlower : Real.exp (Real.sqrt (Real.log B))≤R)
    (hupper : R≤B^((1 : ℝ)/10000)) :
    2*C*(Real.log B)^4*(B/Real.sqrt R+B^((4 : ℝ)/5)+Real.sqrt (2*B^2/R)) ≤
      (8*(48 : ℝ)^8*C)*B*R^(-(1 : ℝ)/3) := by
  have hr : 0<R := lt_trans zero_lt_one hR
  have ht2 := upper_range_secondary_term B R hB hr hupper
  have ht3 := sqrt_tail_le B R (by linarith)
  rw [show 2*B/Real.sqrt R=2*(B/Real.sqrt R) by ring] at ht3
  have hs : B/Real.sqrt R+B^((4 : ℝ)/5)+Real.sqrt (2*B^2/R)≤
      4*B/Real.sqrt R := by
    rw [show 4*B/Real.sqrt R=4*(B/Real.sqrt R) by ring]
    linarith
  calc
    _ ≤ 2*C*(Real.log B)^4*(4*B/Real.sqrt R) :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    _ = (8*C*B)*((Real.log B)^4/Real.sqrt R) := by ring
    _ ≤ (8*C*B)*((48 : ℝ)^8*R^(-(1 : ℝ)/3)) :=
      mul_le_mul_of_nonneg_left (log_four_over_sqrt_bound B R hB hR hlower)
        (by positivity)
    _ = _ := by ring

/-- Actual block cancellation only under the explicit hV parameter. -/
theorem actual_auxiliary_minor_input_fits_budget (B : ℕ) (hB : 6≤B)
    (R C : ℝ) (hC : 0≤C) (hV : RealVaughanEstimate C)
    (hlower : Real.exp (Real.sqrt (Real.log (B : ℝ)))≤R)
    (hupper : R≤(B : ℝ)^((1 : ℝ)/10000))
    (x : UnitAddCircle) (hx : x ∉ auxiliaryMajor (B : ℝ) R) :
    ‖blockFourier B x‖≤(8*(48 : ℝ)^8*C)*(B : ℝ)*R^(-(1 : ℝ)/3) := by
  have hb : (2 : ℝ)≤B := by exact_mod_cast (by omega : 2≤B)
  have hr : 1<R := by linarith [lower_range_two_le (B : ℝ) R hb hlower]
  exact (actual_block_auxiliary_minor_bound B hB R C hr
    (upper_range_implies_R_le_B (B : ℝ) R (by linarith) hupper) hC hV x hx).trans
    (vaughan_block_envelope_absorption (B : ℝ) R C (by linarith) hr hC hlower hupper)

/-- Restricted-output minor error, with the actual tail still included. -/
theorem actual_auxiliary_minor_window_fits_budget (B : ℕ) (hB : 6≤B)
    (R C : ℝ) (hC : 0≤C) (hV : RealVaughanEstimate C)
    (hlower : Real.exp (Real.sqrt (Real.log (B : ℝ)))≤R)
    (hupper : R≤(B : ℝ)^((1 : ℝ)/10000))
    (G : ℝ → ℝ) (M : ℝ) (hM : 0≤M) (hG : ∀ u : ℝ, |G u|≤M)
    (x : UnitAddCircle) (hx : x ∉ auxiliaryMajor (B : ℝ) R) :
    ‖blockFourier B x-windowFourier B R G x‖≤
      ((8*(48 : ℝ)^8*C)*(1+2*M)+36*M)*(B : ℝ)*R^(-(1 : ℝ)/3) := by
  have hb : (2 : ℝ)≤B := by exact_mod_cast (by omega : 2≤B)
  have hr : 1<R := by linarith [lower_range_two_le (B : ℝ) R hb hlower]
  have he := actual_window_auxiliary_minor_error_bound B hB R C
    (upper_range_implies_R_le_B (B : ℝ) R (by linarith) hupper)
    hlower hupper hC hV G M hM hG x hx
  have hp := mul_le_mul_of_nonneg_right
    (vaughan_block_envelope_absorption (B : ℝ) R C (by linarith) hr hC hlower hupper)
    (by positivity : 0≤1+2*M)
  exact he.trans (by nlinarith)

/-- Global auxiliary-mask assembly. A case split covers the circle; no
identification with the original arc mask or assertion of hV is made. -/
theorem actual_window_global_error_fits_budget (B : ℕ) (hB : 6≤B)
    (R C : ℝ) (hC : 0≤C) (hV : RealVaughanEstimate C)
    (hlower : Real.exp (Real.sqrt (Real.log (B : ℝ)))≤R)
    (hupper : R≤(B : ℝ)^((1 : ℝ)/10000))
    (G : ℝ → ℝ) (M : ℝ) (hM : 0≤M) (hG : ∀ u : ℝ, |G u|≤M)
    (hplateau : ∀ u : ℝ, 0≤u → u≤1 → G u=1)
    (x : UnitAddCircle) :
    ‖blockFourier B x-windowFourier B R G x‖≤
      (9*((1+M)/2+3*Real.pi)+(8*(48 : ℝ)^8*C)*(1+2*M)+36*M)*
        (B : ℝ)*R^(-(1 : ℝ)/3) := by
  have hb : (2 : ℝ)≤B := by exact_mod_cast (by omega : 2≤B)
  have hr : 0<R := by linarith [lower_range_two_le (B : ℝ) R hb hlower]
  by_cases hx : x ∈ auxiliaryMajor (B : ℝ) R
  · have h := actual_window_major_error_bound B (by omega) R hlower hupper
      G M hM hG hplateau x hx
    have hp : 0≤(8*(48 : ℝ)^8*C)*(1+2*M)*(B : ℝ)*R^(-(1 : ℝ)/3) := by positivity
    nlinarith
  · have h := actual_auxiliary_minor_window_fits_budget B hB R C hC hV
      hlower hupper G M hM hG x hx
    have hp : 0≤9*((1+M)/2+3*Real.pi)*(B : ℝ)*R^(-(1 : ℝ)/3) := by positivity
    nlinarith

end GoldbachCircleMethodAuxiliaryMinorGlobalErrorV18137
