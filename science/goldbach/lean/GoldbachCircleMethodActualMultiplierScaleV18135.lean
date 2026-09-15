import GoldbachCircleMethodSeparatedFrequencyMultiplierV18134
import GoldbachCircleMethodActualMaskReflectionV1886

set_option autoImplicit false
open scoped BigOperators Classical
open GoldbachCircleMethodLogCutoffPresieveBindingV18120
open GoldbachCircleMethodActualDiscrepancyScaleAbsorptionV18125
open GoldbachCircleMethodActualOutputTailBoundV18132
open GoldbachCircleMethodSignedWindowFourierAdapterV18130
open GoldbachCircleMethodSeparatedFrequencyMultiplierV18134
open GoldbachCircleMethodMajorMinorPartitionV172
open GoldbachCircleMethodActualMaskReflectionV1886

namespace GoldbachCircleMethodActualMultiplierScaleV18135

/-- A name for the existing V130 kernel transform at the fixed V120 scales. -/
noncomputable def logWindowMultiplier (B R : ℝ) (G : ℝ → ℝ) (x : UnitAddCircle) : ℂ :=
  ∑ k ∈ shiftCarrier (B/R^4),
    signedWindowKernel ⌊R^2⌋₊ (B/R^4) (logWeight R G) k * fourier k x

theorem squared_cutoff_positive (R : ℝ) (hR : 1<R) : 0<⌊R^2⌋₊ := by
  apply Nat.lt_of_lt_of_le Nat.zero_lt_one
  apply (Nat.le_floor_iff (sq_nonneg R)).mpr
  exact_mod_cast one_le_pow₀ hR.le (n := 2)

theorem log_weight_norm_le (R : ℝ) (G : ℝ → ℝ) (M : ℝ)
    (hG : ∀ u : ℝ, |G u|≤M) (q : ℕ) :
    ‖logWeight R G q‖≤M := by
  simpa only [logWeight, Complex.norm_real, Real.norm_eq_abs] using
    hG (Real.log (q : ℝ)/Real.log R)

/-- Weight one requires the declared plateau, not boundedness alone. -/
theorem log_weight_eq_one (R : ℝ) (hR : 1<R) (G : ℝ → ℝ)
    (hG : ∀ u : ℝ, 0≤u → u≤1 → G u=1)
    (q : ℕ) (hq : 0<q) (hqr : (q : ℝ)≤R) :
    logWeight R G q=1 := by
  have hlR := Real.log_pos hR
  have hlq : 0≤Real.log (q : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1≤q by omega))
  have hratio : Real.log (q : ℝ)/Real.log R≤1 := by
    apply (div_le_one hlR).mpr
    exact Real.log_le_log (Nat.cast_pos.mpr hq) hqr
  simp only [logWeight, hG _ (div_nonneg hlq hlR.le) hratio, Complex.ofReal_one]

theorem cutoff_remainder_scale (B R M : ℝ) (hB : 0<B) (hR : 0<R) (hM : 0≤M) :
    M*(⌊R^2⌋₊ : ℝ)^4/(2*(B/R^4)) ≤ M*R^12/(2*B) := by
  have hQ : (⌊R^2⌋₊ : ℝ)≤R^2 := Nat.floor_le (sq_nonneg R)
  calc
    _ ≤ M*(R^2)^4/(2*(B/R^4)) := by gcongr
    _ = _ := by field_simp

theorem cutoff_half_gap_scale (B R : ℝ) (hB : 0<B) (hR : 1<R)
    (hscale : 2*R^5≤B) :
    R/B≤1/(2*(⌊R^2⌋₊ : ℝ)^2) := by
  have hr : 0<R := lt_trans zero_lt_one hR
  have hq : (0 : ℝ)<⌊R^2⌋₊ := by exact_mod_cast squared_cutoff_positive R hR
  have hQ : (⌊R^2⌋₊ : ℝ)≤R^2 := Nat.floor_le (sq_nonneg R)
  apply (div_le_div_iff₀ hB (by positivity : 0<2*(⌊R^2⌋₊ : ℝ)^2)).mpr
  calc
    R*(2*(⌊R^2⌋₊ : ℝ)^2) ≤ R*(2*(R^2)^2) := by gcongr
    _ = 2*R^5 := by ring
    _ ≤ 1*B := by simpa using hscale

theorem actual_log_multiplier_global_raw (B R : ℝ) (hB : 0<B) (hR : 1<R)
    (hscale : R^6≤B) (G : ℝ → ℝ) (M : ℝ) (hM : 0≤M)
    (hG : ∀ u : ℝ, |G u|≤M) (x : UnitAddCircle) :
    ‖logWindowMultiplier B R G x‖ ≤ (3/2)*M+M*R^12/(2*B) := by
  have hh := (window_dominates_cutoff B R hR hscale).1
  apply (actual_multiplier_global_bound ⌊R^2⌋₊ (squared_cutoff_positive R hR)
    (B/R^4) hh (logWeight R G) M hM (fun i => log_weight_norm_le R G M hG i.val.1) x).trans
  exact add_le_add_right (cutoff_remainder_scale B R M hB (by linarith) hM) _

/-- Exact reflection selects -a/q, preserving its denominator and plateau weight. -/
theorem actual_log_multiplier_near_major_raw (B R : ℝ) (hB : 0<B) (hR : 1<R)
    (hwindow : R^6≤B) (hgap : 2*R^5≤B)
    (G : ℝ → ℝ) (M : ℝ) (hM : 0≤M) (hG : ∀ u : ℝ, |G u|≤M)
    (hplateau : ∀ u : ℝ, 0≤u → u≤1 → G u=1)
    (x : UnitAddCircle) (i : ReducedRationalIndex ⌊R^2⌋₊)
    (hiR : (i.val.1 : ℝ)≤R) (hx : dist x (majorArcCenter i)≤R/B) :
    ‖logWindowMultiplier B R G x-1‖ ≤
      R^4/(2*B)+3*Real.pi/R^3+M*R^12/(2*B) := by
  have hr : 0<R := lt_trans zero_lt_one hR
  obtain ⟨j,hji,hcenter⟩ := original_index_has_neg_center i
  have hnorm : ‖x+majorArcCenter j‖=dist x (majorArcCenter i) := by
    rw [hcenter,dist_eq_norm,sub_eq_add_neg]
  have hjweight : logWeight R G j.val.1=1 := by
    rw [hji]
    exact log_weight_eq_one R hR G hplateau i.val.1 (index_denominator_pos i) hiR
  have hjgap : ‖x+majorArcCenter j‖≤1/(2*(⌊R^2⌋₊ : ℝ)^2) := by
    rw [hnorm]
    exact hx.trans (cutoff_half_gap_scale B R hB hR hgap)
  have hh := (window_dominates_cutoff B R hR hwindow).1
  apply (actual_multiplier_near_center ⌊R^2⌋₊ (squared_cutoff_positive R hR)
    (B/R^4) hh (logWeight R G) M hM x j
    (fun k => log_weight_norm_le R G M hG k.val.1) hjweight hjgap).trans
  rw [hnorm]
  calc
    _ ≤ 1/(2*(B/R^4))+3*Real.pi*(B/R^4)*(R/B)+M*R^12/(2*B) := by
      exact add_le_add (add_le_add le_rfl
        (mul_le_mul_of_nonneg_left hx (by positivity)))
        (cutoff_remainder_scale B R M hB hr hM)
    _ = _ := by field_simp

/-- The existing lower range implies R>=2 already for B>=2. -/
theorem lower_range_two_le (B R : ℝ) (hB : 2≤B)
    (hlower : Real.exp (Real.sqrt (Real.log B))≤R) : 2≤R := by
  have hl2 : 0≤Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
  have hl21 : Real.log (2 : ℝ)≤1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ)<2)
    linarith
  have hlB : Real.log (2 : ℝ)≤Real.log B := Real.log_le_log (by norm_num) hB
  have hB0 : 0≤Real.log B := hl2.trans hlB
  have hs := Real.sq_sqrt hB0
  have hs0 := Real.sqrt_nonneg (Real.log B)
  have hls : Real.log (2 : ℝ)≤Real.sqrt (Real.log B) := by nlinarith
  have he := Real.exp_le_exp.mpr hls
  rw [Real.exp_log (by norm_num : (0 : ℝ)<2)] at he
  exact he.trans hlower

theorem upper_scale_window_and_gap (B R : ℝ) (hB : 1≤B) (hR : 2≤R)
    (hupper : R≤B^((1 : ℝ)/10000)) :
    R^6≤B ∧ 2*R^5≤B ∧ R^15≤B := by
  have hr : 1≤R := by linarith
  have hs := existing_upper_range_implies_scale B R hB (by linarith) hupper
  have h6 : R^6≤B := (pow_le_pow_right₀ hr (by norm_num : 6≤34)).trans hs
  have hg : 2*R^5≤R^6 := by
    calc
      _ ≤ R*R^5 := mul_le_mul_of_nonneg_right hR (by positivity)
      _ = R^6 := by ring
  exact ⟨h6,hg.trans h6,(pow_le_pow_right₀ hr (by norm_num : 15≤34)).trans hs⟩

theorem power_ratio_absorption (B R : ℝ) (hB : 0<B) (hR : 0<R)
    (k : ℕ) (hscale : R^(k+3)≤B) :
    R^k/B≤1/R^3 := by
  apply (div_le_div_iff₀ hB (pow_pos hR 3)).mpr
  simpa only [←pow_add,one_mul] using hscale

theorem major_error_scale_absorption (B R M : ℝ) (hB : 0<B) (hR : 1≤R)
    (hM : 0≤M) (hscale : R^15≤B) :
    R^4/(2*B)+3*Real.pi/R^3+M*R^12/(2*B) ≤
      ((1+M)/2+3*Real.pi)/R^3 := by
  have hr : 0<R := lt_of_lt_of_le zero_lt_one hR
  have h7 : R^(4+3)≤B := (pow_le_pow_right₀ hR (by norm_num : 4+3≤15)).trans hscale
  have h12 : R^(12+3)≤B := by simpa using hscale
  have hfirst := power_ratio_absorption B R hB hr 4 h7
  have hlast := power_ratio_absorption B R hB hr 12 h12
  have hm := mul_le_mul_of_nonneg_left hlast hM
  calc
    _ = (R^4/B)/2+3*Real.pi/R^3+M*(R^12/B)/2 := by ring
    _ ≤ (1/R^3)/2+3*Real.pi/R^3+M*(1/R^3)/2 := by linarith
    _ = _ := by ring

theorem actual_log_multiplier_global_existing_range (B R : ℝ) (hB : 2≤B)
    (hR : 2≤R) (hupper : R≤B^((1 : ℝ)/10000))
    (G : ℝ → ℝ) (M : ℝ) (hM : 0≤M) (hG : ∀ u : ℝ, |G u|≤M)
    (x : UnitAddCircle) : ‖logWindowMultiplier B R G x‖≤2*M := by
  have hh := upper_scale_window_and_gap B R (by linarith) hR hupper
  apply (actual_log_multiplier_global_raw B R (by linarith) (by linarith)
    hh.1 G M hM hG x).trans
  have h12 : R^12≤B :=
    (pow_le_pow_right₀ (by linarith : 1≤R) (by norm_num : 12≤15)).trans hh.2.2
  have hratio : R^12/B≤1 := (div_le_one (by linarith : 0<B)).mpr h12
  have hm := mul_le_mul_of_nonneg_left hratio hM
  have he : M*R^12/(2*B)=M*(R^12/B)/2 := by ring
  rw [he]
  linarith

theorem actual_log_multiplier_major_existing_range (B R : ℝ) (hB : 2≤B)
    (hR : 2≤R) (hupper : R≤B^((1 : ℝ)/10000))
    (G : ℝ → ℝ) (M : ℝ) (hM : 0≤M) (hG : ∀ u : ℝ, |G u|≤M)
    (hplateau : ∀ u : ℝ, 0≤u → u≤1 → G u=1)
    (x : UnitAddCircle) (i : ReducedRationalIndex ⌊R^2⌋₊)
    (hiR : (i.val.1 : ℝ)≤R) (hx : dist x (majorArcCenter i)≤R/B) :
    ‖logWindowMultiplier B R G x-1‖≤((1+M)/2+3*Real.pi)/R^3 := by
  have hh := upper_scale_window_and_gap B R (by linarith) hR hupper
  exact (actual_log_multiplier_near_major_raw B R (by linarith) (by linarith)
    hh.1 hh.2.1 G M hM hG hplateau x i hiR hx).trans
      (major_error_scale_absorption B R M (by linarith) (by linarith) hM hh.2.2)


theorem inverse_cube_le_target_scale (R : ℝ) (hR : 1≤R) :
    1/R^3≤R^(-(1 : ℝ)/3) := by
  have he : R^(-(3 : ℝ))=1/R^3 := by
    rw [Real.rpow_neg (by linarith : 0≤R)]
    norm_num
  rw [←he]
  exact Real.rpow_le_rpow_of_exponent_le hR (by norm_num)

theorem actual_log_multiplier_full_range (B R : ℝ) (hB : 2≤B)
    (hlower : Real.exp (Real.sqrt (Real.log B))≤R)
    (hupper : R≤B^((1 : ℝ)/10000))
    (G : ℝ → ℝ) (M : ℝ) (hM : 0≤M) (hG : ∀ u : ℝ, |G u|≤M)
    (x : UnitAddCircle) : ‖logWindowMultiplier B R G x‖≤2*M :=
  actual_log_multiplier_global_existing_range B R hB
    (lower_range_two_le B R hB hlower) hupper G M hM hG x

/-- Kernel factor only: this does not bound the actual prime exponential sum. -/
theorem actual_log_multiplier_major_fits_target (B R : ℝ) (hB : 2≤B)
    (hlower : Real.exp (Real.sqrt (Real.log B))≤R)
    (hupper : R≤B^((1 : ℝ)/10000))
    (G : ℝ → ℝ) (M : ℝ) (hM : 0≤M) (hG : ∀ u : ℝ, |G u|≤M)
    (hplateau : ∀ u : ℝ, 0≤u → u≤1 → G u=1)
    (x : UnitAddCircle) (i : ReducedRationalIndex ⌊R^2⌋₊)
    (hiR : (i.val.1 : ℝ)≤R) (hx : dist x (majorArcCenter i)≤R/B) :
    ‖logWindowMultiplier B R G x-1‖≤
      ((1+M)/2+3*Real.pi)*R^(-(1 : ℝ)/3) := by
  have hR := lower_range_two_le B R hB hlower
  apply (actual_log_multiplier_major_existing_range B R hB hR hupper
    G M hM hG hplateau x i hiR hx).trans
  rw [div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_left
    (by simpa only [one_div] using inverse_cube_le_target_scale R (by linarith))
    (by positivity)

end GoldbachCircleMethodActualMultiplierScaleV18135
