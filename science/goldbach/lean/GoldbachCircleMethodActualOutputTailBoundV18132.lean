import GoldbachCircleMethodFiniteRamanujanEnergyV18131

set_option autoImplicit false
open scoped BigOperators Classical
open GoldbachCircleMethodFiniteResiduePrefixV1866
open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodLogCutoffPresieveBindingV18120
open GoldbachCircleMethodActualDiscrepancyScaleAbsorptionV18125
open GoldbachCircleMethodSignedWindowFourierAdapterV18130
open GoldbachCircleMethodFiniteRamanujanEnergyV18131

namespace GoldbachCircleMethodActualOutputTailBoundV18132

/-- Injective translation of the input indices cannot increase kernel L1. -/
theorem translated_kernel_mass_le (Q B : ℕ) (H : ℝ) (hH : 0 ≤ H)
    (w : ℕ → ℂ) (n : ℤ) :
    (∑ U ∈ blockCarrier B, ‖signedWindowKernel Q H w (n-(U : ℤ))‖) ≤
      ∑ k ∈ shiftCarrier H, ‖signedWindowKernel Q H w k‖ := by
  let S := (blockCarrier B).image (fun U : ℕ => n-(U : ℤ))
  have hi : Set.InjOn (fun U : ℕ => n-(U : ℤ)) (blockCarrier B) := by
    intro U _ V _ h
    exact Nat.cast_injective (sub_right_injective h)
  have hs : (∑ U ∈ blockCarrier B, ‖signedWindowKernel Q H w (n-(U : ℤ))‖) =
      ∑ k ∈ S, ‖signedWindowKernel Q H w k‖ := by
    dsimp only [S]
    rw [Finset.sum_image hi]
  calc
    _ = ∑ k ∈ S, ‖signedWindowKernel Q H w k‖ := hs
    _ ≤ ∑ k ∈ S ∪ shiftCarrier H, ‖signedWindowKernel Q H w k‖ :=
      Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left
        (fun _ _ _ => norm_nonneg _)
    _ = ∑ k ∈ shiftCarrier H, ‖signedWindowKernel Q H w k‖ := by
      symm
      apply Finset.sum_subset Finset.subset_union_right
      intro k _ hk
      rw [signed_kernel_eq_zero_outside Q H hH w k hk, norm_zero]

theorem signed_convolution_norm_le_kernel_mass (Q B : ℕ) (H : ℝ) (hH : 0 ≤ H)
    (f w : ℕ → ℂ) (A : ℝ) (hA : 0 ≤ A)
    (hf : ∀ U ∈ blockCarrier B, ‖f U‖ ≤ A) (n : ℤ) :
    ‖signedWindowConvolution Q B H f w n‖ ≤
      A*∑ k ∈ shiftCarrier H, ‖signedWindowKernel Q H w k‖ := by
  unfold signedWindowConvolution
  calc
    _ ≤ ∑ U ∈ blockCarrier B,
        ‖f U*signedWindowKernel Q H w (n-(U : ℤ))‖ := norm_sum_le _ _
    _ ≤ ∑ U ∈ blockCarrier B,
        A*‖signedWindowKernel Q H w (n-(U : ℤ))‖ := by
      apply Finset.sum_le_sum
      intro U hU
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hf U hU) (norm_nonneg _)
    _ = A*∑ U ∈ blockCarrier B, ‖signedWindowKernel Q H w (n-(U : ℤ))‖ := by
      rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (translated_kernel_mass_le Q B H hH w n) hA

/-- Actual outside output mass; the strips are not erased or renamed. -/
noncomputable def outputTailMass (Q B : ℕ) (H : ℝ) (f w : ℕ → ℂ) : ℝ :=
  ∑ n ∈ outputCarrier B H \ integerBlock B, ‖signedWindowConvolution Q B H f w n‖

theorem output_tail_le_kernel_mass (Q B : ℕ) (H : ℝ) (hH : 0 ≤ H)
    (f w : ℕ → ℂ) (A : ℝ) (hA : 0 ≤ A)
    (hf : ∀ U ∈ blockCarrier B, ‖f U‖ ≤ A) :
    outputTailMass Q B H f w ≤
      2*H*A*∑ k ∈ shiftCarrier H, ‖signedWindowKernel Q H w k‖ := by
  have hk0 : 0 ≤ ∑ k ∈ shiftCarrier H, ‖signedWindowKernel Q H w k‖ :=
    Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  unfold outputTailMass
  calc
    _ ≤ ∑ _n ∈ outputCarrier B H \ integerBlock B,
        A*∑ k ∈ shiftCarrier H, ‖signedWindowKernel Q H w k‖ :=
      Finset.sum_le_sum (fun n _ => signed_convolution_norm_le_kernel_mass Q B H hH f w A hA hf n)
    _ = (2*(⌊H⌋₊ : ℝ))*A*∑ k ∈ shiftCarrier H, ‖signedWindowKernel Q H w k‖ := by
      rw [Finset.sum_const, nsmul_eq_mul, outside_output_card]
      push_cast
      ring
    _ ≤ _ := by
      gcongr
      exact Nat.floor_le hH

theorem block_input_norm_le_log (B U : ℕ) (hU : U ∈ blockCarrier B) :
    ‖blockInput B U‖ ≤ Real.log (B : ℝ) := by
  have hu := Finset.mem_Ioc.mp hU
  have hUpos : 0 < U := lt_of_le_of_lt (Nat.zero_le _) hu.1
  rw [blockInput, if_pos hU, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
  exact ArithmeticFunction.vonMangoldt_le_log.trans
    (Real.log_le_log (Nat.cast_pos.mpr hUpos) (Nat.cast_le.mpr hu.2))

/-- The actual unpresieved Lambda input is bounded before scaling. -/
theorem actual_output_tail_le (Q B : ℕ) (hB : 2 ≤ B)
    (H : ℝ) (hH : 1 ≤ H) (hQH : (Q : ℝ) ≤ H)
    (w : ℕ → ℂ) (M : ℝ) (hM : 0 ≤ M)
    (hw : ∀ q : PositiveLevel Q, ‖w q.val‖ ≤ M) :
    outputTailMass Q B H (blockInput B) w ≤
      4*M*H*(Q : ℝ)*Real.sqrt (Q : ℝ)*Real.log (B : ℝ) := by
  have hlog : 0 ≤ Real.log (B : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ B))
  apply (output_tail_le_kernel_mass Q B H (by linarith)
    (blockInput B) w (Real.log (B : ℝ)) hlog (block_input_norm_le_log B)).trans
  calc
    _ ≤ (2*H*Real.log (B : ℝ))*(2*M*(Q : ℝ)*Real.sqrt (Q : ℝ)) :=
      mul_le_mul_of_nonneg_left (signed_kernel_l1_le Q H hH hQH w M hM hw) (by positivity)
    _ = _ := by ring

/-- Exact predeclared scale suffices for H>=max(1,Q). -/
theorem window_dominates_cutoff (B R : ℝ) (hR : 1 < R) (hscale : R^6 ≤ B) :
    1 ≤ B/R^4 ∧ (⌊R^2⌋₊ : ℝ) ≤ B/R^4 := by
  have hr : 0 < R := lt_trans zero_lt_one hR
  have h2 : R^2 ≤ B/R^4 := by
    apply (le_div_iff₀ (by positivity : 0 < R^4)).mpr
    simpa only [← pow_add] using hscale
  exact ⟨(one_le_pow₀ hR.le).trans h2, (Nat.floor_le (sq_nonneg R)).trans h2⟩

/-- Actual Lambda output tail under Q=floor R^2, H=B/R^4. -/
theorem actual_output_tail_scale_bound (B : ℕ) (hB : 2 ≤ B)
    (R : ℝ) (hR : 1 < R) (G : ℝ → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hG : ∀ x : ℝ, |G x| ≤ M) (hscale : R^6 ≤ (B : ℝ)) :
    outputTailMass ⌊R^2⌋₊ B ((B : ℝ)/R^4) (blockInput B) (logWeight R G) ≤
      4*M*(B : ℝ)*Real.log (B : ℝ)/R := by
  have hr : 0 < R := lt_trans zero_lt_one hR
  have hh := window_dominates_cutoff (B : ℝ) R hR hscale
  have hQ : (⌊R^2⌋₊ : ℝ) ≤ R^2 := Nat.floor_le (sq_nonneg R)
  have hsqrt : Real.sqrt (⌊R^2⌋₊ : ℝ) ≤ R := by
    calc
      _ ≤ Real.sqrt (R^2) := Real.sqrt_le_sqrt hQ
      _ = R := Real.sqrt_sq hr.le
  have hlog : 0 ≤ Real.log (B : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ B))
  have hw : ∀ q : PositiveLevel ⌊R^2⌋₊, ‖logWeight R G q.val‖ ≤ M := by
    intro q
    simpa only [logWeight, Complex.norm_real, Real.norm_eq_abs] using
      hG (Real.log (q.val : ℝ)/Real.log R)
  apply (actual_output_tail_le ⌊R^2⌋₊ B hB ((B : ℝ)/R^4) hh.1 hh.2
    (logWeight R G) M hM hw).trans
  calc
    _ ≤ 4*M*((B : ℝ)/R^4)*R^2*R*Real.log (B : ℝ) := by
      gcongr
    _ = _ := by field_simp

/-- The lower scale bound, not the upper bound, absorbs the logarithm. -/
theorem log_absorption_from_lower_scale (B R : ℝ) (hB : 1 ≤ B)
    (hR : 1 < R) (hlower : Real.exp (Real.sqrt (Real.log B)) ≤ R) :
    Real.log B/R ≤ 9*R^(-(1 : ℝ)/3) := by
  have hr : 0 < R := lt_trans zero_lt_one hR
  have hlogB : 0 ≤ Real.log B := Real.log_nonneg hB
  have hlogR : 0 ≤ Real.log R := Real.log_nonneg hR.le
  have hroot : Real.sqrt (Real.log B) ≤ Real.log R := by
    have h := Real.log_le_log (Real.exp_pos _) hlower
    simpa only [Real.log_exp] using h
  have hBsq : Real.log B ≤ (Real.log R)^2 := by
    have h := pow_le_pow_left₀ (Real.sqrt_nonneg _) hroot 2
    simpa only [Real.sq_sqrt hlogB] using h
  have hlog : Real.log R ≤ 3*R^((1 : ℝ)/3) := by
    have h := Real.log_le_rpow_div hr.le (by norm_num : (0 : ℝ) < 1/3)
    linarith
  have hsq : (Real.log R)^2 ≤ 9*R^((2 : ℝ)/3) := by
    calc
      _ ≤ (3*R^((1 : ℝ)/3))^2 := pow_le_pow_left₀ hlogR hlog 2
      _ = 9*R^((2 : ℝ)/3) := by
        rw [mul_pow, ← Real.rpow_mul_natCast hr.le]
        norm_num
  calc
    _ ≤ (9*R^((2 : ℝ)/3))/R :=
      div_le_div_of_nonneg_right (hBsq.trans hsq) hr.le
    _ = 9*R^(-(1 : ℝ)/3) := by
      have hp : R^((2 : ℝ)/3)/R = R^(-(1 : ℝ)/3) := by
        calc
          _ = R^((2 : ℝ)/3)/R^(1 : ℝ) := by rw [Real.rpow_one]
          _ = R^((2 : ℝ)/3-1) := (Real.rpow_sub hr _ _).symm
          _ = _ := by congr 1; norm_num
      rw [mul_div_assoc, hp]

/-- Source-bound tail fits the declared R^(-1/3) budget. -/
theorem actual_output_tail_fits_budget (B : ℕ) (hB : 2 ≤ B)
    (R : ℝ) (hR : 1 < R) (G : ℝ → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hG : ∀ x : ℝ, |G x| ≤ M)
    (hupper : R ≤ (B : ℝ)^((1 : ℝ)/10000))
    (hlower : Real.exp (Real.sqrt (Real.log (B : ℝ))) ≤ R) :
    outputTailMass ⌊R^2⌋₊ B ((B : ℝ)/R^4) (blockInput B) (logWeight R G) ≤
      36*M*(B : ℝ)*R^(-(1 : ℝ)/3) := by
  have hb : (1 : ℝ) ≤ B := by exact_mod_cast (by omega : 1 ≤ B)
  have hs34 := existing_upper_range_implies_scale (B : ℝ) R hb
    (le_of_lt (lt_trans zero_lt_one hR)) hupper
  have hs6 : R^6 ≤ (B : ℝ) :=
    (pow_le_pow_right₀ hR.le (by decide : 6 ≤ 34)).trans hs34
  apply (actual_output_tail_scale_bound B hB R hR G M hM hG hs6).trans
  calc
    _ = (4*M*(B : ℝ))*(Real.log (B : ℝ)/R) := by ring
    _ ≤ (4*M*(B : ℝ))*(9*R^(-(1 : ℝ)/3)) :=
      mul_le_mul_of_nonneg_left (log_absorption_from_lower_scale (B : ℝ) R hb hR hlower)
        (by positivity)
    _ = _ := by ring

noncomputable def actualOutputTailFourier (B : ℕ) (R : ℝ) (G : ℝ → ℝ)
    (x : UnitAddCircle) : ℂ :=
  ∑ n ∈ outputCarrier B ((B : ℝ)/R^4) \ integerBlock B,
    signedWindowConvolution ⌊R^2⌋₊ B ((B : ℝ)/R^4) (blockInput B) (logWeight R G) n *
      fourier n x

theorem actual_output_tail_fourier_fits_budget (B : ℕ) (hB : 2 ≤ B)
    (R : ℝ) (hR : 1 < R) (G : ℝ → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hG : ∀ x : ℝ, |G x| ≤ M)
    (hupper : R ≤ (B : ℝ)^((1 : ℝ)/10000))
    (hlower : Real.exp (Real.sqrt (Real.log (B : ℝ))) ≤ R) (x : UnitAddCircle) :
    ‖actualOutputTailFourier B R G x‖ ≤ 36*M*(B : ℝ)*R^(-(1 : ℝ)/3) := by
  apply (outside_output_fourier_norm_le ⌊R^2⌋₊ B ((B : ℝ)/R^4)
    (blockInput B) (logWeight R G) x).trans
  exact actual_output_tail_fits_budget B hB R hR G M hM hG hupper hlower

/-- The finite restriction adapter now has a quantified tail; the multiplier
factor is explicit and still requires its separate major/minor bounds. -/
theorem actual_window_fourier_error_le (B : ℕ) (hB : 2 ≤ B)
    (R : ℝ) (hR : 1 < R) (G : ℝ → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hG : ∀ x : ℝ, |G x| ≤ M)
    (hupper : R ≤ (B : ℝ)^((1 : ℝ)/10000))
    (hlower : Real.exp (Real.sqrt (Real.log (B : ℝ))) ≤ R) (x : UnitAddCircle) :
    ‖(∑ N ∈ blockCarrier B, blockInput B N*fourier (N : ℤ) x) -
      (∑ N ∈ blockCarrier B,
        GoldbachCircleMethodFiniteWindowConvolutionV18119.normalizedWindowConvolution
          ⌊R^2⌋₊ N ((B : ℝ)/R^4) (blockCarrier B) (blockInput B) (logWeight R G) *
            fourier (N : ℤ) x)‖ ≤
    ‖∑ N ∈ blockCarrier B, blockInput B N*fourier (N : ℤ) x‖ *
      ‖1-∑ k ∈ shiftCarrier ((B : ℝ)/R^4),
        signedWindowKernel ⌊R^2⌋₊ ((B : ℝ)/R^4) (logWeight R G) k * fourier k x‖ +
      36*M*(B : ℝ)*R^(-(1 : ℝ)/3) := by
  rw [input_minus_restricted_fourier_identity ⌊R^2⌋₊ B ((B : ℝ)/R^4)
    (by positivity) (blockInput B) (logWeight R G) x]
  apply (norm_add_le _ _).trans
  rw [norm_mul]
  exact add_le_add le_rfl (actual_output_tail_fourier_fits_budget B hB R hR G M hM hG
    hupper hlower x)

end GoldbachCircleMethodActualOutputTailBoundV18132
