import GoldbachCircleMethodFiniteAbelAdapterV1863
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! # V1.8.64: the actual ceil/ceil parameter schedule.
Only elementary scale envelopes and their limits. No SW estimate is supplied.
-/
open Filter Topology

namespace GoldbachCircleMethodCeilScaleEnvelopesV1864

noncomputable def logRadius (K M : ℕ) : ℕ := ⌈(Real.log (M : ℝ))^K⌉₊
noncomputable def logWidth (K M : ℕ) : ℕ := ⌈(Real.log (M : ℝ))^(3*K)⌉₊

theorem ceil_power_bounds (x : ℝ) (hx : 1 ≤ x) (n : ℕ) :
    x^n ≤ (⌈x^n⌉₊ : ℝ) ∧ (⌈x^n⌉₊ : ℝ) ≤ 2*x^n := by
  have hp : 1 ≤ x^n := one_le_pow₀ hx
  exact ⟨Nat.le_ceil _, (Nat.ceil_lt_add_one (by positivity)).le.trans (by linarith)⟩

theorem log_scales_positive (K M : ℕ) (hlog : 1 ≤ Real.log (M : ℝ)) :
    1 ≤ logRadius K M ∧ 0 < logWidth K M := by
  have hr := (ceil_power_bounds (Real.log (M : ℝ)) hlog K).1
  have hp := (ceil_power_bounds (Real.log (M : ℝ)) hlog (3*K)).1
  have hr1 : (1 : ℝ) ≤ logRadius K M := (one_le_pow₀ hlog).trans hr
  have hp1 : (1 : ℝ) ≤ logWidth K M := (one_le_pow₀ hlog).trans hp
  exact ⟨by exact_mod_cast hr1, by exact_mod_cast hp1⟩

theorem log_scales_product_bound (K M : ℕ) (hlog : 1 ≤ Real.log (M : ℝ)) :
    (logWidth K M : ℝ)*(logRadius K M : ℝ) ≤ 4*(Real.log (M : ℝ))^(4*K) := by
  have h := mul_le_mul (ceil_power_bounds _ hlog (3*K)).2
    (ceil_power_bounds _ hlog K).2 (Nat.cast_nonneg _)
      (show 0 ≤ 2*(Real.log (M : ℝ))^(3*K) by positivity)
  calc
    _ ≤ (2*(Real.log (M : ℝ))^(3*K))*(2*(Real.log (M : ℝ))^K) := h
    _ = _ := by rw [show 4*K=3*K+K by omega, pow_add]; ring

theorem log_scales_model_tail_bound (K M : ℕ) (hlog : 1 ≤ Real.log (M : ℝ)) :
    (logRadius K M : ℝ)^2/(2*(logWidth K M : ℝ)) ≤
      2/(Real.log (M : ℝ))^K := by
  have hx : 0 < Real.log (M : ℝ) := by linarith
  have hr := (ceil_power_bounds _ hlog K).2
  have hp := (ceil_power_bounds _ hlog (3*K)).1
  change (logRadius K M : ℝ) ≤ 2*(Real.log (M : ℝ))^K at hr
  change (Real.log (M : ℝ))^(3*K) ≤ (logWidth K M : ℝ) at hp
  have hsq : (logRadius K M : ℝ)^2 ≤ (2*(Real.log (M : ℝ))^K)^2 := by
    nlinarith [Nat.cast_nonneg (logRadius K M) (α := ℝ)]
  calc
    _ ≤ (2*(Real.log (M : ℝ))^K)^2/(2*(Real.log (M : ℝ))^(3*K)) := by
      exact div_le_div₀ (by positivity) hsq (by positivity) (by linarith)
    _ = _ := by
      rw [show 3*K=K*3 by omega, pow_mul]
      field_simp

theorem log_power_sqrt_exp_decay (n : ℕ) (c : ℝ) (hc : 0 < c) :
    Tendsto (fun x : ℝ => (Real.log x)^n*Real.exp (-c*Real.sqrt (Real.log x)))
      atTop (𝓝 0) := by
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
    ((2*n : ℕ) : ℝ) c hc).comp
      (Real.tendsto_sqrt_atTop.comp Real.tendsto_log_atTop)
  simp only [Real.rpow_natCast, Function.comp_def] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  rw [pow_mul, Real.sq_sqrt (Real.log_nonneg hx)]

theorem log_power_div_scale_tendsto_zero (n : ℕ) :
    Tendsto (fun M : ℕ => (Real.log (M : ℝ))^n/(M : ℝ)) atTop (𝓝 0) := by
  have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 n (by norm_num)).comp
    tendsto_natCast_atTop_atTop
  simpa only [Function.comp_def, one_mul, add_zero] using h

theorem log_scales_geometric_mass_tendsto_zero (K : ℕ) :
    Tendsto (fun M : ℕ => 2*(logWidth K M : ℝ)*(logRadius K M : ℝ)/(M : ℝ))
      atTop (𝓝 0) := by
  have hlog : ∀ᶠ M : ℕ in atTop, 1 ≤ Real.log (M : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1
  have hu : Tendsto (fun M : ℕ => 8*(Real.log (M : ℝ))^(4*K)/(M : ℝ))
      atTop (𝓝 0) := by
    simpa only [mul_zero, mul_div_assoc] using
      (log_power_div_scale_tendsto_zero (4*K)).const_mul 8
  apply squeeze_zero' (Eventually.of_forall (fun M => by positivity)) _ hu
  filter_upwards [hlog] with M hM
  exact div_le_div_of_nonneg_right (by nlinarith [log_scales_product_bound K M hM])
    (Nat.cast_nonneg M)

theorem log_scales_eventually_disjoint (K : ℕ) :
    ∀ᶠ M : ℕ in atTop, 1 ≤ logRadius K M ∧ 0 < logWidth K M ∧
      2*logWidth K M*logRadius K M < M := by
  have hlog : ∀ᶠ M : ℕ in atTop, 1 ≤ Real.log (M : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1
  have hsmall := (log_scales_geometric_mass_tendsto_zero K).eventually_lt_const
    (show (0 : ℝ) < 1 by norm_num)
  filter_upwards [hlog, hsmall, eventually_gt_atTop (0 : ℕ)] with M hl hs hM
  refine ⟨(log_scales_positive K M hl).1, (log_scales_positive K M hl).2, ?_⟩
  have hm : (0 : ℝ) < M := by exact_mod_cast hM
  have hcast : 2*(logWidth K M : ℝ)*(logRadius K M : ℝ) < M :=
    by simpa using (div_lt_iff₀ hm).mp hs
  exact_mod_cast hcast

theorem log_scales_model_tail_tendsto_zero (K : ℕ) (hK : 0 < K) :
    Tendsto (fun M : ℕ => (logRadius K M : ℝ)^2/(2*(logWidth K M : ℝ)))
      atTop (𝓝 0) := by
  have hlog : Tendsto (fun M : ℕ => Real.log (M : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hu := ((tendsto_pow_atTop (α := ℝ) (Nat.ne_of_gt hK)).comp hlog).const_div_atTop 2
  apply squeeze_zero' (Eventually.of_forall (fun M => by positivity)) _ hu
  filter_upwards [hlog.eventually_ge_atTop 1] with M hm
  exact log_scales_model_tail_bound K M hm

theorem log_width_abel_factor_bound (K M : ℕ) (hlog : 1 ≤ Real.log (M : ℝ)) :
    1+2*Real.pi*(logWidth K M : ℝ) ≤
      (1+4*Real.pi)*(Real.log (M : ℝ))^(3*K) := by
  have hp := (ceil_power_bounds _ hlog (3*K)).2
  change (logWidth K M : ℝ) ≤ 2*(Real.log (M : ℝ))^(3*K) at hp
  have h1 : 1 ≤ (Real.log (M : ℝ))^(3*K) := one_le_pow₀ hlog
  nlinarith [Real.pi_pos]

noncomputable def normalizedAbelError (K M : ℕ) (C c : ℝ) : ℝ :=
  2*(logWidth K M : ℝ)*(logRadius K M : ℝ)*
    (2*((1+2*Real.pi*(logWidth K M : ℝ))*C*Real.exp (-c*Real.sqrt (Real.log (M : ℝ))))+
      ((1+2*Real.pi*(logWidth K M : ℝ))*C*Real.exp (-c*Real.sqrt (Real.log (M : ℝ))))^2)

noncomputable def abelErrorEnvelope (K M : ℕ) (C c : ℝ) : ℝ :=
  16*C*(1+4*Real.pi)*(Real.log (M : ℝ))^(7*K)*Real.exp (-c*Real.sqrt (Real.log (M : ℝ)))+
    8*C^2*(1+4*Real.pi)^2*(Real.log (M : ℝ))^(10*K)*
      Real.exp (-(2*c)*Real.sqrt (Real.log (M : ℝ)))

theorem normalizedAbelError_nonneg (K M : ℕ) (C c : ℝ) (hC : 0 ≤ C) :
    0 ≤ normalizedAbelError K M C c := by
  unfold normalizedAbelError
  positivity

theorem normalizedAbelError_le_envelope (K M : ℕ) (C c : ℝ)
    (hC : 0 ≤ C) (hlog : 1 ≤ Real.log (M : ℝ)) :
    normalizedAbelError K M C c ≤ abelErrorEnvelope K M C c := by
  have hpr := log_scales_product_bound K M hlog
  have hf := log_width_abel_factor_bound K M hlog
  let x := Real.log (M : ℝ)
  let t := Real.exp (-c*Real.sqrt x)
  have hx : 0 ≤ x := by dsimp [x]; linarith
  have ht : 0 ≤ t := Real.exp_nonneg _
  have hfirst :
      2*(logWidth K M : ℝ)*(logRadius K M : ℝ)*
        (2*((1+2*Real.pi*(logWidth K M : ℝ))*C*t)+
          ((1+2*Real.pi*(logWidth K M : ℝ))*C*t)^2) ≤
      2*(4*x^(4*K))*(2*(((1+4*Real.pi)*x^(3*K))*C*t)+
        (((1+4*Real.pi)*x^(3*K))*C*t)^2) := by
    rw [mul_assoc 2]
    gcongr
  unfold normalizedAbelError abelErrorEnvelope
  calc
    _ ≤ 2*(4*x^(4*K))*(2*(((1+4*Real.pi)*x^(3*K))*C*t)+
        (((1+4*Real.pi)*x^(3*K))*C*t)^2) := hfirst
    _ = _ := by
      have ht2 : t^2 = Real.exp (-(2*c)*Real.sqrt x) := by
        dsimp [t]
        rw [pow_two, ← Real.exp_add]
        congr 1
        ring
      change _ = 16*C*(1+4*Real.pi)*x^(7*K)*t+
        8*C^2*(1+4*Real.pi)^2*x^(10*K)*Real.exp (-(2*c)*Real.sqrt x)
      rw [← ht2, show 7*K=4*K+3*K by omega,
        show 10*K=4*K+(3*K)*2 by omega, pow_add, pow_add, pow_mul]
      ring

theorem abelErrorEnvelope_tendsto_zero (K : ℕ) (C c : ℝ) (hc : 0 < c) :
    Tendsto (fun M : ℕ => abelErrorEnvelope K M C c) atTop (𝓝 0) := by
  have h1 := ((log_power_sqrt_exp_decay (7*K) c hc).comp
    tendsto_natCast_atTop_atTop).const_mul (16*C*(1+4*Real.pi))
  have h2 := ((log_power_sqrt_exp_decay (10*K) (2*c) (by positivity)).comp
    tendsto_natCast_atTop_atTop).const_mul (8*C^2*(1+4*Real.pi)^2)
  simpa only [abelErrorEnvelope, Function.comp_def, mul_assoc, mul_zero, add_zero] using h1.add h2

theorem normalizedAbelError_tendsto_zero (K : ℕ) (C c : ℝ) (hC : 0 ≤ C) (hc : 0 < c) :
    Tendsto (fun M : ℕ => normalizedAbelError K M C c) atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall (fun M => normalizedAbelError_nonneg K M C c hC))
    _ (abelErrorEnvelope_tendsto_zero K C c hc)
  have hl := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1
  filter_upwards [hl] with M hM
  exact normalizedAbelError_le_envelope K M C c hC hM

noncomputable def normalizedJointBudget (K M : ℕ) (C c : ℝ) : ℝ :=
  (2/7 : ℝ)/(M : ℝ) + (logRadius K M : ℝ)^2/(2*(logWidth K M : ℝ)) +
    normalizedAbelError K M C c

theorem normalizedJointBudget_tendsto_zero (K : ℕ) (hK : 0 < K)
    (C c : ℝ) (hC : 0 ≤ C) (hc : 0 < c) :
    Tendsto (fun M : ℕ => normalizedJointBudget K M C c) atTop (𝓝 0) := by
  have h0 := (tendsto_natCast_atTop_atTop (R := ℝ)).const_div_atTop (2/7)
  have h1 := log_scales_model_tail_tendsto_zero K hK
  have h2 := normalizedAbelError_tendsto_zero K C c hC hc
  simpa only [normalizedJointBudget, add_zero] using (h0.add h1).add h2

theorem eventually_joint_scale_gate (K : ℕ) (hK : 0 < K)
    (C c : ℝ) (hC : 0 ≤ C) (hc : 0 < c) :
    ∀ᶠ M : ℕ in atTop, 0 < M ∧ 1 ≤ logRadius K M ∧ 0 < logWidth K M ∧
      2*logWidth K M*logRadius K M < M ∧ normalizedJointBudget K M C c ≤ 1/14 := by
  have hb := (normalizedJointBudget_tendsto_zero K hK C c hC hc).eventually_lt_const
    (show (0 : ℝ) < 1/14 by norm_num)
  filter_upwards [eventually_gt_atTop (0 : ℕ), log_scales_eventually_disjoint K, hb]
    with M hM hg hbudget
  exact ⟨hM, hg.1, hg.2.1, hg.2.2, hbudget.le⟩

end GoldbachCircleMethodCeilScaleEnvelopesV1864
