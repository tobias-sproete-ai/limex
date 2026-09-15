import GoldbachCircleMethodUniformResidueInputBridgeV1869

/-! # V1.8.70: elementary absorption of the complete prefix error budget.
No distribution theorem is supplied; no numerical common threshold is claimed.
-/
open Filter Topology
open GoldbachCircleMethodUniformResidueInputBridgeV1869
open GoldbachCircleMethodCeilScaleEnvelopesV1864
open GoldbachCircleMethodUniformMajorPrefixReductionV1865

namespace GoldbachCircleMethodPrefixBudgetAbsorptionV1870

theorem exp_sqrt_ratio_bound (M : ℕ) (d : ℝ) (hM : 0 < M)
    (hlarge : 2*(d+1) ≤ Real.sqrt (Real.log (M : ℝ))) :
    Real.exp (d*Real.sqrt (Real.log (M : ℝ)))/Real.sqrt (M : ℝ) ≤
      Real.exp (-Real.sqrt (Real.log (M : ℝ))) := by
  have hm : (0 : ℝ) < M := by exact_mod_cast hM
  have ht := Real.sqrt_nonneg (Real.log (M : ℝ))
  have hs := Real.sq_sqrt (Real.log_natCast_nonneg M)
  have he : d*Real.sqrt (Real.log (M : ℝ))-Real.log (M : ℝ)/2 ≤
      -Real.sqrt (Real.log (M : ℝ)) := by
    nlinarith [mul_le_mul_of_nonneg_right hlarge ht]
  have hexp : Real.exp (Real.log (M : ℝ)/2)=Real.sqrt (M : ℝ) := by
    rw [Real.exp_half, Real.exp_log hm]
  rw [← hexp, ← Real.exp_sub]
  exact Real.exp_le_exp.mpr he

theorem log_power_exp_div_sqrt_tendsto_zero (n : ℕ) (d : ℝ) :
    Tendsto (fun M : ℕ => (Real.log (M : ℝ))^n*
      Real.exp (d*Real.sqrt (Real.log (M : ℝ)))/Real.sqrt (M : ℝ)) atTop (𝓝 0) := by
  have ht : Tendsto (fun M : ℕ => Real.sqrt (Real.log (M : ℝ))) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hu := (log_power_sqrt_exp_decay n 1 (by norm_num)).comp tendsto_natCast_atTop_atTop
  simp only [Function.comp_def, neg_one_mul] at hu
  apply squeeze_zero' (Eventually.of_forall (fun M => by positivity)) _ hu
  filter_upwards [eventually_gt_atTop (0 : ℕ), ht.eventually_ge_atTop (2*(d+1))] with M hM hs
  simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left
    (exp_sqrt_ratio_bound M d hM hs) (pow_nonneg (Real.log_natCast_nonneg M) n)

noncomputable def smallBudgetRatio (M : ℕ) (d : ℝ) : ℝ :=
  (Real.log (M : ℝ)+1)*Real.exp (d*Real.sqrt (Real.log (M : ℝ)))/Real.sqrt (M : ℝ)

theorem smallBudgetRatio_tendsto_zero (d : ℝ) :
    Tendsto (fun M : ℕ => smallBudgetRatio M d) atTop (𝓝 0) := by
  have h := (log_power_exp_div_sqrt_tendsto_zero 1 d).add
    (log_power_exp_div_sqrt_tendsto_zero 0 d)
  simpa only [smallBudgetRatio, pow_one, pow_zero, one_mul, add_zero,
    add_mul, add_div] using h

theorem small_budget_ratio_identity (M : ℕ) (d : ℝ) (hM : 0 < M) :
    Real.sqrt (M : ℝ)*(Real.log (M : ℝ)+1) =
      smallBudgetRatio M d*prefixEnvelope M 1 d := by
  have hm : (0 : ℝ) < M := by exact_mod_cast hM
  have hs : Real.sqrt (M : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hm).ne'
  have hs2 := Real.sq_sqrt hm.le
  unfold smallBudgetRatio prefixEnvelope
  rw [show -d*Real.sqrt (Real.log (M : ℝ))= -(d*Real.sqrt (Real.log (M : ℝ))) by ring,
    Real.exp_neg]
  field_simp
  nlinarith

theorem eventually_small_budget (d : ℝ) :
    ∀ᶠ M : ℕ in atTop, Real.sqrt (M : ℝ)*(Real.log (M : ℝ)+1) ≤ prefixEnvelope M 1 d := by
  have h := (smallBudgetRatio_tendsto_zero d).eventually_lt_const (by norm_num : (0 : ℝ) < 1)
  filter_upwards [h, eventually_gt_atTop (0 : ℕ)] with M hr hM
  rw [small_budget_ratio_identity M d hM]
  simpa using mul_le_mul_of_nonneg_right hr.le (show 0 ≤ prefixEnvelope M 1 d by
    unfold prefixEnvelope; positivity)

theorem sqrt_ratio_identity (M : ℕ) (d u : ℝ) (hM : 0 < M) :
    Real.sqrt (M : ℝ)*u =
      (u*Real.exp (d*Real.sqrt (Real.log (M : ℝ)))/Real.sqrt (M : ℝ))*prefixEnvelope M 1 d := by
  have hm : (0 : ℝ) < M := by exact_mod_cast hM
  have hs : Real.sqrt (M : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hm).ne'
  have hs2 := Real.sq_sqrt hm.le
  unfold prefixEnvelope
  rw [show -d*Real.sqrt (Real.log (M : ℝ))= -(d*Real.sqrt (Real.log (M : ℝ))) by ring,
    Real.exp_neg]
  field_simp
  rw [hs2]
  ring

noncomputable def distributionRatioMajorant (K M : ℕ) (C c : ℝ) : ℝ :=
  2*C*(Real.log (M : ℝ))^K*Real.exp (-(c/4)*Real.sqrt (Real.log (M : ℝ)))

noncomputable def nonreducedRatioMajorant (K M : ℕ) (d : ℝ) : ℝ :=
  2*((Real.log (M : ℝ))^(K+1)*Real.exp (d*Real.sqrt (Real.log (M : ℝ)))/Real.sqrt (M : ℝ))+
    3*(Real.log (M : ℝ)*Real.exp (d*Real.sqrt (Real.log (M : ℝ)))/Real.sqrt (M : ℝ))

theorem distributionRatioMajorant_tendsto_zero (K : ℕ) (C c : ℝ) (hc : 0 < c) :
    Tendsto (fun M : ℕ => distributionRatioMajorant K M C c) atTop (𝓝 0) := by
  have h := ((log_power_sqrt_exp_decay K (c/4) (by positivity)).comp
    tendsto_natCast_atTop_atTop).const_mul (2*C)
  simpa only [distributionRatioMajorant, Function.comp_def, mul_zero, mul_assoc] using h

theorem nonreducedRatioMajorant_tendsto_zero (K : ℕ) (d : ℝ) :
    Tendsto (fun M : ℕ => nonreducedRatioMajorant K M d) atTop (𝓝 0) := by
  have h := ((log_power_exp_div_sqrt_tendsto_zero (K+1) d).const_mul 2).add
    ((log_power_exp_div_sqrt_tendsto_zero 1 d).const_mul 3)
  simpa only [nonreducedRatioMajorant, pow_one, mul_zero, add_zero] using h

theorem distribution_budget_bound (K M : ℕ) (C c : ℝ) (hC : 0 ≤ C)
    (hlog : 1 ≤ Real.log (M : ℝ)) :
    (logRadius K M : ℝ)*prefixEnvelope M C (c/2) ≤
      distributionRatioMajorant K M C c*prefixEnvelope M 1 (c/4) := by
  have hr := (ceil_power_bounds _ hlog K).2
  change (logRadius K M : ℝ) ≤ 2*(Real.log (M : ℝ))^K at hr
  calc
    _ ≤ (2*(Real.log (M : ℝ))^K)*prefixEnvelope M C (c/2) :=
      mul_le_mul_of_nonneg_right hr (by unfold prefixEnvelope; positivity)
    _ = _ := by
      unfold prefixEnvelope distributionRatioMajorant
      have he : Real.exp (-(c/2)*Real.sqrt (Real.log (M : ℝ))) =
          Real.exp (-(c/4)*Real.sqrt (Real.log (M : ℝ)))*
          Real.exp (-(c/4)*Real.sqrt (Real.log (M : ℝ))) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [he]
      ring

theorem nonreduced_budget_bound (K M : ℕ) (d : ℝ) (hM : 0 < M)
    (hlog : 1 ≤ Real.log (M : ℝ)) :
    ((logRadius K M : ℝ)+1+2*Real.sqrt (M : ℝ))*Real.log (M : ℝ) ≤
      nonreducedRatioMajorant K M d*prefixEnvelope M 1 d := by
  have hm : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hs : 1 ≤ Real.sqrt (M : ℝ) := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hm
  have hr := (ceil_power_bounds _ hlog K).2
  change (logRadius K M : ℝ) ≤ 2*(Real.log (M : ℝ))^K at hr
  have hpow : 0 ≤ (Real.log (M : ℝ))^K := by positivity
  have hcoef : (logRadius K M : ℝ)+1+2*Real.sqrt (M : ℝ) ≤
      (2*(Real.log (M : ℝ))^K+3)*Real.sqrt (M : ℝ) := by
    nlinarith [mul_le_mul_of_nonneg_left hs (show 0 ≤ 2*(Real.log (M : ℝ))^K by positivity)]
  calc
    _ ≤ ((2*(Real.log (M : ℝ))^K+3)*Real.sqrt (M : ℝ))*Real.log (M : ℝ) :=
      mul_le_mul_of_nonneg_right hcoef (Real.log_natCast_nonneg M)
    _ = Real.sqrt (M : ℝ)*(2*(Real.log (M : ℝ))^(K+1)+3*Real.log (M : ℝ)) := by
      rw [pow_succ]; ring
    _ = _ := by
      rw [sqrt_ratio_identity M d _ hM]
      unfold nonreducedRatioMajorant
      ring

theorem eventually_large_budget (K : ℕ) (C c : ℝ) (hC : 0 ≤ C) (hc : 0 < c) :
    ∀ᶠ M : ℕ in atTop,
      (logRadius K M : ℝ)*prefixEnvelope M C (c/2)+
        ((logRadius K M : ℝ)+1+2*Real.sqrt (M : ℝ))*Real.log (M : ℝ) ≤
          prefixEnvelope M 1 (c/4) := by
  have ht := (distributionRatioMajorant_tendsto_zero K C c hc).add
    (nonreducedRatioMajorant_tendsto_zero K (c/4))
  have hsmall := ht.eventually_lt_const (by norm_num : (0 : ℝ)+0 < 1)
  have hlog := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1
  filter_upwards [hsmall, hlog, eventually_gt_atTop (0 : ℕ)] with M hsum hl hM
  calc
    _ ≤ (distributionRatioMajorant K M C c+nonreducedRatioMajorant K M (c/4))*
        prefixEnvelope M 1 (c/4) := by
      simpa only [add_mul] using add_le_add (distribution_budget_bound K M C c hC hl)
        (nonreduced_budget_bound K M (c/4) hM hl)
    _ ≤ _ := by
      simpa using mul_le_mul_of_nonneg_right hsum.le
        (show 0 ≤ prefixEnvelope M 1 (c/4) by unfold prefixEnvelope; positivity)

theorem eventual_full_prefix_of_scale_estimate (K k₀ : ℕ) (C c : ℝ)
    (hC : 0 ≤ C) (hc : 0 < c)
    (hscale : ScaleReducedClassEstimate (K+1) k₀ C c) :
    ∀ᶠ M : ℕ in atTop, FullPrefixBound K M 1 (c/4) := by
  have hlog := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop
    ((2 : ℝ)^(K+2))
  have hsqrt := (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop
    (k₀ : ℝ)
  filter_upwards [eventually_gt_atTop (0 : ℕ), hlog, hsqrt,
    eventually_small_budget (c/4), eventually_large_budget K C c hC hc] with M hM hl hs hsmall hbig
  exact fullPrefixBound_of_scale_estimate_and_budgets K M k₀ C c 1 (c/4)
    hM hC hc.le hl hs hscale hsmall hbig

theorem uniform_major_reserve_of_scale_estimate (K k₀ : ℕ) (hK : 0 < K) (C c : ℝ)
    (hC : 0 ≤ C) (hc : 0 < c)
    (hscale : ScaleReducedClassEstimate (K+1) k₀ C c) :
    ∃ M₀ : ℕ, ∀ M ≥ M₀, ∀ N : ℕ, 4 ≤ N → N ≤ M → Even N → M ≤ 2*N →
      (M : ℝ)/14 ≤ GoldbachCircleMethodTwoScaleIntegralPartitionV1831.twoScaleMajorIntegralReal
        M (logWidth K M) (logRadius K M) N :=
  uniform_major_reserve_of_eventual_prefix K hK 1 (c/4) (by norm_num) (by positivity)
    (eventual_full_prefix_of_scale_estimate K k₀ C c hC hc hscale)

end GoldbachCircleMethodPrefixBudgetAbsorptionV1870
