import GoldbachCircleMethodQuantitativeMinorEvenBlockV1874

/-! # V1.8.75: decay of the exact finite budget on the shared logarithmic schedule.
No analytic distribution input is proved by this asymptotic algebra.
-/
set_option autoImplicit false
open scoped BigOperators Classical
open Filter Topology
open GoldbachCircleMethodCeilScaleEnvelopesV1864
open GoldbachCircleMethodQuantitativeMinorEvenBlockV1874
open GoldbachCircleMethodRealApproximationMinorAdapterV1873
open GoldbachCircleMethodArithmeticProgressionInputMatchV1871
open GoldbachCircleMethodTwoScaleEvenBlockDefectReserveV1833
open GoldbachPurePrimeAdequacyV15

namespace GoldbachCircleMethodLogarithmicBlockDecayV1875

noncomputable def scaledBudget (A M : ℕ) (C : ℝ) : ℝ :=
  784*fourthMomentBudget M (logWidth (A+11) M) (logRadius (A+11) M) C /
    (M : ℝ)^2 * (Real.log (M : ℝ))^A / (M : ℝ)

theorem scaledBudget_identity (A M : ℕ) (C : ℝ) (hM : 0<M)
    (hlog : 1≤Real.log (M : ℝ)) :
    scaledBudget A M C =
      2352*C^2 * ((Real.log (M : ℝ))^(A+10)/(logRadius (A+11) M : ℝ) +
        (Real.log (M : ℝ))^(A+10)/(M : ℝ)^((2 : ℝ)/5) +
        2*(Real.log (M : ℝ))^(A+10)/(logWidth (A+11) M : ℝ)) := by
  have hm : (0 : ℝ)<M := by exact_mod_cast hM
  have hr : (logRadius (A+11) M : ℝ)≠0 := by
    have h := (log_scales_positive (A+11) M hlog).1
    exact_mod_cast (show logRadius (A+11) M ≠ 0 by omega)
  have hp : (logWidth (A+11) M : ℝ)≠0 := by
    have h := (log_scales_positive (A+11) M hlog).2
    exact_mod_cast (Nat.ne_of_gt h)
  have hz : (M : ℝ)^((2 : ℝ)/5)≠0 := ne_of_gt (Real.rpow_pos_of_pos hm _)
  have hprod : (M : ℝ)^((8 : ℝ)/5)*(M : ℝ)^((2 : ℝ)/5)=(M : ℝ)^2 := by
    rw [← Real.rpow_add hm]
    norm_num
  have hpow : (M : ℝ)^((8 : ℝ)/5)=(M : ℝ)^2/(M : ℝ)^((2 : ℝ)/5) :=
    (eq_div_iff hz).mpr hprod
  unfold scaledBudget fourthMomentBudget
  rw [hpow, pow_add]
  field_simp
  ring

theorem log_power_over_radius_le_inv_log (A M : ℕ) (hlog : 1≤Real.log (M : ℝ)) :
    (Real.log (M : ℝ))^(A+10)/(logRadius (A+11) M : ℝ) ≤ 1/Real.log (M : ℝ) := by
  have hx : 0<Real.log (M : ℝ) := by linarith
  have hr := (ceil_power_bounds (Real.log (M : ℝ)) hlog (A+11)).1
  change (Real.log (M : ℝ))^(A+11)≤(logRadius (A+11) M : ℝ) at hr
  have hrpos : (0 : ℝ)<logRadius (A+11) M := (pow_pos hx _).trans_le hr
  rw [div_le_div_iff₀ hrpos hx]
  rw [show A+11=(A+10)+1 by omega, pow_succ] at hr
  simpa only [one_mul] using hr

theorem log_power_over_width_le_inv_log (A M : ℕ) (hlog : 1≤Real.log (M : ℝ)) :
    (Real.log (M : ℝ))^(A+10)/(logWidth (A+11) M : ℝ) ≤ 1/Real.log (M : ℝ) := by
  have hx : 0<Real.log (M : ℝ) := by linarith
  have hp := (ceil_power_bounds (Real.log (M : ℝ)) hlog (3*(A+11))).1
  change (Real.log (M : ℝ))^(3*(A+11))≤(logWidth (A+11) M : ℝ) at hp
  have hpow : (Real.log (M : ℝ))^(A+11)≤(Real.log (M : ℝ))^(3*(A+11)) :=
    pow_le_pow_right₀ hlog (by omega)
  have hr := hpow.trans hp
  have hrpos : (0 : ℝ)<logWidth (A+11) M := (pow_pos hx _).trans_le hr
  rw [div_le_div_iff₀ hrpos hx]
  rw [show A+11=(A+10)+1 by omega, pow_succ] at hr
  simpa only [one_mul] using hr

theorem log_power_over_two_fifths_tendsto_zero (n : ℕ) :
    Tendsto (fun M : ℕ => (Real.log (M : ℝ))^n/(M : ℝ)^((2 : ℝ)/5)) atTop (𝓝 0) := by
  have h := (isLittleO_log_rpow_rpow_atTop (n : ℝ)
    (show (0 : ℝ)<2/5 by norm_num)).tendsto_div_nhds_zero
  simpa only [Function.comp_def, Real.rpow_natCast] using h.comp tendsto_natCast_atTop_atTop

theorem scaledBudget_tendsto_zero (A : ℕ) (C : ℝ) :
    Tendsto (fun M : ℕ => scaledBudget A M C) atTop (𝓝 0) := by
  have hinv : Tendsto (fun M : ℕ => 1/Real.log (M : ℝ)) atTop (𝓝 0) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).const_div_atTop 1
  have hupper : Tendsto (fun M : ℕ => 2352*C^2 *
      (3/Real.log (M : ℝ)+(Real.log (M : ℝ))^(A+10)/(M : ℝ)^((2 : ℝ)/5)))
      atTop (𝓝 0) := by
    have h := ((hinv.const_mul 3).add (log_power_over_two_fifths_tendsto_zero (A+10))).const_mul (2352*C^2)
    simpa only [mul_zero, add_zero, mul_one_div] using h
  apply squeeze_zero' _ _ hupper
  · filter_upwards [eventually_gt_atTop (0 : ℕ),
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1] with M hm hl
    rw [scaledBudget_identity A M C hm hl]
    positivity
  · filter_upwards [eventually_gt_atTop (0 : ℕ),
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1] with M hm hl
    rw [scaledBudget_identity A M C hm hl]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have hr := log_power_over_radius_le_inv_log A M hl
    have hp := log_power_over_width_le_inv_log A M hl
    simp only [div_eq_mul_inv] at hr hp ⊢
    linarith

theorem eventual_evenBlock_log_decay_of_two_analytic_inputs
    (A k₀ : ℕ) (Csw csw Cv : ℝ) (hCsw : 0 ≤ Csw) (hcsw : 0 < csw) (hCv : 0 ≤ Cv)
    (hAP : ScaleAPEstimate (A+12) k₀ Csw csw) (hV : RealVaughanEstimate Cv) :
    ∃ M₀ : ℕ, ∀ M ≥ M₀,
      (((evenTargetBlock M).filter (fun N => ¬ GoldbachAt N)).card : ℝ) ≤
        (M : ℝ)/(Real.log (M : ℝ))^A := by
  obtain ⟨M₁, hb⟩ := eventual_evenBlock_budget_of_two_analytic_inputs
    (A+11) k₀ (by omega) Csw csw Cv hCsw hcsw hCv
      (by simpa only [Nat.add_assoc] using hAP) hV
  have hsmall := (scaledBudget_tendsto_zero A Cv).eventually_lt_const
    (show (0 : ℝ)<1 by norm_num)
  have hev : ∀ᶠ M : ℕ in atTop,
      (((evenTargetBlock M).filter (fun N => ¬ GoldbachAt N)).card : ℝ) ≤
        (M : ℝ)/(Real.log (M : ℝ))^A := by
    filter_upwards [hsmall, eventually_ge_atTop M₁, eventually_gt_atTop (0 : ℕ),
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1]
        with M hs hM₁ hM hl
    change 1 ≤ Real.log (M : ℝ) at hl
    have hm : (0 : ℝ)<M := by exact_mod_cast hM
    have hp : 0<(Real.log (M : ℝ))^A := pow_pos (by linarith) _
    have hprod := (div_le_iff₀ hm).mp (show
      784*fourthMomentBudget M (logWidth (A+11) M) (logRadius (A+11) M) Cv /
        (M : ℝ)^2 * (Real.log (M : ℝ))^A / (M : ℝ) ≤ 1 from hs.le)
    apply (hb M hM₁).trans
    apply (le_div_iff₀ hp).mpr
    simpa only [one_mul] using hprod
  exact eventually_atTop.mp hev

end GoldbachCircleMethodLogarithmicBlockDecayV1875
