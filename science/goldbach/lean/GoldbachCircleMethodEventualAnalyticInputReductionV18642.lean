import GoldbachCircleMethodCubicScalePrefixInhabitationV18641

/-!
# V1.8.642: eventual exact budget from the two named analytic source inputs

All elementary scale gates and the full-prefix adapter are discharged
eventually.  The resulting exception budget depends only on two visible
number-theoretic premises: a reduced-residue Siegel--Walfisz-shaped estimate
and the source-shaped real Vaughan estimate.

Neither premise is inhabited here.  No unconditional exceptional-set bound,
exception-set emptiness, or Goldbach theorem is supplied.

`proof_status = NO_PROOF`.
-/
set_option autoImplicit false

open scoped BigOperators Classical
open Filter Topology
open GoldbachPurePrimeAdequacyV15
open GoldbachCircleMethodExceptionalTransferV1823
open GoldbachCircleMethodTwoScaleEvenBlockDefectReserveV1833
open GoldbachCircleMethodCeilScaleEnvelopesV1864
open GoldbachCircleMethodUniformMajorPrefixReductionV1865
open GoldbachCircleMethodUniformResidueInputBridgeV1869
open GoldbachCircleMethodPrefixBudgetAbsorptionV1870
open GoldbachCircleMethodRealApproximationMinorAdapterV1873
open GoldbachCircleMethodChebyshevEnergyBudgetV1889
open GoldbachCircleMethodMajorOperatorErrorEnergyV18634
open GoldbachCircleMethodUniformModelReserveCubicScaleV18639
open GoldbachCircleMethodCubicScalePrefixInhabitationV18641

namespace GoldbachCircleMethodEventualAnalyticInputReductionV18642

/-- The cubic model window holds eventually for every fixed logarithmic
radius exponent. -/
theorem logRadius_cubic_window_eventually (K : ℕ) :
    ∀ᶠ M : ℕ in atTop, 16 * (logRadius K M) ^ 3 < M := by
  have hlog : ∀ᶠ M : ℕ in atTop, 1 ≤ Real.log (M : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1
  have hratio : Tendsto (fun M : ℕ =>
      128 * (Real.log (M : ℝ)) ^ (3 * K) / (M : ℝ)) atTop (𝓝 0) := by
    simpa only [mul_zero, mul_div_assoc] using
      (log_power_div_scale_tendsto_zero (3 * K)).const_mul 128
  have hsmall := hratio.eventually_lt_const (by norm_num : (0 : ℝ) < 1)
  filter_upwards [hlog, hsmall, eventually_gt_atTop (0 : ℕ)] with M hl hs hM
  have hr := (ceil_power_bounds (Real.log (M : ℝ)) hl K).2
  change (logRadius K M : ℝ) ≤ 2 * (Real.log (M : ℝ)) ^ K at hr
  have hr3 : (logRadius K M : ℝ) ^ 3 ≤
      (2 * (Real.log (M : ℝ)) ^ K) ^ 3 := by
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) hr 3
  have hupper : 16 * (logRadius K M : ℝ) ^ 3 ≤
      128 * (Real.log (M : ℝ)) ^ (3 * K) := by
    calc
      _ ≤ 16 * (2 * (Real.log (M : ℝ)) ^ K) ^ 3 :=
        mul_le_mul_of_nonneg_left hr3 (by norm_num)
      _ = _ := by rw [pow_mul]; ring
  have hm : (0 : ℝ) < M := by exact_mod_cast hM
  have hcast : 16 * (logRadius K M : ℝ) ^ 3 < (M : ℝ) := by
    have hs' : 128 * (Real.log (M : ℝ)) ^ (3 * K) < (M : ℝ) :=
      (div_lt_one hm).mp hs
    exact hupper.trans_lt hs'
  exact_mod_cast hcast

/-- The prime-power defect threshold used by the exact target detector is
eventually satisfied. -/
theorem defect_scale_gate_eventually :
    ∀ᶠ M : ℕ in atTop,
      112 * (Real.log (M : ℝ)) ^ 2 ≤ Real.sqrt (M : ℝ) := by
  have hratio := log_power_exp_div_sqrt_tendsto_zero 2 0
  have hsmall := hratio.eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 112)
  filter_upwards [hsmall, eventually_gt_atTop (0 : ℕ)] with M hs hM
  have hm : (0 : ℝ) < M := by exact_mod_cast hM
  have hsqrt : 0 < Real.sqrt (M : ℝ) := Real.sqrt_pos.mpr hm
  simp only [zero_mul, Real.exp_zero, mul_one] at hs
  rw [div_lt_iff₀ hsqrt] at hs
  nlinarith

/-- The exact support-sensitive exception budget eventually follows from the
two named analytic source contracts.  All elementary and adapter obligations
have disappeared from the final signature. -/
theorem eventually_exception_budget_of_source_inputs
    (K k₀ : ℕ) (CSW c CV : ℝ)
    (hCSW : 0 ≤ CSW) (hc : 0 < c)
    (hSW : ScaleReducedClassEstimate (K + 1) k₀ CSW c)
    (hCV : 0 ≤ CV) (hV : RealVaughanEstimate CV) :
    ∀ᶠ M : ℕ in atTop,
      ((((evenTargetBlock M).filter (fun N => ¬ GoldbachAt N)).card : ℝ) *
          ((M : ℝ) / 28) ^ 2) ≤
        2 * ((majorOperatorErrorEnvelope M
            (cubicPrefixArcEnvelope K M 1 (c / 4))) ^ 2 *
          (2 * (cubicModelScale (logRadius K M) : ℝ) *
            (logRadius K M : ℝ) ^ 2 / (M : ℝ))) +
          2 * chebyshevFourthBudget M
            (cubicModelScale (logRadius K M)) (logRadius K M) CV := by
  have hprefix := eventual_full_prefix_of_scale_estimate
    K k₀ CSW c hCSW hc hSW
  have hlog : ∀ᶠ M : ℕ in atTop, 1 ≤ Real.log (M : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1
  filter_upwards [eventually_ge_atTop (32 : ℕ), hlog,
      logRadius_cubic_window_eventually K, defect_scale_gate_eventually,
      hprefix] with M hM hl hcubic hScale hp
  have hR := (log_scales_positive K M hl).1
  exact exception_card_mul_threshold_sq_le_cubic_prefix_budget
    K 1 (c / 4) CV (by norm_num) hCV hV M hM hR hcubic hScale hp

end GoldbachCircleMethodEventualAnalyticInputReductionV18642
