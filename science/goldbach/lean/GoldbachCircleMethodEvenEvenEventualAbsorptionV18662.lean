import GoldbachCircleMethodEvenEvenChannelCompositionV18661
import GoldbachCircleMethodOddChannelEventualAbsorptionV18658

/-!
# V1.8.662: eventual absorption of the sparse even-even channel

This append-only module substitutes the unchanged project schedule
`R=ceil(log(M)^10)` and `P=8R^2` into the kernel-checked V1.8.661
even-even moment bound.  The resulting envelope is
`2^21 M log(M)^74`, hence is eventually below every positive multiple of
`M^2`.

The dense odd-odd channel is not estimated. `proof_status = NO_PROOF`.
-/
set_option autoImplicit false

open Filter Topology
open GoldbachCircleMethodExceptionalTransferV1823
open GoldbachCircleMethodTwoScaleEvenBlockDefectReserveV1833
open GoldbachCircleMethodCeilScaleEnvelopesV1864
open GoldbachCircleMethodUniformModelReserveCubicScaleV18639
open GoldbachCircleMethodEventualAnalyticInputReductionV18642
open GoldbachCircleMethodActualHalfScaleCorrelationV18177
open GoldbachCircleMethodEvenSubchannelSplitV18660
open GoldbachCircleMethodEvenEvenChannelCompositionV18661
open GoldbachCircleMethodOddChannelEventualAbsorptionV18658

namespace GoldbachCircleMethodEvenEvenEventualAbsorptionV18662

/-- The exact real envelope after substituting the unchanged project plan. -/
noncomputable def evenEvenProjectLogEnvelope (M : Nat) : Real :=
  2097152 * (M : Real) * Real.log (M : Real) ^ 74

/-- The normalized sparse-channel envelope. -/
noncomputable def normalizedEvenEvenProjectLogEnvelope (M : Nat) : Real :=
  2097152 * (Real.log (M : Real) ^ 74 / (M : Real))

/-- Exact schedule substitution in the V1.8.661 finite moment bound. -/
theorem evenEven_project_raw_envelope_le_log74
    {M : Nat} (hlog : 1 ≤ Real.log (M : Real)) :
    256 * (M : Real) * (oddProjectWidth M : Real) ^ 2 *
        (oddProjectRadius M : Real) ^ 3 * Real.log (M : Real) ^ 4 ≤
      evenEvenProjectLogEnvelope M := by
  have hR := (ceil_power_bounds (Real.log (M : Real)) hlog 10).2
  change (oddProjectRadius M : Real) ≤ 2 * Real.log (M : Real) ^ 10 at hR
  have hR7 : (oddProjectRadius M : Real) ^ 7 ≤
      (2 * Real.log (M : Real) ^ 10) ^ 7 := by
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) hR 7
  unfold oddProjectWidth oddProjectRadius evenEvenProjectLogEnvelope
    cubicModelScale
  simp only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow]
  calc
    256 * (M : Real) * (8 * (logRadius 10 M : Real) ^ 2) ^ 2 *
          (logRadius 10 M : Real) ^ 3 * Real.log (M : Real) ^ 4 =
        16384 * (M : Real) *
          ((logRadius 10 M : Real) ^ 7 * Real.log (M : Real) ^ 4) := by ring
    _ ≤ 16384 * (M : Real) *
          ((2 * Real.log (M : Real) ^ 10) ^ 7 *
            Real.log (M : Real) ^ 4) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact mul_le_mul_of_nonneg_right hR7 (by positivity)
    _ = 2097152 * (M : Real) * Real.log (M : Real) ^ 74 := by
      rw [mul_pow]
      rw [show (Real.log (M : Real) ^ 10) ^ 7 =
          Real.log (M : Real) ^ 70 by rw [← pow_mul]]
      norm_num
      rw [show 74 = 70 + 4 by norm_num, pow_add]
      ring

theorem normalizedEvenEvenProjectLogEnvelope_tendsto_zero :
    Tendsto normalizedEvenEvenProjectLogEnvelope atTop (nhds 0) := by
  have h := (log_power_div_scale_tendsto_zero 74).const_mul
    (2097152 : Real)
  change Tendsto (fun M : Nat =>
    2097152 * (Real.log (M : Real) ^ 74 / (M : Real))) atTop (nhds 0)
  simpa only [mul_zero] using h

/-- At the exact project schedule, the sparse even-even moment is eventually
below every prescribed positive fraction of `M^2`. -/
theorem evenEven_channel_project_moment_eventually_lt
    (delta : Real) (hdelta : 0 < delta) :
    ∀ᶠ M : Nat in atTop,
      negativePartSquaredMoment (evenTargetBlock M)
          (fun N => -explicitEvenEvenSubchannelDeficit M
            (oddProjectWidth M) (oddProjectRadius M) N) <
        delta * (M : Real) ^ 2 := by
  have hlog : ∀ᶠ M : Nat in atTop, 1 ≤ Real.log (M : Real) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1
  have hsmall := normalizedEvenEvenProjectLogEnvelope_tendsto_zero.eventually_lt_const hdelta
  filter_upwards [eventually_ge_atTop (16 : Nat), hlog,
      logRadius_cubic_window_eventually 10, hsmall] with M hM hl hcubic hs
  have hM2 : 2 ≤ M := by omega
  have hR : 1 ≤ oddProjectRadius M := (log_scales_positive 10 M hl).1
  have hP : 0 < oddProjectWidth M := cubicModelScale_pos _ hR
  have hscale : 2 * oddProjectWidth M * oddProjectRadius M < M :=
    cubicModelScale_window M (oddProjectRadius M) hcubic
  have hMoment :=
    negativePartSquaredMoment_neg_evenEvenSubchannelDeficit_evenTargetBlock_le
      hM2 hP hscale
  have hEnvelope := evenEven_project_raw_envelope_le_log74 hl
  have hm : (0 : Real) < M := by exact_mod_cast (show 0 < M by omega)
  change 2097152 * (Real.log (M : Real) ^ 74 / (M : Real)) < delta at hs
  have hratio :
      2097152 * Real.log (M : Real) ^ 74 < delta * (M : Real) :=
    (div_lt_iff₀ hm).mp (by simpa only [mul_div_assoc] using hs)
  have hscaled := mul_lt_mul_of_pos_left hratio hm
  calc
    negativePartSquaredMoment (evenTargetBlock M)
          (fun N => -explicitEvenEvenSubchannelDeficit M
            (oddProjectWidth M) (oddProjectRadius M) N) ≤
        256 * (M : Real) * (oddProjectWidth M : Real) ^ 2 *
          (oddProjectRadius M : Real) ^ 3 * Real.log (M : Real) ^ 4 := hMoment
    _ ≤ evenEvenProjectLogEnvelope M := hEnvelope
    _ < delta * (M : Real) ^ 2 := by
      unfold evenEvenProjectLogEnvelope
      calc
        2097152 * (M : Real) * Real.log (M : Real) ^ 74 =
            (M : Real) * (2097152 * Real.log (M : Real) ^ 74) := by ring
        _ < (M : Real) * (delta * (M : Real)) := hscaled
        _ = delta * (M : Real) ^ 2 := by ring

/-- Concrete allocation used by the next exact even-channel composition. -/
theorem evenEven_channel_project_moment_eventually_lt_one_over_12544 :
    ∀ᶠ M : Nat in atTop,
      negativePartSquaredMoment (evenTargetBlock M)
          (fun N => -explicitEvenEvenSubchannelDeficit M
            (oddProjectWidth M) (oddProjectRadius M) N) <
        (M : Real) ^ 2 / 12544 := by
  have h := evenEven_channel_project_moment_eventually_lt
    ((1 : Real) / 12544) (by norm_num)
  filter_upwards [h] with M hM
  convert hM using 1
  ring

end GoldbachCircleMethodEvenEvenEventualAbsorptionV18662
