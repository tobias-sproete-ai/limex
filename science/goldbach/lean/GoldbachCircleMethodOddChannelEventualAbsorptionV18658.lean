import GoldbachCircleMethodOddChannelMomentV18657
import GoldbachCircleMethodCubicChebyshevDecayV18643
import GoldbachCircleMethodActualHalfScaleCorrelationV18177

/-!
# V1.8.658: eventual absorption of the exact odd channel

This append-only module instantiates the exact V1.8.657 odd-channel moment at
the project schedule `R = ceil(log(M)^10)` and `P = 8 R^2`.  The resulting
finite moment is bounded by `2^27 M log(M)^74`, hence is eventually smaller
than every positive multiple of `M^2`.

Only the odd Jordan-parity channel is absorbed.  The even channel is not
estimated, so the total deficit premise of V1.8.654 remains open.

`proof_status = NO_PROOF`.
-/
set_option autoImplicit false

open Filter Topology
open GoldbachCircleMethodExceptionalTransferV1823
open GoldbachCircleMethodTwoScaleEvenBlockDefectReserveV1833
open GoldbachCircleMethodCeilScaleEnvelopesV1864
open GoldbachCircleMethodUniformModelReserveCubicScaleV18639
open GoldbachCircleMethodEventualAnalyticInputReductionV18642
open GoldbachCircleMethodActualHalfScaleCorrelationV18177
open GoldbachCircleMethodExplicitJordanParitySplitV18652
open GoldbachCircleMethodOddChannelCompositionV18656
open GoldbachCircleMethodOddChannelMomentV18657

namespace GoldbachCircleMethodOddChannelEventualAbsorptionV18658

/-- The fixed project radius for the odd-channel absorption. -/
noncomputable def oddProjectRadius (M : Nat) : Nat := logRadius 10 M

/-- The fixed cubic project width paired with `oddProjectRadius`. -/
noncomputable def oddProjectWidth (M : Nat) : Nat :=
  cubicModelScale (oddProjectRadius M)

/-- The elementary real envelope after substituting the project schedule. -/
noncomputable def oddProjectLogEnvelope (M : Nat) : Real :=
  134217728 * (M : Real) * Real.log (M : Real) ^ 74

/-- The normalized envelope which tends to zero. -/
noncomputable def normalizedOddProjectLogEnvelope (M : Nat) : Real :=
  134217728 * (Real.log (M : Real) ^ 74 / (M : Real))

/-- Exact schedule substitution: the V1.8.657 raw bound is at most the
`2^27 M log(M)^74` envelope once `M >= 16` and `log M >= 1`. -/
theorem odd_project_raw_envelope_le_log74
    {M : Nat} (hM : 16 ≤ M) (hlog : 1 ≤ Real.log (M : Real)) :
    1024 * (M : Real) * (oddProjectWidth M : Real) ^ 2 *
        (oddProjectRadius M : Real) ^ 3 *
          Real.log ((2 * M : Nat) : Real) ^ 4 ≤
      oddProjectLogEnvelope M := by
  have hR := (ceil_power_bounds (Real.log (M : Real)) hlog 10).2
  change (oddProjectRadius M : Real) ≤ 2 * Real.log (M : Real) ^ 10 at hR
  have hR7 : (oddProjectRadius M : Real) ^ 7 ≤
      (2 * Real.log (M : Real) ^ 10) ^ 7 := by
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) hR 7
  have hlog2 := double_window_log_upper_bound hM
  have hlog2nonneg : 0 ≤ Real.log ((2 * M : Nat) : Real) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ 2 * M by omega))
  have hlog4 : Real.log ((2 * M : Nat) : Real) ^ 4 ≤
      (2 * Real.log (M : Real)) ^ 4 := by
    exact pow_le_pow_left₀ hlog2nonneg hlog2 4
  have hprod :
      (oddProjectRadius M : Real) ^ 7 *
          Real.log ((2 * M : Nat) : Real) ^ 4 ≤
        (2 * Real.log (M : Real) ^ 10) ^ 7 *
          (2 * Real.log (M : Real)) ^ 4 := by
    exact mul_le_mul hR7 hlog4 (by positivity) (by positivity)
  unfold oddProjectWidth oddProjectLogEnvelope cubicModelScale
  simp only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow]
  have hprod' :
      (oddProjectRadius M : Real) ^ 7 *
          Real.log (2 * (M : Real)) ^ 4 ≤
        (2 * Real.log (M : Real) ^ 10) ^ 7 *
          (2 * Real.log (M : Real)) ^ 4 := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using hprod
  calc
    1024 * (M : Real) * (8 * (oddProjectRadius M : Real) ^ 2) ^ 2 *
          (oddProjectRadius M : Real) ^ 3 *
            Real.log (2 * (M : Real)) ^ 4 =
        65536 * (M : Real) *
          ((oddProjectRadius M : Real) ^ 7 *
            Real.log (2 * (M : Real)) ^ 4) := by ring
    _ ≤ 65536 * (M : Real) *
          ((2 * Real.log (M : Real) ^ 10) ^ 7 *
            (2 * Real.log (M : Real)) ^ 4) := by
      exact mul_le_mul_of_nonneg_left hprod' (by positivity)
    _ = 134217728 * (M : Real) * Real.log (M : Real) ^ 74 := by
      rw [mul_pow, mul_pow]
      rw [show (Real.log (M : Real) ^ 10) ^ 7 =
          Real.log (M : Real) ^ 70 by
        rw [← pow_mul]]
      norm_num
      rw [show 74 = 70 + 4 by norm_num, pow_add]
      ring

/-- The normalized project envelope tends to zero. -/
theorem normalizedOddProjectLogEnvelope_tendsto_zero :
    Tendsto normalizedOddProjectLogEnvelope atTop (nhds 0) := by
  have h := (log_power_div_scale_tendsto_zero 74).const_mul
    (134217728 : Real)
  change Tendsto (fun M : Nat =>
    134217728 * (Real.log (M : Real) ^ 74 / (M : Real))) atTop (nhds 0)
  simpa only [mul_zero] using h

/-- At the exact project schedule, the odd-channel moment is eventually below
every prescribed positive fraction of `M^2`. -/
theorem odd_channel_project_moment_eventually_lt
    (delta : Real) (hdelta : 0 < delta) :
    ∀ᶠ M : Nat in atTop,
      negativePartSquaredMoment (evenTargetBlock M)
          (fun N => -explicitOddChannelDeficit M
            (oddProjectWidth M) (oddProjectRadius M) N) <
        delta * (M : Real) ^ 2 := by
  have hlog : ∀ᶠ M : Nat in atTop, 1 ≤ Real.log (M : Real) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1
  have hsmall := normalizedOddProjectLogEnvelope_tendsto_zero.eventually_lt_const hdelta
  filter_upwards [eventually_ge_atTop (16 : Nat), hlog,
      logRadius_cubic_window_eventually 10, hsmall] with M hM hl hcubic hs
  have hM2 : 2 ≤ M := by omega
  have hR : 1 ≤ oddProjectRadius M := (log_scales_positive 10 M hl).1
  have hP : 0 < oddProjectWidth M := cubicModelScale_pos _ hR
  have hscale : 2 * oddProjectWidth M * oddProjectRadius M < M :=
    cubicModelScale_window M (oddProjectRadius M) hcubic
  have hMoment :=
    negativePartSquaredMoment_neg_oddChannelDeficit_evenTargetBlock_le
      hM2 hP hscale
  have hEnvelope := odd_project_raw_envelope_le_log74 hM hl
  have hm : (0 : Real) < M := by exact_mod_cast (show 0 < M by omega)
  change 134217728 * (Real.log (M : Real) ^ 74 / (M : Real)) < delta at hs
  have hratio :
      134217728 * Real.log (M : Real) ^ 74 < delta * (M : Real) :=
    (div_lt_iff₀ hm).mp (by simpa only [mul_div_assoc] using hs)
  have hscaled := mul_lt_mul_of_pos_left hratio hm
  calc
    negativePartSquaredMoment (evenTargetBlock M)
          (fun N => -explicitOddChannelDeficit M
            (oddProjectWidth M) (oddProjectRadius M) N) ≤
        1024 * (M : Real) * (oddProjectWidth M : Real) ^ 2 *
          (oddProjectRadius M : Real) ^ 3 *
            Real.log ((2 * M : Nat) : Real) ^ 4 := hMoment
    _ ≤ oddProjectLogEnvelope M := hEnvelope
    _ < delta * (M : Real) ^ 2 := by
      unfold oddProjectLogEnvelope
      calc
        134217728 * (M : Real) * Real.log (M : Real) ^ 74 =
            (M : Real) * (134217728 * Real.log (M : Real) ^ 74) := by ring
        _ < (M : Real) * (delta * (M : Real)) := hscaled
        _ = delta * (M : Real) ^ 2 := by ring

/-- The exact composition reserve threshold used downstream. -/
theorem odd_channel_project_moment_eventually_lt_one_over_3136 :
    ∀ᶠ M : Nat in atTop,
      negativePartSquaredMoment (evenTargetBlock M)
          (fun N => -explicitOddChannelDeficit M
            (oddProjectWidth M) (oddProjectRadius M) N) <
        (M : Real) ^ 2 / 3136 := by
  have h := odd_channel_project_moment_eventually_lt
    ((1 : Real) / 3136) (by norm_num)
  filter_upwards [h] with M hM
  convert hM using 1
  ring

/-- The coarser project threshold requested by the earlier transfer layer. -/
theorem odd_channel_project_moment_eventually_lt_one_over_784 :
    ∀ᶠ M : Nat in atTop,
      negativePartSquaredMoment (evenTargetBlock M)
          (fun N => -explicitOddChannelDeficit M
            (oddProjectWidth M) (oddProjectRadius M) N) <
        (M : Real) ^ 2 / 784 := by
  have h := odd_channel_project_moment_eventually_lt
    ((1 : Real) / 784) (by norm_num)
  filter_upwards [h] with M hM
  convert hM using 1
  ring

end GoldbachCircleMethodOddChannelEventualAbsorptionV18658
