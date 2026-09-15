import GoldbachCircleMethodEventualAnalyticInputReductionV18642
import GoldbachCircleMethodLogarithmicBlockDecayV1875

/-!
# V1.8.643: decay of the cubic-scale Chebyshev/Vaughan channel

At radius `logRadius 10 M` and width `8 * R^2`, the explicit Chebyshev fourth
moment divided by `M^3` tends to zero.  This is elementary asymptotic algebra;
it does not inhabit `RealVaughanEstimate`.

`proof_status = NO_PROOF`.
-/
set_option autoImplicit false

open Filter Topology
open GoldbachCircleMethodCeilScaleEnvelopesV1864
open GoldbachCircleMethodQuantitativeMinorEvenBlockV1874
open GoldbachCircleMethodLogarithmicBlockDecayV1875
open GoldbachCircleMethodChebyshevEnergyBudgetV1889
open GoldbachCircleMethodUniformModelReserveCubicScaleV18639

namespace GoldbachCircleMethodCubicChebyshevDecayV18643

noncomputable def cubicChebyshevScaledBudget (M : ℕ) (C : ℝ) : ℝ :=
  2 * chebyshevFourthBudget M
      (cubicModelScale (logRadius 10 M)) (logRadius 10 M) C /
    (M : ℝ) ^ 3

theorem cubicChebyshevScaledBudget_identity
    (M : ℕ) (C : ℝ) (hM : 0 < M)
    (hlog : 1 ≤ Real.log (M : ℝ)) :
    cubicChebyshevScaledBudget M C =
      6 * chebyshevConstant * C ^ 2 *
        ((Real.log (M : ℝ)) ^ 9 / (logRadius 10 M : ℝ) +
         (Real.log (M : ℝ)) ^ 9 / (M : ℝ) ^ ((2 : ℝ) / 5) +
         2 * (Real.log (M : ℝ)) ^ 9 /
           (cubicModelScale (logRadius 10 M) : ℝ)) := by
  have hm : (0 : ℝ) < M := by exact_mod_cast hM
  have hRnat := (log_scales_positive 10 M hlog).1
  have hR : (logRadius 10 M : ℝ) ≠ 0 := by
    exact_mod_cast (show logRadius 10 M ≠ 0 by omega)
  have hP : (cubicModelScale (logRadius 10 M) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (cubicModelScale_pos (logRadius 10 M) hRnat))
  have hz : (M : ℝ) ^ ((2 : ℝ) / 5) ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos hm _)
  have hprod : (M : ℝ) ^ ((8 : ℝ) / 5) *
      (M : ℝ) ^ ((2 : ℝ) / 5) = (M : ℝ) ^ 2 := by
    rw [← Real.rpow_add hm]
    norm_num
  have hpow : (M : ℝ) ^ ((8 : ℝ) / 5) =
      (M : ℝ) ^ 2 / (M : ℝ) ^ ((2 : ℝ) / 5) :=
    (eq_div_iff hz).mpr hprod
  unfold cubicChebyshevScaledBudget chebyshevFourthBudget
  rw [hpow]
  field_simp
  ring

theorem log_nine_over_radius_le_inv_log
    (M : ℕ) (hlog : 1 ≤ Real.log (M : ℝ)) :
    (Real.log (M : ℝ)) ^ 9 / (logRadius 10 M : ℝ) ≤
      1 / Real.log (M : ℝ) := by
  have hx : 0 < Real.log (M : ℝ) := by linarith
  have hr := (ceil_power_bounds (Real.log (M : ℝ)) hlog 10).1
  change (Real.log (M : ℝ)) ^ 10 ≤ (logRadius 10 M : ℝ) at hr
  have hrpos : (0 : ℝ) < logRadius 10 M := (pow_pos hx 10).trans_le hr
  rw [div_le_div_iff₀ hrpos hx]
  rw [show 10 = 9 + 1 by norm_num, pow_succ] at hr
  simpa only [one_mul] using hr

theorem log_nine_over_cubic_scale_le_inv_log
    (M : ℕ) (hlog : 1 ≤ Real.log (M : ℝ)) :
    (Real.log (M : ℝ)) ^ 9 /
        (cubicModelScale (logRadius 10 M) : ℝ) ≤
      1 / Real.log (M : ℝ) := by
  have hRnat := (log_scales_positive 10 M hlog).1
  have hRpos : (0 : ℝ) < logRadius 10 M := by exact_mod_cast (show 0 < logRadius 10 M by omega)
  have hPpos : (0 : ℝ) < cubicModelScale (logRadius 10 M) := by
    exact_mod_cast cubicModelScale_pos (logRadius 10 M) hRnat
  have hRP : (logRadius 10 M : ℝ) ≤
      (cubicModelScale (logRadius 10 M) : ℝ) := by
    unfold cubicModelScale
    simp only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow]
    calc
      (logRadius 10 M : ℝ) = (logRadius 10 M : ℝ) * 1 := by ring
      _ ≤ (logRadius 10 M : ℝ) * (logRadius 10 M : ℝ) :=
        mul_le_mul_of_nonneg_left (by exact_mod_cast hRnat) hRpos.le
      _ ≤ 8 * (logRadius 10 M : ℝ) ^ 2 := by
        nlinarith [sq_nonneg (logRadius 10 M : ℝ)]
  exact (div_le_div_of_nonneg_left (by positivity) hRpos hRP).trans
    (log_nine_over_radius_le_inv_log M hlog)

theorem cubicChebyshevScaledBudget_tendsto_zero (C : ℝ) :
    Tendsto (fun M : ℕ => cubicChebyshevScaledBudget M C) atTop (𝓝 0) := by
  have hinv : Tendsto (fun M : ℕ => 1 / Real.log (M : ℝ)) atTop (𝓝 0) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).const_div_atTop 1
  have hmiddle := log_power_over_two_fifths_tendsto_zero 9
  have hupper : Tendsto (fun M : ℕ =>
      6 * chebyshevConstant * C ^ 2 *
        (3 / Real.log (M : ℝ) +
          (Real.log (M : ℝ)) ^ 9 / (M : ℝ) ^ ((2 : ℝ) / 5)))
      atTop (𝓝 0) := by
    have h := ((hinv.const_mul 3).add hmiddle).const_mul
      (6 * chebyshevConstant * C ^ 2)
    simpa only [mul_zero, add_zero, mul_one_div] using h
  apply squeeze_zero' _ _ hupper
  · filter_upwards [eventually_gt_atTop (0 : ℕ),
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1]
      with M hM hlog
    rw [cubicChebyshevScaledBudget_identity M C hM hlog]
    have hconst : 0 ≤ chebyshevConstant := chebyshevConstant_pos.le
    positivity
  · filter_upwards [eventually_gt_atTop (0 : ℕ),
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1]
      with M hM hlog
    rw [cubicChebyshevScaledBudget_identity M C hM hlog]
    have hcoef : 0 ≤ 6 * chebyshevConstant * C ^ 2 := by
      exact mul_nonneg (mul_nonneg (by norm_num) chebyshevConstant_pos.le) (sq_nonneg C)
    apply mul_le_mul_of_nonneg_left _ hcoef
    have hR := log_nine_over_radius_le_inv_log M hlog
    have hP := log_nine_over_cubic_scale_le_inv_log M hlog
    calc
      _ ≤ 1 / Real.log (M : ℝ) +
          (Real.log (M : ℝ)) ^ 9 / (M : ℝ) ^ ((2 : ℝ) / 5) +
          2 * (1 / Real.log (M : ℝ)) := by
        rw [show 2 * (Real.log (M : ℝ)) ^ 9 /
            (cubicModelScale (logRadius 10 M) : ℝ) =
          2 * ((Real.log (M : ℝ)) ^ 9 /
            (cubicModelScale (logRadius 10 M) : ℝ)) by ring]
        exact add_le_add (add_le_add hR le_rfl)
          (mul_le_mul_of_nonneg_left hP (by norm_num : (0 : ℝ) ≤ 2))
      _ = _ := by ring

end GoldbachCircleMethodCubicChebyshevDecayV18643
