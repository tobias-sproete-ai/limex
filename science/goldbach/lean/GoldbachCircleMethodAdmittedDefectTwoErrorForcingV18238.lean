import GoldbachCircleMethodNonGoldbachBlockSourceDefectBridgeV18237
import GoldbachCircleMethodSignedTwoErrorSplitV18226

/-!
# Goldbach V1.8.238: admitted defect absorption and two-error forcing

The admitted scale is so large that the explicit Mathlib Chebyshev
prime-power defect is much smaller than the linear principal-model reserve.
Combining that fact with the exact source/model/residual/correction identity
forces every hypothetical non-Goldbach target into a large-value set for one
of the two genuine error channels, at one of the two covering source scales.

No moment bound for the centered-error correction is supplied here.
-/

set_option autoImplicit false

namespace GoldbachCircleMethodAdmittedDefectTwoErrorForcingV18238

open GoldbachPurePrimeAdequacyV15
open GoldbachVonMangoldtDecompositionV16
open GoldbachPrimePowerDefectBoundV161
open GoldbachCircleMethodResidualScaleAdmissionV18196
open GoldbachCircleMethodActualResidualLargeValueTransferV18224
open GoldbachCircleMethodActualResidualExactDecompositionV18225
open GoldbachCircleMethodSignedTwoErrorSplitV18226
open GoldbachCircleMethodActualBlockInteriorPairReserveV18231
open GoldbachCircleMethodTwoSourceScaleCoverV18232
open GoldbachCircleMethodTwoSourceScalePrincipalReserveV18233
open GoldbachCircleMethodTwoScaleEvenBlockDefectReserveV1833
open GoldbachCircleMethodQuantitativeAdmittedPrincipalReserveV18236
open GoldbachCircleMethodNonGoldbachBlockSourceDefectBridgeV18237
open GoldbachCircleMethodFiniteResiduePrefixV1866
open GoldbachCircleMethodBoundedConductorReindexV18117

/-- The very large existing admission threshold implies a strong elementary
logarithmic scale gate used only to absorb the prime-power defect. -/
theorem strong_log_sq_gate_of_exp_one_hundred_million_le
    (M : ℕ) (hLarge : Real.exp (100000000 : ℝ) ≤ (M : ℝ)) :
    4096 * (Real.log (M : ℝ)) ^ 2 ≤ Real.sqrt (M : ℝ) := by
  have hMPos : (0 : ℝ) < M := (Real.exp_pos _).trans_le hLarge
  have hLog : (100000000 : ℝ) ≤ Real.log (M : ℝ) := by
    simpa using Real.log_le_log (Real.exp_pos _) hLarge
  have hLogNonneg : 0 ≤ Real.log (M : ℝ) := by linarith
  have hxNonneg : 0 ≤ Real.log (M : ℝ) / 4 := by positivity
  have hQuadratic := Real.pow_div_factorial_le_exp
    (Real.log (M : ℝ) / 4) hxNonneg 2
  norm_num at hQuadratic
  have hLinear : 64 * Real.log (M : ℝ) ≤
      (Real.log (M : ℝ) / 4) ^ 2 / 2 := by
    nlinarith
  have hOneSide : 64 * Real.log (M : ℝ) ≤
      Real.exp (Real.log (M : ℝ) / 4) := hLinear.trans hQuadratic
  have hSquare := mul_self_le_mul_self
    (mul_nonneg (by norm_num) hLogNonneg) hOneSide
  have hHalf :
      Real.exp (Real.log (M : ℝ) / 4) *
          Real.exp (Real.log (M : ℝ) / 4) = Real.sqrt (M : ℝ) := by
    rw [← Real.exp_add]
    rw [show Real.log (M : ℝ) / 4 + Real.log (M : ℝ) / 4 =
      Real.log (M : ℝ) / 2 by ring, Real.exp_half,
      Real.exp_log hMPos]
  rw [hHalf] at hSquare
  nlinarith

/-- The explicit V1.6.1 defect estimate is at most `M/1024` under the strong
logarithmic scale gate. -/
theorem primePowerDefect_le_target_scale_over_one_zero_two_four
    (M N : ℕ) (hN : 1 ≤ N) (hNM : N ≤ M)
    (hScale : 4096 * (Real.log (M : ℝ)) ^ 2 ≤ Real.sqrt (M : ℝ)) :
    primePowerDefect N ≤ (M : ℝ) / 1024 := by
  have hBase := primePowerDefect_le_scale_ceiling M N hN hNM
  have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  have hScaled := mul_le_mul_of_nonneg_left hScale
    (Real.sqrt_nonneg (M : ℝ))
  have hSq : Real.sqrt (M : ℝ) * Real.sqrt (M : ℝ) = (M : ℝ) :=
    Real.mul_self_sqrt hM0
  rw [hSq] at hScaled
  calc
    primePowerDefect N ≤
        4 * Real.sqrt (M : ℝ) * (Real.log (M : ℝ)) ^ 2 := hBase
    _ ≤ (M : ℝ) / 1024 := by nlinarith

/-- Admission of the lower covering source scale already forces the target
scale itself beyond the threshold used in the preceding defect gate. -/
theorem target_exp_threshold_of_lower_source_admitted
    (M : ℕ) (rho : ℝ) (hrho : 0 < rho)
    (hrhoUpper : rho ≤ (1 : ℝ) / 10000)
    (hLow : blockThreshold rho ≤ lowerSourceScale M) :
    Real.exp (100000000 : ℝ) ≤ (M : ℝ) := by
  have hThresholdLarge :=
    logThreshold_ge_one_hundred_million rho hrho hrhoUpper
  have hExpLow : Real.exp (logThreshold rho) ≤
      (lowerSourceScale M : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hLow)
  have hExpLarge : Real.exp (100000000 : ℝ) ≤
      Real.exp (logThreshold rho) := Real.exp_le_exp.mpr hThresholdLarge
  have hScaleNat : lowerSourceScale M ≤ M := by
    simp only [lowerSourceScale]
    omega
  have hScaleReal : (lowerSourceScale M : ℝ) ≤ (M : ℝ) := by
    exact_mod_cast hScaleNat
  exact hExpLarge.trans (hExpLow.trans hScaleReal)

/-- One covered scale with a quarter-scale lower bound and the admitted
principal floor converts a hypothetical Goldbach failure into one of the two
literal large error channels. -/
theorem one_scale_not_goldbach_forces_large_residual_or_correction
    {K : ℕ} [NeZero K]
    (M B N : ℕ) (rho : ℝ)
    (hQuarter : M ≤ 4 * B)
    (hB : 1 ≤ B) (hInterior : HasInteriorPairReserve B N (linearPairReserve B))
    (hEven : Even N)
    (hrho : 0 < rho) (hrhoUpper : rho ≤ (1 : ℝ) / 10000)
    (hAdmitted : blockThreshold rho ≤ B)
    (hK : ∀ q : PositiveLevel ⌊((B : ℝ) ^ rho) ^ 2⌋₊, q.val ∣ K)
    (hDefect : primePowerDefect N ≤ (M : ℝ) / 1024)
    (hNot : ¬ GoldbachAt N) :
    (M : ℝ) / 2048 ≤
        ‖canonicalPrincipalResidualAt B rho
          (actual_scale_admission rho hrho hrhoUpper B hAdmitted).2.1 (N : ℤ)‖ ∨
      (M : ℝ) / 2048 ≤
        ‖canonicalCenteredErrorCorrectionAt B rho (N : ℤ)‖ := by
  have hB16 : 16 ≤ B := by
    have hThresholdLarge :=
      logThreshold_ge_one_hundred_million rho hrho hrhoUpper
    have hExpThreshold : Real.exp (logThreshold rho) ≤ (B : ℝ) :=
      (Nat.le_ceil _).trans (by exact_mod_cast hAdmitted)
    have hExpLarge : Real.exp (100000000 : ℝ) ≤
        Real.exp (logThreshold rho) := Real.exp_le_exp.mpr hThresholdLarge
    have h16Exp : (16 : ℝ) < Real.exp (100000000 : ℝ) := by
      have h := Real.add_one_lt_exp
        (show (100000000 : ℝ) ≠ 0 by norm_num)
      linarith
    exact_mod_cast (h16Exp.trans_le (hExpLarge.trans hExpThreshold)).le
  have htPos : 1 ≤ linearPairReserve B := by
    simp only [linearPairReserve]
    omega
  have hGeometry := blockPair_geometry_of_interior_reserve
    B N (linearPairReserve B) hB htPos hInterior
  have hBN : B ≤ N := hGeometry.1
  have hModelFloor := canonicalPrincipalModelAt_real_floor_of_interior_reserve
    B N (linearPairReserve B) rho
    (one_lt_power_of_admitted rho hrho hrhoUpper B hAdmitted)
    hB htPos hInterior hEven hK
  have hScaleFloor := sourceScaleFloor_gt_one_twenty_eighth_of_admitted_scale
    rho hrho hrhoUpper B hAdmitted
  have hQuarterReal : (M : ℝ) / 512 ≤ (B : ℝ) / 128 := by
    have hCast : (M : ℝ) ≤ 4 * (B : ℝ) := by exact_mod_cast hQuarter
    linarith
  have hModel : (M : ℝ) / 512 ≤
      (canonicalPrincipalModelAt B rho (N : ℤ)).re :=
    le_of_lt (hQuarterReal.trans_lt (hScaleFloor.trans_le hModelFloor))
  have hSource : (canonicalBlockSourceAt B (N : ℤ)).re ≤
      (M : ℝ) / 1024 :=
    (canonicalBlockSourceAt_re_le_primePowerDefect_of_not_goldbachAt
      B N hBN hNot).trans hDefect
  have hGap : 2 * ((M : ℝ) / 2048) ≤
      (M : ℝ) / 512 - (M : ℝ) / 1024 := by
    ring_nf
    exact le_rfl
  exact canonical_one_of_two_errors_large_of_real_gap B rho
    (actual_scale_admission rho hrho hrhoUpper B hAdmitted).2.1 (N : ℤ)
    ((M : ℝ) / 1024) ((M : ℝ) / 512) ((M : ℝ) / 2048)
    hSource hModel hGap

/-- Main forcing theorem for the repaired two-scale geometry.  Every
hypothetical non-Goldbach target in the dyadic block forces a residual or a
centered-error correction of size at least `M/2048` on the source scale that
actually covers that target. -/
theorem evenTargetBlock_not_goldbach_forces_large_error_at_covering_scale
    {K : ℕ} [NeZero K]
    (M N : ℕ) (rho : ℝ) (hM : 37 ≤ M)
    (hN : N ∈ evenTargetBlock M)
    (hrho : 0 < rho) (hrhoUpper : rho ≤ (1 : ℝ) / 10000)
    (hLow : blockThreshold rho ≤ lowerSourceScale M)
    (hHigh : blockThreshold rho ≤ upperSourceScale M)
    (hKLow : ∀ q : PositiveLevel
        ⌊((lowerSourceScale M : ℝ) ^ rho) ^ 2⌋₊, q.val ∣ K)
    (hKHigh : ∀ q : PositiveLevel
        ⌊((upperSourceScale M : ℝ) ^ rho) ^ 2⌋₊, q.val ∣ K)
    (hNot : ¬ GoldbachAt N) :
    ((M : ℝ) / 2048 ≤
        ‖canonicalPrincipalResidualAt (lowerSourceScale M) rho
          (actual_scale_admission rho hrho hrhoUpper
            (lowerSourceScale M) hLow).2.1 (N : ℤ)‖ ∨
      (M : ℝ) / 2048 ≤
        ‖canonicalCenteredErrorCorrectionAt
          (lowerSourceScale M) rho (N : ℤ)‖) ∨
    ((M : ℝ) / 2048 ≤
        ‖canonicalPrincipalResidualAt (upperSourceScale M) rho
          (actual_scale_admission rho hrho hrhoUpper
            (upperSourceScale M) hHigh).2.1 (N : ℤ)‖ ∨
      (M : ℝ) / 2048 ≤
        ‖canonicalCenteredErrorCorrectionAt
          (upperSourceScale M) rho (N : ℤ)‖) := by
  have hExpM := target_exp_threshold_of_lower_source_admitted
    M rho hrho hrhoUpper hLow
  have hScale := strong_log_sq_gate_of_exp_one_hundred_million_le M hExpM
  have hDefect : primePowerDefect N ≤ (M : ℝ) / 1024 := by
    have hRange := (mem_evenTargetBlock_iff M N).mp hN
    exact primePowerDefect_le_target_scale_over_one_zero_two_four
      M N (by omega) hRange.2.1 hScale
  have hQuarter := target_scale_quarter_le_source_scales M (by omega)
  have hEven := ((mem_evenTargetBlock_iff M N).mp hN).2.2.1
  rcases evenTargetBlock_two_source_scale_cover M N (by omega) hN with
      hCoverLow | hCoverHigh
  · exact Or.inl (one_scale_not_goldbach_forces_large_residual_or_correction
      M (lowerSourceScale M) N rho hQuarter.1
      (by simp only [lowerSourceScale]; omega) hCoverLow.2 hEven
      hrho hrhoUpper hLow hKLow hDefect hNot)
  · exact Or.inr (one_scale_not_goldbach_forces_large_residual_or_correction
      M (upperSourceScale M) N rho hQuarter.2
      (by simp only [upperSourceScale]; omega) hCoverHigh.2 hEven
      hrho hrhoUpper hHigh hKHigh hDefect hNot)

end GoldbachCircleMethodAdmittedDefectTwoErrorForcingV18238
