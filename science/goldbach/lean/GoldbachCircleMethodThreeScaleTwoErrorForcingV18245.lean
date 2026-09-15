import GoldbachCircleMethodCenteredCorrectionV184CompositionV18244

/-!
# Goldbach V1.8.245: three-scale two-error forcing

The actual principal reserve, explicit prime-power defect absorption, and
literal two-error split are transferred to the analytically compatible
three-scale cover.  Every hypothetical non-Goldbach target now forces one of
six named large-value channels with no endpoint gap.
-/

set_option autoImplicit false

namespace GoldbachCircleMethodThreeScaleTwoErrorForcingV18245

open GoldbachPurePrimeAdequacyV15
open GoldbachVonMangoldtDecompositionV16
open GoldbachPrimePowerDefectBoundV161
open GoldbachCircleMethodResidualScaleAdmissionV18196
open GoldbachCircleMethodActualResidualLargeValueTransferV18224
open GoldbachCircleMethodActualResidualExactDecompositionV18225
open GoldbachCircleMethodActualBlockInteriorPairReserveV18231
open GoldbachCircleMethodTwoScaleEvenBlockDefectReserveV1833
open GoldbachCircleMethodAdmittedDefectTwoErrorForcingV18238
open GoldbachCircleMethodThreeScaleCenteredContractCoverV18242
open GoldbachCircleMethodFiniteResiduePrefixV1866
open GoldbachCircleMethodBoundedConductorReindexV18117

/-- Literal two-channel large-value alternative at one named source scale. -/
def ScaleErrorLarge
    (M B N : ℕ) (rho : ℝ) (hR2 : 2 ≤ (B : ℝ)^rho) : Prop :=
  (M : ℝ) / 2048 ≤ ‖canonicalPrincipalResidualAt B rho hR2 (N : ℤ)‖ ∨
    (M : ℝ) / 2048 ≤ ‖canonicalCenteredErrorCorrectionAt B rho (N : ℤ)‖

/-- The admitted threshold at any source subscale `B ≤ M` pushes the target
scale beyond the fixed logarithmic defect threshold. -/
theorem target_exp_threshold_of_admitted_subscale
    (M B : ℕ) (rho : ℝ) (hrho : 0 < rho)
    (hrhoUpper : rho ≤ (1 : ℝ) / 10000)
    (hBM : B ≤ M) (hAdmitted : blockThreshold rho ≤ B) :
    Real.exp (100000000 : ℝ) ≤ (M : ℝ) := by
  have hThresholdLarge :=
    logThreshold_ge_one_hundred_million rho hrho hrhoUpper
  have hExpB : Real.exp (logThreshold rho) ≤ (B : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hAdmitted)
  have hExpLarge : Real.exp (100000000 : ℝ) ≤
      Real.exp (logThreshold rho) := Real.exp_le_exp.mpr hThresholdLarge
  have hBMReal : (B : ℝ) ≤ (M : ℝ) := by exact_mod_cast hBM
  exact hExpLarge.trans (hExpB.trans hBMReal)

/-- Each of the three analytic source scales is a true subscale of `M`. -/
theorem analytic_source_scales_le_target_scale (M : ℕ) :
    analyticLowerSourceScale M ≤ M ∧
      analyticMiddleSourceScale M ≤ M ∧
      analyticUpperSourceScale M ≤ M := by
  simp only [analyticLowerSourceScale, analyticMiddleSourceScale,
    analyticUpperSourceScale]
  omega

/-- Main endpoint-safe forcing theorem.  Every hypothetical non-Goldbach
target in the dyadic block produces a large principal residual or centered
correction at the analytic source scale selected by V1.8.242. -/
theorem evenTargetBlock_not_goldbach_forces_large_error_at_three_scale
    {K : ℕ} [NeZero K]
    (M N : ℕ) (rho : ℝ) (hM : 128 ≤ M)
    (hN : N ∈ evenTargetBlock M)
    (hrho : 0 < rho) (hrhoUpper : rho ≤ (1 : ℝ) / 10000)
    (hLow : blockThreshold rho ≤ analyticLowerSourceScale M)
    (hMiddle : blockThreshold rho ≤ analyticMiddleSourceScale M)
    (hUpper : blockThreshold rho ≤ analyticUpperSourceScale M)
    (hKLow : ∀ q : PositiveLevel
        ⌊((analyticLowerSourceScale M : ℝ) ^ rho) ^ 2⌋₊, q.val ∣ K)
    (hKMiddle : ∀ q : PositiveLevel
        ⌊((analyticMiddleSourceScale M : ℝ) ^ rho) ^ 2⌋₊, q.val ∣ K)
    (hKUpper : ∀ q : PositiveLevel
        ⌊((analyticUpperSourceScale M : ℝ) ^ rho) ^ 2⌋₊, q.val ∣ K)
    (hNot : ¬ GoldbachAt N) :
    ScaleErrorLarge M (analyticLowerSourceScale M) N rho
        (actual_scale_admission rho hrho hrhoUpper
          (analyticLowerSourceScale M) hLow).2.1 ∨
      ScaleErrorLarge M (analyticMiddleSourceScale M) N rho
        (actual_scale_admission rho hrho hrhoUpper
          (analyticMiddleSourceScale M) hMiddle).2.1 ∨
      ScaleErrorLarge M (analyticUpperSourceScale M) N rho
        (actual_scale_admission rho hrho hrhoUpper
          (analyticUpperSourceScale M) hUpper).2.1 := by
  have hScales := analytic_source_scales_le_target_scale M
  have hExpM := target_exp_threshold_of_admitted_subscale
    M (analyticLowerSourceScale M) rho hrho hrhoUpper hScales.1 hLow
  have hScale := strong_log_sq_gate_of_exp_one_hundred_million_le M hExpM
  have hRange := (mem_evenTargetBlock_iff M N).mp hN
  have hDefect : primePowerDefect N ≤ (M : ℝ) / 1024 :=
    primePowerDefect_le_target_scale_over_one_zero_two_four
      M N (by omega) hRange.2.1 hScale
  have hEven := hRange.2.2.1
  rcases evenTargetBlock_three_scale_analytic_cover M N hM hN with
      hCoverLow | hCoverMiddle | hCoverUpper
  · left
    exact one_scale_not_goldbach_forces_large_residual_or_correction
      M (analyticLowerSourceScale M) N rho hCoverLow.1
      (by
        have := hCoverLow.2.1
        simp only [analyticPairReserve] at this
        omega)
      hCoverLow.2.2.1 hEven hrho hrhoUpper hLow hKLow hDefect hNot
  · right
    left
    exact one_scale_not_goldbach_forces_large_residual_or_correction
      M (analyticMiddleSourceScale M) N rho hCoverMiddle.1
      (by
        have := hCoverMiddle.2.1
        simp only [analyticPairReserve] at this
        omega)
      hCoverMiddle.2.2.1 hEven hrho hrhoUpper hMiddle hKMiddle hDefect hNot
  · right
    right
    exact one_scale_not_goldbach_forces_large_residual_or_correction
      M (analyticUpperSourceScale M) N rho hCoverUpper.1
      (by
        have := hCoverUpper.2.1
        simp only [analyticPairReserve] at this
        omega)
      hCoverUpper.2.2.1 hEven hrho hrhoUpper hUpper hKUpper hDefect hNot

end GoldbachCircleMethodThreeScaleTwoErrorForcingV18245

