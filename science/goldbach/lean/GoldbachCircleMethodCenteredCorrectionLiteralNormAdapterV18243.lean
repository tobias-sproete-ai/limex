import GoldbachCircleMethodThreeScaleCenteredContractCoverV18242

/-!
# Goldbach V1.8.243: centered-correction literal norm adapter

The exact centered-error correction from V1.8.225 is reduced at a natural
target to the literal nonnegative finite majorant consumed by V1.8.184.  This
is the missing definitional adapter; all analytic source-family premises
remain outside this module.
-/

open scoped Classical BigOperators

set_option autoImplicit false

namespace GoldbachCircleMethodCenteredCorrectionLiteralNormAdapterV18243

open GoldbachCircleMethodLogCutoffPresieveBindingV18120
open GoldbachCircleMethodUncorrectedSupportedErrorConvolutionV18184
open GoldbachCircleMethodCanonicalBumpPrincipalFloorV18220
open GoldbachCircleMethodActualResidualExactDecompositionV18225
open GoldbachCircleMethodBlockPairCarrierV18227
open GoldbachCircleMethodThreeScaleCenteredContractCoverV18242

/-- Literal targetwise nonnegative majorant used by the V1.8.184
uncorrected-error theorem. -/
noncomputable def centeredCorrectionMajorant
    (B N : ℕ) (rho : ℝ) : ℝ :=
  ∑ n ∈ blockCarrier B,
    ‖supportedUncorrectedError B n ((B : ℝ)^rho) canonicalLogBump‖ *
      (‖blockInput B (N - n)‖ +
        ‖supportedPrincipalModel B (N - n) ((B : ℝ)^rho)
          canonicalLogBump‖)

/-- The exact centered-correction convolution norm is bounded by the literal
finite majorant.  The only geometric premise is `B ≤ N`, used to prevent
natural-subtraction truncation in the pair-carrier reduction. -/
theorem norm_canonicalCenteredErrorCorrectionAt_le_majorant
    (B N : ℕ) (rho : ℝ) (hBN : B ≤ N) :
    ‖canonicalCenteredErrorCorrectionAt B rho (N : ℤ)‖ ≤
      centeredCorrectionMajorant B N rho := by
  have hJN : ∀ n ∈ blockCarrier B, n ≤ N := by
    intro n hn
    simp only [blockCarrier, Finset.mem_Ioc] at hn
    omega
  have hConv := integerPairConvolution_nat_eq_pairFirstCarrier
    (blockCarrier B)
    (fun n => supportedUncorrectedError B n ((B : ℝ)^rho) canonicalLogBump)
    (fun n => blockInput B n +
      supportedPrincipalModel B n ((B : ℝ)^rho) canonicalLogBump)
    N hJN
  rw [canonicalCenteredErrorCorrectionAt, hConv]
  calc
    ‖∑ n ∈ pairFirstCarrier (blockCarrier B) N,
        supportedUncorrectedError B n ((B : ℝ)^rho) canonicalLogBump *
          (blockInput B (N - n) +
            supportedPrincipalModel B (N - n) ((B : ℝ)^rho)
              canonicalLogBump)‖
        ≤ ∑ n ∈ pairFirstCarrier (blockCarrier B) N,
          ‖supportedUncorrectedError B n ((B : ℝ)^rho) canonicalLogBump *
            (blockInput B (N - n) +
              supportedPrincipalModel B (N - n) ((B : ℝ)^rho)
                canonicalLogBump)‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ pairFirstCarrier (blockCarrier B) N,
        ‖supportedUncorrectedError B n ((B : ℝ)^rho) canonicalLogBump‖ *
          (‖blockInput B (N - n)‖ +
            ‖supportedPrincipalModel B (N - n) ((B : ℝ)^rho)
              canonicalLogBump‖) := by
      apply Finset.sum_le_sum
      intro n hn
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left
        (norm_add_le (blockInput B (N - n))
          (supportedPrincipalModel B (N - n) ((B : ℝ)^rho)
            canonicalLogBump))
        (norm_nonneg _)
    _ ≤ ∑ n ∈ blockCarrier B,
        ‖supportedUncorrectedError B n ((B : ℝ)^rho) canonicalLogBump‖ *
          (‖blockInput B (N - n)‖ +
            ‖supportedPrincipalModel B (N - n) ((B : ℝ)^rho)
              canonicalLogBump‖) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.filter_subset _ _
      · intro n _ _
        positivity
    _ = centeredCorrectionMajorant B N rho := rfl

/-- The three-scale analytic cover supplies the natural-target premise for
the adapter on whichever source scale covers the target. -/
theorem analyticCompatibleCover_norm_correction_le_majorant
    (M B N : ℕ) (rho : ℝ)
    (hCover : AnalyticCompatibleCover M B N) :
    ‖canonicalCenteredErrorCorrectionAt B rho (N : ℤ)‖ ≤
      centeredCorrectionMajorant B N rho := by
  apply norm_canonicalCenteredErrorCorrectionAt_le_majorant
  exact selected_analytic_cover_implies_source_le_target M B N hCover

end GoldbachCircleMethodCenteredCorrectionLiteralNormAdapterV18243
