import GoldbachCircleMethodActiveResidualExactDecompositionV18251

/-!
# Goldbach V1.8.252: adjusted centered-correction literal adapter

The exact adjusted centered-error convolution from V1.8.251 is reduced to
the literal finite nonnegative majorant consumed by the active-error estimate
of V1.8.182.  The character slot and coefficient remain explicit.
-/

open scoped Classical BigOperators

set_option autoImplicit false

namespace GoldbachCircleMethodAdjustedCenteredCorrectionLiteralAdapterV18252

open GoldbachCircleMethodLogCutoffPresieveBindingV18120
open GoldbachCircleMethodSupportedModelErrorConvolutionV18182
open GoldbachCircleMethodActualResidualExactDecompositionV18225
open GoldbachCircleMethodBlockPairCarrierV18227
open GoldbachCircleMethodActiveExceptionalCenteringV18129
open GoldbachCircleMethodCanonicalBumpPrincipalFloorV18220
open GoldbachCircleMethodActiveResidualExactDecompositionV18251

/-- Literal targetwise majorant for the active adjusted centered correction. -/
noncomputable def adjustedCenteredCorrectionMajorant
    (B N : ℕ) (rho b : ℝ)
    (e : CharacterSlot ⌊((B : ℝ)^rho)^2⌋₊) : ℝ :=
  ∑ n ∈ blockCarrier B,
    ‖supportedAdjustedError B n ((B : ℝ)^rho) b canonicalLogBump e‖ *
      (‖blockInput B (N - n)‖ +
        ‖supportedAdjustedModel B (N - n) ((B : ℝ)^rho)
          b canonicalLogBump e‖)

/-- The exact adjusted correction is bounded by the literal V1.8.182
majorant.  `B ≤ N` prevents natural-subtraction truncation. -/
theorem norm_canonicalAdjustedCenteredErrorCorrectionAt_le_majorant
    (B N : ℕ) (rho b : ℝ)
    (e : CharacterSlot ⌊((B : ℝ)^rho)^2⌋₊) (hBN : B ≤ N) :
    ‖canonicalAdjustedCenteredErrorCorrectionAt B rho b e (N : ℤ)‖ ≤
      adjustedCenteredCorrectionMajorant B N rho b e := by
  have hJN : ∀ n ∈ blockCarrier B, n ≤ N := by
    intro n hn
    simp only [blockCarrier, Finset.mem_Ioc] at hn
    omega
  have hConv := integerPairConvolution_nat_eq_pairFirstCarrier
    (blockCarrier B)
    (fun n => supportedAdjustedError B n ((B : ℝ)^rho) b canonicalLogBump e)
    (fun n => blockInput B n +
      supportedAdjustedModel B n ((B : ℝ)^rho) b canonicalLogBump e)
    N hJN
  rw [canonicalAdjustedCenteredErrorCorrectionAt, hConv]
  calc
    ‖∑ n ∈ pairFirstCarrier (blockCarrier B) N,
        supportedAdjustedError B n ((B : ℝ)^rho) b canonicalLogBump e *
          (blockInput B (N - n) +
            supportedAdjustedModel B (N - n) ((B : ℝ)^rho)
              b canonicalLogBump e)‖
        ≤ ∑ n ∈ pairFirstCarrier (blockCarrier B) N,
          ‖supportedAdjustedError B n ((B : ℝ)^rho) b canonicalLogBump e *
            (blockInput B (N - n) +
              supportedAdjustedModel B (N - n) ((B : ℝ)^rho)
                b canonicalLogBump e)‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ pairFirstCarrier (blockCarrier B) N,
        ‖supportedAdjustedError B n ((B : ℝ)^rho) b canonicalLogBump e‖ *
          (‖blockInput B (N - n)‖ +
            ‖supportedAdjustedModel B (N - n) ((B : ℝ)^rho)
              b canonicalLogBump e‖) := by
      apply Finset.sum_le_sum
      intro n _hn
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left
        (norm_add_le (blockInput B (N - n))
          (supportedAdjustedModel B (N - n) ((B : ℝ)^rho)
            b canonicalLogBump e))
        (norm_nonneg _)
    _ ≤ ∑ n ∈ blockCarrier B,
        ‖supportedAdjustedError B n ((B : ℝ)^rho) b canonicalLogBump e‖ *
          (‖blockInput B (N - n)‖ +
            ‖supportedAdjustedModel B (N - n) ((B : ℝ)^rho)
              b canonicalLogBump e‖) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.filter_subset _ _
      · intro n _ _
        positivity
    _ = adjustedCenteredCorrectionMajorant B N rho b e := rfl

end GoldbachCircleMethodAdjustedCenteredCorrectionLiteralAdapterV18252

