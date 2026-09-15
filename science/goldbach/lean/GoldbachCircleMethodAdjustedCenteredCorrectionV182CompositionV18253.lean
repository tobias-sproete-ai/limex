import GoldbachCircleMethodAdjustedCenteredCorrectionLiteralAdapterV18252

/-!
# Goldbach V1.8.253: adjusted centered-correction V1.8.182 composition

The active literal norm adapter is composed with the existing V1.8.182
adjusted-error theorem.  All analytic source assumptions and the active
character slot remain visible.
-/

open scoped Classical BigOperators ArithmeticFunction

set_option autoImplicit false

namespace GoldbachCircleMethodAdjustedCenteredCorrectionV182CompositionV18253

open GoldbachCircleMethodFiniteCompanionBindingV18118
open GoldbachCircleMethodLogCutoffPresieveBindingV18120
open GoldbachCircleMethodActiveExceptionalCenteringV18129
open GoldbachCircleMethodBumpDecayRadicalEnvelopeV18155
open GoldbachCircleMethodActiveCharacterRadicalErrorV18158
open GoldbachCircleMethodRadicalCorrelationTransferV18161
open GoldbachCircleMethodBadPrimeProductComparisonV18165
open GoldbachCircleMethodMertensUniformConstantsV18168
open GoldbachCircleMethodBadPrimeUniformFrequencyV18169
open GoldbachCircleMethodGlobalSieveFiniteFactorV18173
open GoldbachCircleMethodMertensProductFromHarmonicV18174
open GoldbachCircleMethodDisjointPrimeFactorCompositionV18171
open GoldbachCircleMethodDirectLambdaRadicalDominationV18178
open GoldbachCircleMethodEventualScaleActualErrorLambdaV18181
open GoldbachCircleMethodSupportedModelErrorConvolutionV18182
open GoldbachCircleMethodCanonicalBumpPrincipalFloorV18220
open GoldbachCircleMethodCanonicalBumpResidualMomentsV18222
open GoldbachCircleMethodActiveResidualExactDecompositionV18251
open GoldbachCircleMethodAdjustedCenteredCorrectionLiteralAdapterV18252

/-- Exact pointwise bound for the literal active adjusted correction.  No
exceptional-character existence statement, source estimate, or fluctuation
mass bound is constructed here. -/
theorem eventual_canonicalAdjustedCenteredErrorCorrectionAt_bound :
    ∃ CE : ℝ, 0 ≤ CE ∧ ∃ CB : ℝ, 0 ≤ CB ∧
      ∀ (D c CH : ℝ) (_hD : 0 ≤ D) (_hCH : 0 ≤ CH)
        (_hweighted : ∀ (X : ℕ), 2 ≤ X → ∀ t : ℝ, 2 ≤ t → t ≤ (X : ℝ) →
          |prefixLogMoment X t - Real.log t| ≤ D)
        (_hharmonic : ∀ (X : ℕ), 2 ≤ X → ∀ t : ℝ, 2 ≤ t → t ≤ (X : ℝ) →
          |prefixHarmonicMoment X t - Real.log (Real.log t) - c| ≤
            D / Real.log t)
        (rho : ℝ) (_hrho : 0 < rho) (_hrho1 : rho ≤ 1),
      ∃ B₀ : ℕ, ∀ {B N : ℕ} (b eta : ℝ)
        (e : CharacterSlot ⌊((B : ℝ)^rho)^2⌋₊),
        B₀ ≤ B → 5 * B ≤ 4 * N → 4 * N ≤ 7 * B → 0 ≤ b → 0 ≤ eta →
        (∀ ξ η' : ℝ,
          arithmeticCorrelation ((B : ℝ)^rho) ξ η'
              (Finset.Ioc (B / 2) B) N ≤
            CH * ((B : ℝ) / 2) * finiteSieveProduct N (B / 2) *
              goodBadProduct ((B : ℝ)^rho) ξ η' N (B / 2)) →
        (∀ n ∈ blockCarrier B,
          activeFluctuationMass ⌊((B : ℝ)^rho)^2⌋₊ B n
            ((B : ℝ) / ((B : ℝ)^rho)^4) b (blockInput B) e ≤ eta) →
        ‖canonicalAdjustedCenteredErrorCorrectionAt B rho b e (N : ℤ)‖ ≤
          CE * eta *
            ((128 * CH * (mertensProductConstant D c)^2 *
                (oneFrequencyConstant D c)^2 *
                (∫ ξ : ℝ, secondMomentDecay ξ)^2 / tenthDecayMass) *
              (B : ℝ) * arithmeticFactor N / rho^3 +
             CB * (128 * CH * (mertensProductConstant D c)^2 *
                (oneFrequencyConstant D c)^2 *
                (∫ ξ : ℝ, secondMomentDecay ξ)^2) *
              (B : ℝ) * arithmeticFactor N / rho^2) := by
  obtain ⟨CE, hCE, CB, hCB, hCore⟩ :=
    eventual_supported_actual_error_model_lambda_bound
      canonicalLogBump_hasCompactSupport canonicalLogBump_contDiff
      (fun _ hx => canonicalLogBump_zero_above_two hx)
  refine ⟨CE, hCE, CB, hCB, ?_⟩
  intro D c CH hD hCH hweighted hharmonic rho hrho hrho1
  obtain ⟨B₀, hBound⟩ :=
    hCore D c CH hD hCH hweighted hharmonic rho hrho hrho1
  refine ⟨B₀, ?_⟩
  intro B N b eta e hB₀ hLower hUpper hb heta hsource hmass
  have hMajor := hBound b eta e hB₀ hLower hUpper hb heta hsource (by
    simpa only [blockCarrier] using hmass)
  have hAdapter := norm_canonicalAdjustedCenteredErrorCorrectionAt_le_majorant
    B N rho b e (by omega)
  exact hAdapter.trans (by
    simpa only [adjustedCenteredCorrectionMajorant, blockCarrier] using hMajor)

end GoldbachCircleMethodAdjustedCenteredCorrectionV182CompositionV18253
