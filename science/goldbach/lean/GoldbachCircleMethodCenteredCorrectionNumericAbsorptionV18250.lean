import GoldbachCircleMethodConditionalThreeScaleExceptionBoundV18249

/-!
# Goldbach V1.8.250: centered-correction numeric absorption

The exact V1.8.244 centered-correction majorant is given a name and connected
to the `M/2048` threshold consumed by the three-scale exception theorem.
Every source, fluctuation, and numerical absorption premise stays explicit.
-/

open scoped Classical BigOperators ArithmeticFunction

set_option autoImplicit false

namespace GoldbachCircleMethodCenteredCorrectionNumericAbsorptionV18250

open GoldbachCircleMethodFiniteCompanionBindingV18118
open GoldbachCircleMethodLogCutoffPresieveBindingV18120
open GoldbachCircleMethodBumpDecayRadicalEnvelopeV18155
open GoldbachCircleMethodActualCharacterRadicalErrorV18157
open GoldbachCircleMethodRadicalCorrelationTransferV18161
open GoldbachCircleMethodBadPrimeProductComparisonV18165
open GoldbachCircleMethodMertensUniformConstantsV18168
open GoldbachCircleMethodBadPrimeUniformFrequencyV18169
open GoldbachCircleMethodGlobalSieveFiniteFactorV18173
open GoldbachCircleMethodMertensProductFromHarmonicV18174
open GoldbachCircleMethodDisjointPrimeFactorCompositionV18171
open GoldbachCircleMethodDirectLambdaRadicalDominationV18178
open GoldbachCircleMethodActualResidualExactDecompositionV18225
open GoldbachCircleMethodCenteredCorrectionV184CompositionV18244

/-- Literal right-hand side produced by V1.8.244. -/
noncomputable def centeredCorrectionBudgetExpression
    (CE CB D c CH rho eta : ℝ) (B N : ℕ) : ℝ :=
  CE * eta *
    ((128 * CH * (mertensProductConstant D c)^2 *
        (oneFrequencyConstant D c)^2 *
        (∫ ξ : ℝ, secondMomentDecay ξ)^2 / tenthDecayMass) *
      (B : ℝ) * arithmeticFactor N / rho^3 +
     CB * (128 * CH * (mertensProductConstant D c)^2 *
        (oneFrequencyConstant D c)^2 *
        (∫ ξ : ℝ, secondMomentDecay ξ)^2) *
      (B : ℝ) * arithmeticFactor N / rho^2)

/-- Exact one-scale gateway from literal analytic source data to the strict
`M/2048` centered-correction threshold.  The final numerical inequality is
an explicit premise, not a conclusion obtained from positivity alone. -/
theorem eventual_centeredCorrection_subthreshold_of_numeric_budget :
    ∃ CE : ℝ, 0 ≤ CE ∧ ∃ CB : ℝ, 0 ≤ CB ∧
      ∀ (D c CH : ℝ) (_hD : 0 ≤ D) (_hCH : 0 ≤ CH)
        (_hweighted : ∀ (X : ℕ), 2 ≤ X → ∀ t : ℝ, 2 ≤ t → t ≤ (X : ℝ) →
          |prefixLogMoment X t - Real.log t| ≤ D)
        (_hharmonic : ∀ (X : ℕ), 2 ≤ X → ∀ t : ℝ, 2 ≤ t → t ≤ (X : ℝ) →
          |prefixHarmonicMoment X t - Real.log (Real.log t) - c| ≤
            D / Real.log t)
        (rho : ℝ) (_hrho : 0 < rho) (_hrho1 : rho ≤ 1),
      ∃ B₀ : ℕ, ∀ {M B N : ℕ} (eta : ℝ),
        B₀ ≤ B → 5 * B ≤ 4 * N → 4 * N ≤ 7 * B → 0 ≤ eta →
        (∀ ξ η' : ℝ,
          arithmeticCorrelation ((B : ℝ)^rho) ξ η'
              (Finset.Ioc (B / 2) B) N ≤
            CH * ((B : ℝ) / 2) * finiteSieveProduct N (B / 2) *
              goodBadProduct ((B : ℝ)^rho) ξ η' N (B / 2)) →
        (∀ n ∈ blockCarrier B,
          actualFluctuationMass ⌊((B : ℝ)^rho)^2⌋₊ n
            ((B : ℝ) / ((B : ℝ)^rho)^4)
            (blockCarrier B) (blockInput B) ≤ eta) →
        centeredCorrectionBudgetExpression CE CB D c CH rho eta B N <
          (M : ℝ) / 2048 →
        ‖canonicalCenteredErrorCorrectionAt B rho (N : ℤ)‖ <
          (M : ℝ) / 2048 := by
  obtain ⟨CE, hCE, CB, hCB, hCore⟩ :=
    eventual_canonicalCenteredErrorCorrectionAt_bound
  refine ⟨CE, hCE, CB, hCB, ?_⟩
  intro D c CH hD hCH hweighted hharmonic rho hrho hrho1
  obtain ⟨B₀, hBound⟩ :=
    hCore D c CH hD hCH hweighted hharmonic rho hrho hrho1
  refine ⟨B₀, ?_⟩
  intro M B N eta hB₀ hLower hUpper heta hsource hmass hBudget
  have hCorrection := hBound eta hB₀ hLower hUpper heta hsource hmass
  exact hCorrection.trans_lt (by
    simpa only [centeredCorrectionBudgetExpression] using hBudget)

end GoldbachCircleMethodCenteredCorrectionNumericAbsorptionV18250
