import GoldbachCircleMethodAdjustedCenteredCorrectionV182CompositionV18253

/-!
# Goldbach V1.8.254: adjusted centered-correction numeric absorption

The exact active V1.8.253 majorant is named and connected to the strict
`M/2048` threshold.  The numerical inequality remains an explicit premise.
-/

open scoped Classical BigOperators ArithmeticFunction

set_option autoImplicit false

namespace GoldbachCircleMethodAdjustedCenteredCorrectionNumericAbsorptionV18254

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
open GoldbachCircleMethodActualResidualExactDecompositionV18225
open GoldbachCircleMethodActiveResidualExactDecompositionV18251
open GoldbachCircleMethodAdjustedCenteredCorrectionV182CompositionV18253

/-- Literal right-hand side produced by V1.8.253. -/
noncomputable def adjustedCenteredCorrectionBudgetExpression
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

/-- One-scale gateway from active source data to the strict correction
threshold.  The final numerical absorption is supplied, not inferred. -/
theorem eventual_adjustedCenteredCorrection_subthreshold_of_numeric_budget :
    ∃ CE : ℝ, 0 ≤ CE ∧ ∃ CB : ℝ, 0 ≤ CB ∧
      ∀ (D c CH : ℝ) (_hD : 0 ≤ D) (_hCH : 0 ≤ CH)
        (_hweighted : ∀ (X : ℕ), 2 ≤ X → ∀ t : ℝ, 2 ≤ t → t ≤ (X : ℝ) →
          |prefixLogMoment X t - Real.log t| ≤ D)
        (_hharmonic : ∀ (X : ℕ), 2 ≤ X → ∀ t : ℝ, 2 ≤ t → t ≤ (X : ℝ) →
          |prefixHarmonicMoment X t - Real.log (Real.log t) - c| ≤
            D / Real.log t)
        (rho : ℝ) (_hrho : 0 < rho) (_hrho1 : rho ≤ 1),
      ∃ B₀ : ℕ, ∀ {M B N : ℕ} (b eta : ℝ)
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
        adjustedCenteredCorrectionBudgetExpression CE CB D c CH rho eta B N <
          (M : ℝ) / 2048 →
        ‖canonicalAdjustedCenteredErrorCorrectionAt B rho b e (N : ℤ)‖ <
          (M : ℝ) / 2048 := by
  obtain ⟨CE, hCE, CB, hCB, hCore⟩ :=
    eventual_canonicalAdjustedCenteredErrorCorrectionAt_bound
  refine ⟨CE, hCE, CB, hCB, ?_⟩
  intro D c CH hD hCH hweighted hharmonic rho hrho hrho1
  obtain ⟨B₀, hBound⟩ :=
    hCore D c CH hD hCH hweighted hharmonic rho hrho hrho1
  refine ⟨B₀, ?_⟩
  intro M B N b eta e hB₀ hLower hUpper hb heta hsource hmass hBudget
  have hCorrection := hBound b eta e hB₀ hLower hUpper hb heta hsource hmass
  exact hCorrection.trans_lt (by
    simpa only [adjustedCenteredCorrectionBudgetExpression] using hBudget)

end GoldbachCircleMethodAdjustedCenteredCorrectionNumericAbsorptionV18254

