import GoldbachCircleMethodCenteredCorrectionSourceBudgetInterfaceV18248

/-!
# Goldbach V1.8.249: conditional three-scale exception bound

The three source-matched principal estimates and the exact centered
subthreshold interface are composed into one explicit finite bound for the
hypothetical non-Goldbach set in a complete dyadic target block.

Both analytic inputs remain visible in the theorem signature.
-/

open scoped Classical BigOperators

set_option autoImplicit false

namespace GoldbachCircleMethodConditionalThreeScaleExceptionBoundV18249

open GoldbachCircleMethodActualResidualLargeValueTransferV18224
open GoldbachCircleMethodResidualScaleAdmissionV18196
open GoldbachCircleMethodThreeScaleCenteredContractCoverV18242
open GoldbachCircleMethodFourChannelExceptionDecompositionV18239
open GoldbachCircleMethodThreeScalePrincipalChannelBoundsV18247
open GoldbachCircleMethodCenteredCorrectionSourceBudgetInterfaceV18248
open GoldbachCircleMethodRealApproximationMinorAdapterV1873
open GoldbachCircleMethodBoundedConductorReindexV18117

/-- Complete finite dyadic exception bound, conditional on the source-matched
Vaughan estimate and the explicit three-scale centered-correction contract. -/
theorem conditional_nonGoldbachTargets_card_bound
    (C rho : ℝ) (hC : 0 ≤ C) (hV : RealVaughanEstimate C)
    (hrho : 0 < rho) (hrhoUpper : rho ≤ (1 : ℝ) / 10000) :
    ∃ Crho : ℝ, 0 ≤ Crho ∧ ∀ (M : ℕ), 128 ≤ M →
      ∀ (_hLow : blockThreshold rho ≤ analyticLowerSourceScale M)
        (_hMid : blockThreshold rho ≤ analyticMiddleSourceScale M)
        (_hHigh : blockThreshold rho ≤ analyticUpperSourceScale M),
      ∀ {K : ℕ} [NeZero K],
        (∀ q : PositiveLevel
          ⌊((analyticLowerSourceScale M : ℝ) ^ rho) ^ 2⌋₊, q.val ∣ K) →
        (∀ q : PositiveLevel
          ⌊((analyticMiddleSourceScale M : ℝ) ^ rho) ^ 2⌋₊, q.val ∣ K) →
        (∀ q : PositiveLevel
          ⌊((analyticUpperSourceScale M : ℝ) ^ rho) ^ 2⌋₊, q.val ∣ K) →
        ThreeScaleCenteredCorrectionSubthreshold M rho →
        ((nonGoldbachTargets M).card : ℝ) ≤
          (Crho * (analyticLowerSourceScale M : ℝ)^3 *
            ((analyticLowerSourceScale M : ℝ)^rho)^(-(5 : ℝ) / 8) *
            (Real.log (analyticLowerSourceScale M : ℝ))^2) /
              ((M : ℝ) / 2048)^2 +
          (Crho * (analyticMiddleSourceScale M : ℝ)^3 *
            ((analyticMiddleSourceScale M : ℝ)^rho)^(-(5 : ℝ) / 8) *
            (Real.log (analyticMiddleSourceScale M : ℝ))^2) /
              ((M : ℝ) / 2048)^2 +
          (Crho * (analyticUpperSourceScale M : ℝ)^3 *
            ((analyticUpperSourceScale M : ℝ)^rho)^(-(5 : ℝ) / 8) *
            (Real.log (analyticUpperSourceScale M : ℝ))^2) /
              ((M : ℝ) / 2048)^2 := by
  obtain ⟨Crho, hCrho, hPrincipal⟩ :=
    three_scale_principalBadTargets_card_bounds C rho hC hV hrho hrhoUpper
  refine ⟨Crho, hCrho, ?_⟩
  intro M hM hLow hMid hHigh K _inst hKLow hKMid hKHigh hCentered
  have hNat := nonGoldbachTargets_card_le_three_principal_sum
    M rho hM hrho hrhoUpper hLow hMid hHigh hKLow hKMid hKHigh hCentered
  have hCard : ((nonGoldbachTargets M).card : ℝ) ≤
      ((principalBadTargets M (analyticLowerSourceScale M) rho
        (actual_scale_admission rho hrho hrhoUpper
          (analyticLowerSourceScale M) hLow).2.1).card : ℝ) +
      ((principalBadTargets M (analyticMiddleSourceScale M) rho
        (actual_scale_admission rho hrho hrhoUpper
          (analyticMiddleSourceScale M) hMid).2.1).card : ℝ) +
      ((principalBadTargets M (analyticUpperSourceScale M) rho
        (actual_scale_admission rho hrho hrhoUpper
          (analyticUpperSourceScale M) hHigh).2.1).card : ℝ) := by
    exact_mod_cast hNat
  have hBounds := hPrincipal M hM hLow hMid hHigh
  exact hCard.trans (add_le_add (add_le_add hBounds.1 hBounds.2.1) hBounds.2.2)

end GoldbachCircleMethodConditionalThreeScaleExceptionBoundV18249
