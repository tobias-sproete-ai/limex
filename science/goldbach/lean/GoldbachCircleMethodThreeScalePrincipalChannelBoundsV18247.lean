import GoldbachCircleMethodSixChannelExceptionDecompositionV18246
import GoldbachCircleMethodTwoScalePrincipalChannelBoundsV18240

/-!
# Goldbach V1.8.247: three-scale principal-channel bounds

The source-matched conditional Vaughan moment is applied at every member of
the endpoint-safe three-scale cover.  One uniform constant controls all three
principal-residual large-value sets.

No estimate for a centered-error correction is asserted here.
-/

open scoped Classical BigOperators

set_option autoImplicit false

namespace GoldbachCircleMethodThreeScalePrincipalChannelBoundsV18247

open GoldbachCircleMethodActualResidualLargeValueTransferV18224
open GoldbachCircleMethodResidualScaleAdmissionV18196
open GoldbachCircleMethodThreeScaleCenteredContractCoverV18242
open GoldbachCircleMethodFourChannelExceptionDecompositionV18239
open GoldbachCircleMethodTwoScalePrincipalChannelBoundsV18240
open GoldbachCircleMethodRealApproximationMinorAdapterV1873

/-- The V1.8.224 source-matched moment theorem gives one uniform `Crho` and
simultaneous cardinality bounds at the lower, middle, and upper analytic
source scales. -/
theorem three_scale_principalBadTargets_card_bounds
    (C rho : ℝ) (hC : 0 ≤ C) (hV : RealVaughanEstimate C)
    (hrho : 0 < rho) (hrhoUpper : rho ≤ (1 : ℝ) / 10000) :
    ∃ Crho : ℝ, 0 ≤ Crho ∧ ∀ (M : ℕ), 128 ≤ M →
      ∀ (hLow : blockThreshold rho ≤ analyticLowerSourceScale M)
        (hMid : blockThreshold rho ≤ analyticMiddleSourceScale M)
        (hHigh : blockThreshold rho ≤ analyticUpperSourceScale M),
      ((principalBadTargets M (analyticLowerSourceScale M) rho
          (actual_scale_admission rho hrho hrhoUpper
            (analyticLowerSourceScale M) hLow).2.1).card : ℝ) ≤
          (Crho * (analyticLowerSourceScale M : ℝ)^3 *
            ((analyticLowerSourceScale M : ℝ)^rho)^(-(5 : ℝ) / 8) *
            (Real.log (analyticLowerSourceScale M : ℝ))^2) /
              ((M : ℝ) / 2048)^2 ∧
      ((principalBadTargets M (analyticMiddleSourceScale M) rho
          (actual_scale_admission rho hrho hrhoUpper
            (analyticMiddleSourceScale M) hMid).2.1).card : ℝ) ≤
          (Crho * (analyticMiddleSourceScale M : ℝ)^3 *
            ((analyticMiddleSourceScale M : ℝ)^rho)^(-(5 : ℝ) / 8) *
            (Real.log (analyticMiddleSourceScale M : ℝ))^2) /
              ((M : ℝ) / 2048)^2 ∧
      ((principalBadTargets M (analyticUpperSourceScale M) rho
          (actual_scale_admission rho hrho hrhoUpper
            (analyticUpperSourceScale M) hHigh).2.1).card : ℝ) ≤
          (Crho * (analyticUpperSourceScale M : ℝ)^3 *
            ((analyticUpperSourceScale M : ℝ)^rho)^(-(5 : ℝ) / 8) *
            (Real.log (analyticUpperSourceScale M : ℝ))^2) /
              ((M : ℝ) / 2048)^2 := by
  obtain ⟨Crho, hCrho, hMomentCard⟩ :=
    canonical_principal_residual_largeNorm_card_bound C rho hC hV hrho
  refine ⟨Crho, hCrho, ?_⟩
  intro M hM hLow hMid hHigh
  have hMLow := actual_scale_admission rho hrho hrhoUpper
    (analyticLowerSourceScale M) hLow
  have hMMid := actual_scale_admission rho hrho hrhoUpper
    (analyticMiddleSourceScale M) hMid
  have hMHigh := actual_scale_admission rho hrho hrhoUpper
    (analyticUpperSourceScale M) hHigh
  refine ⟨?_, ?_, ?_⟩
  · exact principalBadTargets_card_bound Crho rho hMomentCard
      M (analyticLowerSourceScale M) (by omega) hMLow.1 hMLow.2.1
      hMLow.2.2.1 hMLow.2.2.2
  · exact principalBadTargets_card_bound Crho rho hMomentCard
      M (analyticMiddleSourceScale M) (by omega) hMMid.1 hMMid.2.1
      hMMid.2.2.1 hMMid.2.2.2
  · exact principalBadTargets_card_bound Crho rho hMomentCard
      M (analyticUpperSourceScale M) (by omega) hMHigh.1 hMHigh.2.1
      hMHigh.2.2.1 hMHigh.2.2.2

end GoldbachCircleMethodThreeScalePrincipalChannelBoundsV18247

