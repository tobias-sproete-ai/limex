import GoldbachCircleMethodFourChannelExceptionDecompositionV18239

/-!
# Goldbach V1.8.240: two-scale principal-channel bounds

The already source-matched conditional Vaughan moment is applied separately
to the principal-residual large-value sets at the two covering source scales.
The target block may extend beyond `[0,2B]` at the lower scale, so a dedicated
injective support transfer is proved before any cardinality estimate is used.

No estimate for the centered-error correction is asserted here.
-/

open scoped Classical BigOperators

set_option autoImplicit false

namespace GoldbachCircleMethodTwoScalePrincipalChannelBoundsV18240

open GoldbachCircleMethodSupportedResidualParsevalV18190
open GoldbachCircleMethodActualInputModelResidualV18138
open GoldbachCircleMethodSupportedModelErrorConvolutionV18182
open GoldbachCircleMethodActualResidualLargeValueTransferV18224
open GoldbachCircleMethodResidualScaleAdmissionV18196
open GoldbachCircleMethodTwoSourceScaleCoverV18232
open GoldbachCircleMethodFourChannelExceptionDecompositionV18239
open GoldbachCircleMethodRealApproximationMinorAdapterV1873

/-- Casting a natural target to an integer injects the target-block
principal large-value set into the full support interval used by the moment
theorem.  Large values outside `[0,2B]` are impossible because the literal
block convolution is zero there. -/
theorem principalBadTargets_card_le_fullSupportLargeSet
    (M B : ℕ) (rho : ℝ) (hR2 : 2 ≤ (B : ℝ)^rho) (hM : 1 ≤ M) :
    (principalBadTargets M B rho hR2).card ≤
      (largeNormIndices (Finset.Icc (0 : ℤ) (2 * B : ℕ))
        (canonicalPrincipalResidualAt B rho hR2)
        ((M : ℝ) / 2048)).card := by
  classical
  apply Finset.card_le_card_of_injOn (fun N : ℕ => (N : ℤ))
  · intro N hN
    have hData := Finset.mem_filter.mp hN
    have hLarge : (M : ℝ) / 2048 ≤
        ‖canonicalPrincipalResidualAt B rho hR2 (N : ℤ)‖ := hData.2
    have hSupport : (N : ℤ) ∈ Finset.Icc (0 : ℤ) (2 * B : ℕ) := by
      by_contra hOutside
      have hZero : canonicalPrincipalResidualAt B rho hR2 (N : ℤ) = 0 := by
        unfold canonicalPrincipalResidualAt
        apply integerPairConvolution_block_zero_outside
        exact hOutside
      rw [hZero, norm_zero] at hLarge
      have hThreshold : 0 < (M : ℝ) / 2048 := by positivity
      linarith
    exact Finset.mem_filter.mpr ⟨hSupport, hLarge⟩
  · intro x _ y _ hxy
    exact Int.ofNat_injective hxy

/-- A single source scale inherits the literal conditional Vaughan
large-value bound, even when the ambient target block is larger than the
convolution support. -/
theorem principalBadTargets_card_bound
    (Crho rho : ℝ)
    (hMomentCard : ∀ (B : ℕ) (_hB : 6 ≤ B),
      ∀ (hR2 : 2 ≤ (B : ℝ)^rho),
      Real.exp (Real.sqrt (Real.log (B : ℝ))) ≤ (B : ℝ)^rho →
      (B : ℝ)^rho ≤ (B : ℝ)^((1 : ℝ) / 10000) →
      ∀ T : ℝ, 0 < T →
      ((largeNormIndices (Finset.Icc (0 : ℤ) (2 * B : ℕ))
        (canonicalPrincipalResidualAt B rho hR2) T).card : ℝ) ≤
        (Crho * (B : ℝ)^3 * ((B : ℝ)^rho)^(-(5 : ℝ) / 8) *
          (Real.log (B : ℝ))^2) / T^2)
    (M B : ℕ) (hM : 1 ≤ M) (hB6 : 6 ≤ B)
    (hR2 : 2 ≤ (B : ℝ)^rho)
    (hLower : Real.exp (Real.sqrt (Real.log (B : ℝ))) ≤ (B : ℝ)^rho)
    (hUpper : (B : ℝ)^rho ≤ (B : ℝ)^((1 : ℝ) / 10000)) :
    ((principalBadTargets M B rho hR2).card : ℝ) ≤
      (Crho * (B : ℝ)^3 * ((B : ℝ)^rho)^(-(5 : ℝ) / 8) *
        (Real.log (B : ℝ))^2) / ((M : ℝ) / 2048)^2 := by
  have hCardNat := principalBadTargets_card_le_fullSupportLargeSet
    M B rho hR2 hM
  have hCardReal : ((principalBadTargets M B rho hR2).card : ℝ) ≤
      ((largeNormIndices (Finset.Icc (0 : ℤ) (2 * B : ℕ))
        (canonicalPrincipalResidualAt B rho hR2)
        ((M : ℝ) / 2048)).card : ℝ) := by
    exact_mod_cast hCardNat
  exact hCardReal.trans
    (hMomentCard B hB6 hR2 hLower hUpper ((M : ℝ) / 2048) (by positivity))

/-- The source-matched V1.8.224 theorem provides one uniform `Crho` and
simultaneous explicit cardinality bounds at both actual source scales. -/
theorem two_scale_principalBadTargets_card_bounds
    (C rho : ℝ) (hC : 0 ≤ C) (hV : RealVaughanEstimate C)
    (hrho : 0 < rho) (hrhoUpper : rho ≤ (1 : ℝ) / 10000) :
    ∃ Crho : ℝ, 0 ≤ Crho ∧ ∀ (M : ℕ), 37 ≤ M →
      ∀ (hLow : blockThreshold rho ≤ lowerSourceScale M)
        (hHigh : blockThreshold rho ≤ upperSourceScale M),
      ((principalBadTargets M (lowerSourceScale M) rho
          (actual_scale_admission rho hrho hrhoUpper
            (lowerSourceScale M) hLow).2.1).card : ℝ) ≤
          (Crho * (lowerSourceScale M : ℝ)^3 *
            ((lowerSourceScale M : ℝ)^rho)^(-(5 : ℝ) / 8) *
            (Real.log (lowerSourceScale M : ℝ))^2) /
              ((M : ℝ) / 2048)^2 ∧
      ((principalBadTargets M (upperSourceScale M) rho
          (actual_scale_admission rho hrho hrhoUpper
            (upperSourceScale M) hHigh).2.1).card : ℝ) ≤
          (Crho * (upperSourceScale M : ℝ)^3 *
            ((upperSourceScale M : ℝ)^rho)^(-(5 : ℝ) / 8) *
            (Real.log (upperSourceScale M : ℝ))^2) /
              ((M : ℝ) / 2048)^2 := by
  obtain ⟨Crho, hCrho, hMomentCard⟩ :=
    canonical_principal_residual_largeNorm_card_bound C rho hC hV hrho
  refine ⟨Crho, hCrho, ?_⟩
  intro M hM hLow hHigh
  have hMLow := actual_scale_admission rho hrho hrhoUpper
    (lowerSourceScale M) hLow
  have hMHigh := actual_scale_admission rho hrho hrhoUpper
    (upperSourceScale M) hHigh
  constructor
  · exact principalBadTargets_card_bound Crho rho hMomentCard
      M (lowerSourceScale M) (by omega) hMLow.1 hMLow.2.1
      hMLow.2.2.1 hMLow.2.2.2
  · exact principalBadTargets_card_bound Crho rho hMomentCard
      M (upperSourceScale M) (by omega) hMHigh.1 hMHigh.2.1
      hMHigh.2.2.1 hMHigh.2.2.2

end GoldbachCircleMethodTwoScalePrincipalChannelBoundsV18240
