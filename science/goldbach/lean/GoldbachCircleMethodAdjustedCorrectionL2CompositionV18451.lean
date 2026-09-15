import GoldbachCircleMethodAdjustedCenteredCorrectionLiteralAdapterV18252
import GoldbachCircleMethodAdjustedCharacterSlotL2AdapterV18449

/-!
# Goldbach V1.8.451: adjusted correction L2 composition

The exact character-slot energy adapter is now composed with the literal
centered-error convolution.  Cauchy--Schwarz is applied at both interfaces:
inside each source slot (V1.8.449) and across the finite pair carrier here.

This removes the uniform `eta` and L1 source-mass requirement from the formal
correction interface.  The resulting source-energy and partner-energy product
is exact and finite; its analytic smallness remains open.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodAdjustedCorrectionL2CompositionV18451

open GoldbachCircleMethodActiveExceptionalCenteringV18129
open GoldbachCircleMethodActiveResidualExactDecompositionV18251
open GoldbachCircleMethodAdjustedCenteredCorrectionLiteralAdapterV18252
open GoldbachCircleMethodAdjustedCharacterSlotL2AdapterV18449
open GoldbachCircleMethodCanonicalBumpPrincipalFloorV18220
open GoldbachCircleMethodLogCutoffPresieveBindingV18120
open GoldbachCircleMethodSupportedModelErrorConvolutionV18182

/-- Squared supported adjusted-error mass on the literal source block. -/
noncomputable def supportedAdjustedErrorEnergy
    (B : ℕ) (rho b : ℝ)
    (e : CharacterSlot ⌊((B : ℝ)^rho)^2⌋₊) : ℝ :=
  ∑ n ∈ blockCarrier B,
    ‖supportedAdjustedError B n ((B : ℝ)^rho) b canonicalLogBump e‖ ^ 2

/-- Sum of the exact character coefficient/source energy products generating
the supported error on the source block. -/
noncomputable def adjustedSlotEnergyProductSourceSum
    (B : ℕ) (rho b : ℝ)
    (e : CharacterSlot ⌊((B : ℝ)^rho)^2⌋₊) : ℝ :=
  ∑ n ∈ blockCarrier B,
    adjustedCoefficientEnergy ⌊((B : ℝ)^rho)^2⌋₊ n
        (logWeight ((B : ℝ)^rho) canonicalLogBump) *
      adjustedSourceEnergy ⌊((B : ℝ)^rho)^2⌋₊ B n
        ((B : ℝ) / ((B : ℝ)^rho)^4) b (blockInput B) e

/-- Literal norm of the factor paired with the adjusted error. -/
noncomputable def adjustedCorrectionPartnerNorm
    (B N n : ℕ) (rho b : ℝ)
    (e : CharacterSlot ⌊((B : ℝ)^rho)^2⌋₊) : ℝ :=
  ‖blockInput B (N - n)‖ +
    ‖supportedAdjustedModel B (N - n) ((B : ℝ)^rho)
      b canonicalLogBump e‖

/-- Exact partner-factor energy for one convolution target. -/
noncomputable def adjustedCorrectionPartnerEnergy
    (B N : ℕ) (rho b : ℝ)
    (e : CharacterSlot ⌊((B : ℝ)^rho)^2⌋₊) : ℝ :=
  ∑ n ∈ blockCarrier B,
    (adjustedCorrectionPartnerNorm B N n rho b e) ^ 2

/-- The supported source-error energy is controlled by the sum of the literal
slotwise coefficient/source energy products. -/
theorem supported_adjusted_error_energy_le_slot_energy_sum
    (B : ℕ) (rho b : ℝ)
    (e : CharacterSlot ⌊((B : ℝ)^rho)^2⌋₊) :
    supportedAdjustedErrorEnergy B rho b e ≤
      adjustedSlotEnergyProductSourceSum B rho b e := by
  unfold supportedAdjustedErrorEnergy adjustedSlotEnergyProductSourceSum
  apply Finset.sum_le_sum
  intro n hn
  have hnIoc : n ∈ Finset.Ioc (B / 2) B := by
    simpa only [blockCarrier] using hn
  rw [supportedAdjustedError, if_pos hnIoc]
  exact adjusted_centered_error_sq_le_energy_product
    ⌊((B : ℝ)^rho)^2⌋₊ B n
      ((B : ℝ) / ((B : ℝ)^rho)^4) b
      (blockInput B) (logWeight ((B : ℝ)^rho) canonicalLogBump) e

/-- Two-level exact L2 control of the literal centered correction: slot
Cauchy--Schwarz followed by pair-carrier Cauchy--Schwarz. -/
theorem canonical_adjusted_centered_correction_sq_le_energy_product
    (B N : ℕ) (rho b : ℝ)
    (e : CharacterSlot ⌊((B : ℝ)^rho)^2⌋₊) (hBN : B ≤ N) :
    ‖canonicalAdjustedCenteredErrorCorrectionAt B rho b e (N : ℤ)‖ ^ 2 ≤
      adjustedSlotEnergyProductSourceSum B rho b e *
        adjustedCorrectionPartnerEnergy B N rho b e := by
  have hmajor := norm_canonicalAdjustedCenteredErrorCorrectionAt_le_majorant
    B N rho b e hBN
  have hmajorNonneg : 0 ≤ adjustedCenteredCorrectionMajorant B N rho b e := by
    unfold adjustedCenteredCorrectionMajorant
    exact Finset.sum_nonneg (fun n _hn =>
      mul_nonneg (norm_nonneg _)
        (add_nonneg (norm_nonneg _) (norm_nonneg _)))
  have hsq :
      ‖canonicalAdjustedCenteredErrorCorrectionAt B rho b e (N : ℤ)‖ ^ 2 ≤
        (adjustedCenteredCorrectionMajorant B N rho b e) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) hmajorNonneg).mpr hmajor
  have hcs :
      (adjustedCenteredCorrectionMajorant B N rho b e) ^ 2 ≤
        supportedAdjustedErrorEnergy B rho b e *
          adjustedCorrectionPartnerEnergy B N rho b e := by
    unfold adjustedCenteredCorrectionMajorant supportedAdjustedErrorEnergy
      adjustedCorrectionPartnerEnergy adjustedCorrectionPartnerNorm
    exact Finset.sum_mul_sq_le_sq_mul_sq (blockCarrier B)
      (fun n =>
        ‖supportedAdjustedError B n ((B : ℝ)^rho) b canonicalLogBump e‖)
      (fun n =>
        ‖blockInput B (N - n)‖ +
          ‖supportedAdjustedModel B (N - n) ((B : ℝ)^rho)
            b canonicalLogBump e‖)
  calc
    _ ≤ supportedAdjustedErrorEnergy B rho b e *
        adjustedCorrectionPartnerEnergy B N rho b e := hsq.trans hcs
    _ ≤ adjustedSlotEnergyProductSourceSum B rho b e *
        adjustedCorrectionPartnerEnergy B N rho b e := by
      exact mul_le_mul_of_nonneg_right
        (supported_adjusted_error_energy_le_slot_energy_sum B rho b e)
        (by unfold adjustedCorrectionPartnerEnergy; positivity)

end GoldbachCircleMethodAdjustedCorrectionL2CompositionV18451
