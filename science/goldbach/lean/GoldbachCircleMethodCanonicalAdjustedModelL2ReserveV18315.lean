import GoldbachCircleMethodOffDivisorPairL2AdapterV18314

/-!
# Goldbach V1.8.315: canonical adjusted-model L2 reserve

The actual V1.8.312 zero-gap reserve is composed with the finite energy
adapter of V1.8.314.  The literal norm of the three off-divisor channels is
thereby replaced by three visible Cauchy--Schwarz energy budgets.

This is a conditional reduction.  It does not assert that the energy budgets
are small enough to be absorbed.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodCanonicalAdjustedModelL2ReserveV18315

open GoldbachCircleMethodActiveConductorDivisorLocalizationV18290
open GoldbachCircleMethodActiveExceptionalCenteringV18129
open GoldbachCircleMethodAdjustedModelFourChannelPartitionV18292
open GoldbachCircleMethodBlockPairCarrierV18227
open GoldbachCircleMethodCanonicalAdjustedModelExplicitReserveV18312
open GoldbachCircleMethodCanonicalBumpPrincipalFloorV18220
open GoldbachCircleMethodExceptionalZeroGapAttestationRepairV18263
open GoldbachCircleMethodLogCutoffPresieveBindingV18120
open GoldbachCircleMethodOffDivisorPairL2AdapterV18314
open GoldbachCircleMethodPrincipalWindowBoundaryV18121
open GoldbachCircleMethodActiveResidualExactDecompositionV18251
open GoldbachCircleMethodStructurallyAdmissibleActiveSlotV18258
open GoldbachCircleMethodZeroGapReserveScaleV18266

/-- Exact energy product for the localized-left/off-divisor-right channel. -/
noncomputable def localizedOffEnergyProduct {Q : ℕ} (hQ : 1 ≤ Q)
    (J : Finset ℕ) (e : CharacterSlot Q) (N : ℕ)
    (b : ℝ) (w : ℕ → ℂ) : ℝ :=
  finiteEnergy (pairFirstCarrier J N) (localizedFactorNorm hQ e b w) *
    finiteEnergy (pairFirstCarrier J N)
      (fun n => offDivisorFactorNorm hQ e b w (N - n))

/-- Exact energy product for the off-divisor-left/localized-right channel. -/
noncomputable def offLocalizedEnergyProduct {Q : ℕ} (hQ : 1 ≤ Q)
    (J : Finset ℕ) (e : CharacterSlot Q) (N : ℕ)
    (b : ℝ) (w : ℕ → ℂ) : ℝ :=
  finiteEnergy (pairFirstCarrier J N) (offDivisorFactorNorm hQ e b w) *
    finiteEnergy (pairFirstCarrier J N)
      (fun n => localizedFactorNorm hQ e b w (N - n))

/-- Exact energy product for the off-divisor/off-divisor channel. -/
noncomputable def offOffEnergyProduct {Q : ℕ} (hQ : 1 ≤ Q)
    (J : Finset ℕ) (e : CharacterSlot Q) (N : ℕ)
    (b : ℝ) (w : ℕ → ℂ) : ℝ :=
  finiteEnergy (pairFirstCarrier J N) (offDivisorFactorNorm hQ e b w) *
    finiteEnergy (pairFirstCarrier J N)
      (fun n => offDivisorFactorNorm hQ e b w (N - n))

/-- Literal localized reserve from V1.8.311, with the terminal-period and
spatial-freezing costs retained. -/
noncomputable def canonicalLocalizedExplicitReserve
    (B N active : ℕ) [NeZero active] (gap : ℝ) : ℝ :=
  let T := blockPairUpper B N - blockPairLower B N + 1
  (((active : ℝ) / (active.totient : ℝ)) ^ 2) *
    ((((T / active : ℕ) : ℝ) *
          ((GoldbachCircleMethodActualUnitPairArithmeticV18194.unitPairCount
              active (N : ℤ) : ℝ) *
            zeroGapReserveScale gap B / 6) -
        4 * ((T % active : ℕ) : ℝ) -
        8 * gap * (T : ℝ) ^ 2 / (B : ℝ)))

/-- The actual canonical adjusted model has the V1.8.311 localized reserve
minus the three explicit finite energy budgets. -/
theorem canonicalAdjustedModelAt_zeroGap_l2_floor
    (B N : ℕ) (rho : ℝ)
    {ExceptionalZeroAt :
      StructurallyAdmissibleActiveSlot ⌊((B : ℝ) ^ rho) ^ 2⌋₊ → ℝ → Prop}
    (d : ExceptionalZeroGapAttestation
      ⌊((B : ℝ) ^ rho) ^ 2⌋₊ ExceptionalZeroAt)
    (hr3 : 3 < d.slot.val.1.val) (hEven : Even N)
    (hB : 4 ≤ B) (hBN : B ≤ N)
    (hInterval : blockPairLower B N ≤ blockPairUpper B N)
    (hR : 1 < (B : ℝ) ^ rho)
    (hactiveR : (d.slot.val.1.val : ℝ) ≤ (B : ℝ) ^ rho)
    (C₁ C₂ C₃ : ℝ)
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hC₃ : 0 ≤ C₃)
    (h₁ : localizedOffEnergyProduct
        (log_cutoff_contains_one ((B : ℝ) ^ rho) hR)
        (blockCarrier B) d.slot.val N d.zeroGap
        (logWeight ((B : ℝ) ^ rho) canonicalLogBump) ≤ C₁ ^ 2)
    (h₂ : offLocalizedEnergyProduct
        (log_cutoff_contains_one ((B : ℝ) ^ rho) hR)
        (blockCarrier B) d.slot.val N d.zeroGap
        (logWeight ((B : ℝ) ^ rho) canonicalLogBump) ≤ C₂ ^ 2)
    (h₃ : offOffEnergyProduct
        (log_cutoff_contains_one ((B : ℝ) ^ rho) hR)
        (blockCarrier B) d.slot.val N d.zeroGap
        (logWeight ((B : ℝ) ^ rho) canonicalLogBump) ≤ C₃ ^ 2) :
    canonicalLocalizedExplicitReserve B N d.slot.val.1.val d.zeroGap -
        (C₁ + C₂ + C₃) ≤
      (canonicalAdjustedModelAt B rho d.zeroGap d.slot.val (N : ℤ)).re := by
  let hQ := log_cutoff_contains_one ((B : ℝ) ^ rho) hR
  let wt := logWeight ((B : ℝ) ^ rho) canonicalLogBump
  have hoff :
      ‖offDivisorPairRemainder hQ (blockCarrier B) d.slot.val N
          d.zeroGap wt‖ ≤ C₁ + C₂ + C₃ := by
    apply offDivisorPairRemainder_norm_le_of_energy_budgets
      hQ (blockCarrier B) d.slot.val N d.zeroGap wt C₁ C₂ C₃
      hC₁ hC₂ hC₃
    · simpa only [localizedOffEnergyProduct, hQ, wt] using h₁
    · simpa only [offLocalizedEnergyProduct, hQ, wt] using h₂
    · simpa only [offOffEnergyProduct, hQ, wt] using h₃
  have hbase := canonicalAdjustedModelAt_zeroGap_explicit_floor
    B N rho d hr3 hEven hB hBN hInterval hR hactiveR
  dsimp only [canonicalLocalizedExplicitReserve] at hbase ⊢
  dsimp only [hQ, wt] at hoff
  linarith

/-- Strict dominance of the three energy budgets over the explicit localized
reserve yields positivity of the actual canonical adjusted model.  Every
analytic obligation remains a visible premise. -/
theorem canonicalAdjustedModelAt_zeroGap_re_pos_of_l2_absorption
    (B N : ℕ) (rho : ℝ)
    {ExceptionalZeroAt :
      StructurallyAdmissibleActiveSlot ⌊((B : ℝ) ^ rho) ^ 2⌋₊ → ℝ → Prop}
    (d : ExceptionalZeroGapAttestation
      ⌊((B : ℝ) ^ rho) ^ 2⌋₊ ExceptionalZeroAt)
    (hr3 : 3 < d.slot.val.1.val) (hEven : Even N)
    (hB : 4 ≤ B) (hBN : B ≤ N)
    (hInterval : blockPairLower B N ≤ blockPairUpper B N)
    (hR : 1 < (B : ℝ) ^ rho)
    (hactiveR : (d.slot.val.1.val : ℝ) ≤ (B : ℝ) ^ rho)
    (C₁ C₂ C₃ : ℝ)
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hC₃ : 0 ≤ C₃)
    (h₁ : localizedOffEnergyProduct
        (log_cutoff_contains_one ((B : ℝ) ^ rho) hR)
        (blockCarrier B) d.slot.val N d.zeroGap
        (logWeight ((B : ℝ) ^ rho) canonicalLogBump) ≤ C₁ ^ 2)
    (h₂ : offLocalizedEnergyProduct
        (log_cutoff_contains_one ((B : ℝ) ^ rho) hR)
        (blockCarrier B) d.slot.val N d.zeroGap
        (logWeight ((B : ℝ) ^ rho) canonicalLogBump) ≤ C₂ ^ 2)
    (h₃ : offOffEnergyProduct
        (log_cutoff_contains_one ((B : ℝ) ^ rho) hR)
        (blockCarrier B) d.slot.val N d.zeroGap
        (logWeight ((B : ℝ) ^ rho) canonicalLogBump) ≤ C₃ ^ 2)
    (habsorb : C₁ + C₂ + C₃ <
      canonicalLocalizedExplicitReserve B N d.slot.val.1.val d.zeroGap) :
    0 <
      (canonicalAdjustedModelAt B rho d.zeroGap d.slot.val (N : ℤ)).re := by
  have hfloor := canonicalAdjustedModelAt_zeroGap_l2_floor
    B N rho d hr3 hEven hB hBN hInterval hR hactiveR
    C₁ C₂ C₃ hC₁ hC₂ hC₃ h₁ h₂ h₃
  linarith

end GoldbachCircleMethodCanonicalAdjustedModelL2ReserveV18315
