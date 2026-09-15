import GoldbachCircleMethodPowerWeightAbelIntervalV18331

/-!
# Goldbach V1.8.332: canonical Abel pairwise bound

The variable-weight Abel estimate is attached to the exact canonical block
convolution.  Under `0 <= b <= 1`, the full spatial factor is at most twelve,
so the centered error is at most `24*Q^4*M^2`.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodCanonicalAbelPairwiseBoundV18332

open GoldbachCircleMethodActiveExceptionalCenteringV18129
open GoldbachCircleMethodActiveResidualExactDecompositionV18251
open GoldbachCircleMethodBlockPairCarrierV18227
open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodCanonicalBumpPrincipalFloorV18220
open GoldbachCircleMethodCanonicalLocalizedIntervalReserveV18311
open GoldbachCircleMethodCanonicalPairwiseBlockBindingV18326
open GoldbachCircleMethodExceptionalWeightBoundaryV18128
open GoldbachCircleMethodFullFrozenPairwiseIntervalV18323
open GoldbachCircleMethodLogCutoffPresieveBindingV18120
open GoldbachCircleMethodPowerWeightAbelIntervalV18331
open GoldbachCircleMethodPrincipalWindowBoundaryV18121
open GoldbachCircleMethodSupportedAdjustedModelBindingAuditV18285

/-- The exact length of a nonempty canonical pair interval is bounded by the
ambient dyadic scale. -/
theorem blockPair_interval_length_le
    (B N : ℕ) (hB : 2 ≤ B)
    (hInterval : blockPairLower B N ≤ blockPairUpper B N) :
    blockPairUpper B N - blockPairLower B N + 1 ≤ B := by
  unfold blockPairLower blockPairUpper at *
  omega

/-- Canonical power-weight pairwise-period estimate with no common LCM and no
linear-in-`B` freezing loss. -/
theorem canonicalAdjustedModelAt_abel_centered_norm_le
    (B N : ℕ) (rho b : ℝ)
    (e : CharacterSlot ⌊((B : ℝ) ^ rho) ^ 2⌋₊)
    (hInv : e.2.val⁻¹ = e.2.val)
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (hB : 2 ≤ B) (hBN : B ≤ N)
    (hInterval : blockPairLower B N ≤ blockPairUpper B N)
    (hR : 1 < (B : ℝ) ^ rho)
    (M : ℝ) (hM : 0 ≤ M)
    (hw : ∀ n : ℕ,
      ‖logWeight ((B : ℝ) ^ rho) canonicalLogBump n‖ ≤ M) :
    let Q := ⌊((B : ℝ) ^ rho) ^ 2⌋₊
    let A := blockPairLower B N
    let T := blockPairUpper B N - blockPairLower B N + 1
    ‖canonicalAdjustedModelAt B rho b e (N : ℤ) -
        powerPairwiseVariableMean
          (log_cutoff_contains_one ((B : ℝ) ^ rho) hR)
          e.1 e.2
          (logWeight ((B : ℝ) ^ rho) canonicalLogBump)
          (logWeight ((B : ℝ) ^ rho) canonicalLogBump)
          b N A T‖ ≤
      24 * (Q : ℝ) ^ 4 * M ^ 2 := by
  dsimp only
  let T := blockPairUpper B N - blockPairLower B N + 1
  have hT1 : 1 ≤ T := by
    dsimp [T]
    omega
  have hTB : T ≤ B := by
    exact blockPair_interval_length_le B N hB hInterval
  rcases blockPair_interval_geometry B N hBN hInterval with
    ⟨_hAN, hend, _hA, _hNA, hleft, hright⟩
  rw [canonicalAdjustedModelAt_eq_adjustedBlockPairSum B N rho b e hR hBN]
  rw [adjustedBlockPairSum_eq_variablePowerPairInterval
    (log_cutoff_contains_one ((B : ℝ) ^ rho) hR)
    e.1 e.2
    (logWeight ((B : ℝ) ^ rho) canonicalLogBump)
    (logWeight ((B : ℝ) ^ rho) canonicalLogBump)
    b B N (by omega) hBN hInterval]
  have h := variablePowerPairInterval_abel_centered_norm_le
    (log_cutoff_contains_one ((B : ℝ) ^ rho) hR)
    e.1 e.2 hInv
    (logWeight ((B : ℝ) ^ rho) canonicalLogBump)
    (logWeight ((B : ℝ) ^ rho) canonicalLogBump)
    b N (blockPairLower B N) T B hB hb0 hT1 hend hleft hright
    M M hM hM hw hw
  have hBpos : (0 : ℝ) < B := by exact_mod_cast (by omega : 0 < B)
  have hTnonneg : (0 : ℝ) ≤ T := by positivity
  have hTB' : (T : ℝ) ≤ B := by exact_mod_cast hTB
  have hfrac0 : 0 ≤ (T : ℝ) / (B : ℝ) := div_nonneg hTnonneg hBpos.le
  have hfrac1 : (T : ℝ) / (B : ℝ) ≤ 1 := (div_le_one hBpos).2 hTB'
  have hbfrac : b * ((T : ℝ) / (B : ℝ)) ≤ 1 := by
    calc
      b * ((T : ℝ) / (B : ℝ)) ≤ 1 * 1 := by gcongr
      _ = 1 := by ring
  have hfactor : 4 + 8 * b * (T : ℝ) / (B : ℝ) ≤ 12 := by
    calc
      4 + 8 * b * (T : ℝ) / (B : ℝ) =
          4 + 8 * (b * ((T : ℝ) / (B : ℝ))) := by ring
      _ ≤ 4 + 8 * 1 := by gcongr
      _ = 12 := by ring
  calc
    _ ≤ (2 * (⌊((B : ℝ) ^ rho) ^ 2⌋₊ : ℝ) ^ 4 * M * M) *
        (4 + 8 * b * (T : ℝ) / (B : ℝ)) := h
    _ ≤ (2 * (⌊((B : ℝ) ^ rho) ^ 2⌋₊ : ℝ) ^ 4 * M * M) * 12 := by
      apply mul_le_mul_of_nonneg_left hfactor
      positivity
    _ = 24 * (⌊((B : ℝ) ^ rho) ^ 2⌋₊ : ℝ) ^ 4 * M ^ 2 := by ring

end GoldbachCircleMethodCanonicalAbelPairwiseBoundV18332
