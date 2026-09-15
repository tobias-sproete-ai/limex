import GoldbachCircleMethodVariablePowerPairwiseIntervalV18325
import GoldbachCircleMethodCanonicalLocalizedIntervalReserveV18311
import GoldbachCircleMethodSupportedAdjustedModelBindingAuditV18285

/-!
# Goldbach V1.8.326: canonical pairwise block binding

The pairwise-period interval of V1.8.325 is attached to the exact canonical
upper-half block carrier.  The proof uses the already audited closed-interval
description and its endpoint-preserving range reindexing.  It then identifies
the resulting sum with the pre-existing `canonicalAdjustedModelAt` object.

No global common period, positivity, asymptotic absorption, source estimate,
or Goldbach conclusion is introduced.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodCanonicalPairwiseBlockBindingV18326

open GoldbachCircleMethodActiveExceptionalCenteringV18129
open GoldbachCircleMethodActiveResidualExactDecompositionV18251
open GoldbachCircleMethodBlockPairCarrierV18227
open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodCanonicalBumpPrincipalFloorV18220
open GoldbachCircleMethodCanonicalLocalizedIntervalReserveV18311
open GoldbachCircleMethodExceptionalWeightBoundaryV18128
open GoldbachCircleMethodFullFrozenPairwiseIntervalV18323
open GoldbachCircleMethodLogCutoffPresieveBindingV18120
open GoldbachCircleMethodPrincipalWindowBoundaryV18121
open GoldbachCircleMethodSupportedAdjustedModelBindingAuditV18285
open GoldbachCircleMethodSupportedModelErrorConvolutionV18182
open GoldbachCircleMethodSupportedModelIntervalDiagonalV18228
open GoldbachCircleMethodVariablePowerPairwiseIntervalV18325

/-- The literal adjusted-model pair sum on the exact canonical block carrier.
The order matches V1.8.325: the first factor is evaluated at the complement. -/
noncomputable def adjustedBlockPairSum {Q : ℕ} (hQ : 1 ≤ Q)
    (r : PositiveLevel Q)
    (chi : {χ : DirichletCharacter ℂ r.val // χ.IsPrimitive})
    (v w : ℕ → ℂ) (b : ℝ) (B N : ℕ) : ℂ :=
  ∑ n ∈ pairFirstCarrier (blockCarrier B) N,
    adjustedModel Q (N - n) hQ b v ⟨r, chi⟩ *
      adjustedModel Q n hQ b w ⟨r, chi⟩

/-- Exact endpoint-preserving conversion of the block carrier into the
half-open interval consumed by the pairwise-period theorem. -/
theorem adjustedBlockPairSum_eq_variablePowerPairInterval
    {Q : ℕ} (hQ : 1 ≤ Q)
    (r : PositiveLevel Q)
    (chi : {χ : DirichletCharacter ℂ r.val // χ.IsPrimitive})
    (v w : ℕ → ℂ) (b : ℝ) (B N : ℕ)
    (hB : 1 ≤ B) (hBN : B ≤ N)
    (hInterval : blockPairLower B N ≤ blockPairUpper B N) :
    adjustedBlockPairSum hQ r chi v w b B N =
      variablePowerPairInterval hQ r chi v w b N
        (blockPairLower B N)
        (blockPairUpper B N - blockPairLower B N + 1) := by
  unfold adjustedBlockPairSum variablePowerPairInterval
  rw [pairFirstCarrier_block_eq_Icc B N hB hBN]
  rw [sum_Icc_eq_sum_range_shift
    (blockPairLower B N) (blockPairUpper B N) hInterval]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [naturalFrozenCoefficient_powerWeight_eq_adjustedModel,
    naturalFrozenCoefficient_powerWeight_eq_adjustedModel]

/-- On the canonical data, the established supported adjusted convolution is
literally the same block sum.  This theorem is an identity, not an estimate. -/
theorem canonicalAdjustedModelAt_eq_adjustedBlockPairSum
    (B N : ℕ) (rho b : ℝ)
    (e : CharacterSlot ⌊((B : ℝ) ^ rho) ^ 2⌋₊)
    (hR : 1 < (B : ℝ) ^ rho) (hBN : B ≤ N) :
    canonicalAdjustedModelAt B rho b e (N : ℤ) =
      adjustedBlockPairSum
        (log_cutoff_contains_one ((B : ℝ) ^ rho) hR)
        e.1 e.2
        (logWeight ((B : ℝ) ^ rho) canonicalLogBump)
        (logWeight ((B : ℝ) ^ rho) canonicalLogBump)
        b B N := by
  unfold canonicalAdjustedModelAt adjustedBlockPairSum
  rw [integerPairConvolution_nat_eq_pairFirstCarrier]
  · apply Finset.sum_congr rfl
    intro n hn
    have hpair := Finset.mem_filter.mp hn
    have hnIoc : n ∈ Finset.Ioc (B / 2) B := by
      simpa only [blockCarrier] using hpair.1
    have hcIoc : N - n ∈ Finset.Ioc (B / 2) B := by
      simpa only [blockCarrier] using hpair.2
    unfold supportedAdjustedModel
    rw [dif_pos hR, if_pos hnIoc, dif_pos hR, if_pos hcIoc]
    ring
  · intro n hn
    simp only [blockCarrier, Finset.mem_Ioc] at hn
    omega

/-- The actual canonical adjusted convolution inherits the V1.8.325
pairwise-period error on the exact block interval.  Both the spatial freezing
cost and the quartic pairwise boundary cost remain explicit. -/
theorem canonicalAdjustedModelAt_pairwise_centered_norm_le
    (B N : ℕ) (rho b : ℝ)
    (e : CharacterSlot ⌊((B : ℝ) ^ rho) ^ 2⌋₊)
    (hInv : e.2.val⁻¹ = e.2.val)
    (hb : 0 ≤ b)
    (hB : 2 ≤ B) (hBN : B ≤ N)
    (hInterval : blockPairLower B N ≤ blockPairUpper B N)
    (hR : 1 < (B : ℝ) ^ rho)
    (M : ℝ) (hM : 0 ≤ M)
    (hw : ∀ n : ℕ,
      ‖logWeight ((B : ℝ) ^ rho) canonicalLogBump n‖ ≤ M) :
    let Q := ⌊((B : ℝ) ^ rho) ^ 2⌋₊
    let T := blockPairUpper B N - blockPairLower B N + 1
    ‖canonicalAdjustedModelAt B rho b e (N : ℤ) -
        (T : ℂ) * fullFrozenPairwiseMean
          (log_cutoff_contains_one ((B : ℝ) ^ rho) hR)
          e.1 e.2
          (logWeight ((B : ℝ) ^ rho) canonicalLogBump)
          (logWeight ((B : ℝ) ^ rho) canonicalLogBump)
          (powerWeight b (N - blockPairLower B N) : ℂ)
          (powerWeight b (blockPairLower B N) : ℂ) N‖ ≤
      8 * b * (M * (Q : ℝ)) ^ 2 * (T : ℝ) ^ 2 / (B : ℝ) +
        8 * (Q : ℝ) ^ 4 * M ^ 2 := by
  dsimp only
  rcases blockPair_interval_geometry B N hBN hInterval with
    ⟨hAN, hend, hA, hNA, hleft, hright⟩
  rw [canonicalAdjustedModelAt_eq_adjustedBlockPairSum B N rho b e hR hBN]
  rw [adjustedBlockPairSum_eq_variablePowerPairInterval
    (log_cutoff_contains_one ((B : ℝ) ^ rho) hR)
    e.1 e.2
    (logWeight ((B : ℝ) ^ rho) canonicalLogBump)
    (logWeight ((B : ℝ) ^ rho) canonicalLogBump)
    b B N (by omega) hBN hInterval]
  exact variablePowerPairInterval_centered_norm_le
    (log_cutoff_contains_one ((B : ℝ) ^ rho) hR)
    e.1 e.2 hInv
    (logWeight ((B : ℝ) ^ rho) canonicalLogBump)
    (logWeight ((B : ℝ) ^ rho) canonicalLogBump)
    b N (blockPairLower B N)
    (blockPairUpper B N - blockPairLower B N + 1) B
    hB hb hAN hend hA hNA hleft hright
    M hM hw hw

end GoldbachCircleMethodCanonicalPairwiseBlockBindingV18326
