import GoldbachCircleMethodCanonicalLocalizedIntervalReserveV18311
import GoldbachCircleMethodCanonicalAdjustedFourChannelBindingV18293

/-!
# Goldbach V1.8.312: canonical adjusted-model explicit reserve

This module transports the V1.8.311 localized reserve through the exact
four-channel decomposition of the actual canonical adjusted model.  Every
known loss remains explicit, including the complete norm of the three
off-divisor channels.  No positivity or absorption claim is made.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodCanonicalAdjustedModelExplicitReserveV18312

open GoldbachCircleMethodAdjustedModelFourChannelPartitionV18292
open GoldbachCircleMethodActiveResidualExactDecompositionV18251
open GoldbachCircleMethodBlockPairCarrierV18227
open GoldbachCircleMethodCanonicalAdjustedFourChannelBindingV18293
open GoldbachCircleMethodCanonicalBumpPrincipalFloorV18220
open GoldbachCircleMethodCanonicalLocalizedIntervalReserveV18311
open GoldbachCircleMethodExceptionalZeroGapAttestationRepairV18263
open GoldbachCircleMethodLogCutoffPresieveBindingV18120
open GoldbachCircleMethodPrincipalWindowBoundaryV18121
open GoldbachCircleMethodStructurallyAdmissibleActiveSlotV18258
open GoldbachCircleMethodActualUnitPairArithmeticV18194
open GoldbachCircleMethodZeroGapReserveScaleV18266

/-- The actual canonical adjusted model has the localized zero-gap reserve
minus the literal terminal, spatial variation, and full off-divisor costs. -/
theorem canonicalAdjustedModelAt_zeroGap_explicit_floor
    (B N : ℕ) (rho : ℝ)
    {ExceptionalZeroAt :
      StructurallyAdmissibleActiveSlot ⌊((B : ℝ) ^ rho) ^ 2⌋₊ → ℝ → Prop}
    (d : ExceptionalZeroGapAttestation
      ⌊((B : ℝ) ^ rho) ^ 2⌋₊ ExceptionalZeroAt)
    (hr3 : 3 < d.slot.val.1.val) (hEven : Even N)
    (hB : 4 ≤ B) (hBN : B ≤ N)
    (hInterval : blockPairLower B N ≤ blockPairUpper B N)
    (hR : 1 < (B : ℝ) ^ rho)
    (hactiveR : (d.slot.val.1.val : ℝ) ≤ (B : ℝ) ^ rho) :
    let T := blockPairUpper B N - blockPairLower B N + 1
    (((d.slot.val.1.val : ℝ) /
          (d.slot.val.1.val.totient : ℝ)) ^ 2) *
          ((((T / d.slot.val.1.val : ℕ) : ℝ) *
                ((unitPairCount d.slot.val.1.val (N : ℤ) : ℝ) *
                  zeroGapReserveScale d.zeroGap B / 6) -
              4 * ((T % d.slot.val.1.val : ℕ) : ℝ) -
              8 * d.zeroGap * (T : ℝ) ^ 2 / (B : ℝ))) -
        ‖offDivisorPairRemainder
          (log_cutoff_contains_one ((B : ℝ) ^ rho) hR)
          (blockCarrier B) d.slot.val N d.zeroGap
          (logWeight ((B : ℝ) ^ rho) canonicalLogBump)‖ ≤
      (canonicalAdjustedModelAt B rho d.zeroGap d.slot.val (N : ℤ)).re := by
  dsimp only
  let hQ := log_cutoff_contains_one ((B : ℝ) ^ rho) hR
  have hlocalized := canonical_localized_pair_reserve_with_costs
    hQ d B N ((B : ℝ) ^ rho) hr3 hEven hB hBN hInterval hR hactiveR
  have hmodel := canonicalAdjustedModelAt_nat_re_ge_localized_sub_remainderNorm
    B N rho d.zeroGap d.slot.val hR hBN
  dsimp only [hQ] at hlocalized
  linarith

end GoldbachCircleMethodCanonicalAdjustedModelExplicitReserveV18312
