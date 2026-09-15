import GoldbachCircleMethodLocalizedShapeIntervalAdapterV18309

/-!
# Goldbach V1.8.310: canonical localized interval factorization

This module composes the exact canonical factorization from V1.8.308 with the
endpoint-preserving carrier adapter from V1.8.309.  The actual localized-localized
channel is thereby identified with the pre-existing literal unit-pair interval,
up to its explicit squared totient scale.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodCanonicalLocalizedIntervalFactorizationV18310

open GoldbachCircleMethodActiveExceptionalCenteringV18129
open GoldbachCircleMethodBlockPairCarrierV18227
open GoldbachCircleMethodCanonicalBumpPrincipalFloorV18220
open GoldbachCircleMethodLogCutoffPresieveBindingV18120
open GoldbachCircleMethodAdjustedModelFourChannelPartitionV18292
open GoldbachCircleMethodLocalizedReducedPairExactFactorizationV18308
open GoldbachCircleMethodLocalizedShapeIntervalAdapterV18309
open GoldbachCircleMethodVariableWeightIntervalDiscrepancyV18272

/-- Exact canonical localized-localized block channel as the literal variable
unit-pair interval, with no frozen-weight or positivity substitution. -/
theorem localizedLocalizedPairSum_canonical_block_eq_scale_mul_variableInterval
    {Q : ℕ} (hQ : 1 ≤ Q) (B N : ℕ) (e : CharacterSlot Q)
    (b R : ℝ) (hR : 1 < R) (hactiveR : (e.1.val : ℝ) ≤ R)
    (hB : 1 ≤ B) (hBN : B ≤ N)
    (hInterval : blockPairLower B N ≤ blockPairUpper B N) :
    localizedLocalizedPairSum hQ (blockCarrier B) e N b
        (logWeight R canonicalLogBump) =
      localizedTotientScale e.1 * localizedTotientScale e.1 *
        variableUnitPairInterval e.1.val N (blockPairLower B N)
          (blockPairUpper B N - blockPairLower B N + 1) e.2.val b := by
  rw [localizedLocalizedPairSum_canonical_eq_scale_mul_reducedShapeSum
    hQ (blockCarrier B) e N b R hR hactiveR]
  rw [localizedReducedPairShapeSum_block_eq_variableUnitPairInterval
    B N e b hB hBN hInterval]

end GoldbachCircleMethodCanonicalLocalizedIntervalFactorizationV18310
