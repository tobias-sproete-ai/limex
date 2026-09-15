import GoldbachCircleMethodAdjustedModelFourChannelPartitionV18292

/-!
# Goldbach V1.8.293: canonical adjusted four-channel binding

The four-channel partition is attached to the actual V1.8.251 canonical
supported adjusted model at a natural target.  Its two open quantitative
obligations are exposed directly in a positivity theorem for that model.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodCanonicalAdjustedFourChannelBindingV18293

open GoldbachCircleMethodActiveExceptionalCenteringV18129
open GoldbachCircleMethodLogCutoffPresieveBindingV18120
open GoldbachCircleMethodPrincipalWindowBoundaryV18121
open GoldbachCircleMethodCanonicalBumpPrincipalFloorV18220
open GoldbachCircleMethodActiveResidualExactDecompositionV18251
open GoldbachCircleMethodSupportedAdjustedModelBindingAuditV18285
open GoldbachCircleMethodAdjustedModelFourChannelPartitionV18292

/-- Exact four-channel identity for the literal canonical adjusted model. -/
theorem canonicalAdjustedModelAt_nat_eq_localized_add_offDivisorRemainder
    (B N : ℕ) (rho b : ℝ)
    (e : CharacterSlot ⌊((B : ℝ)^rho)^2⌋₊)
    (hR : 1 < (B : ℝ)^rho) (hBN : B ≤ N) :
    canonicalAdjustedModelAt B rho b e (N : ℤ) =
      localizedLocalizedPairSum
          (log_cutoff_contains_one ((B : ℝ)^rho) hR)
          (blockCarrier B) e N b
          (logWeight ((B : ℝ)^rho) canonicalLogBump) +
        offDivisorPairRemainder
          (log_cutoff_contains_one ((B : ℝ)^rho) hR)
          (blockCarrier B) e N b
          (logWeight ((B : ℝ)^rho) canonicalLogBump) := by
  rw [canonicalAdjustedModelAt_nat_eq_amplitudeAdjustedFullPairSum
    B N rho b e hR hBN]
  exact amplitudeAdjustedFullPairSum_eq_localized_add_offDivisorRemainder
    (log_cutoff_contains_one ((B : ℝ)^rho) hR)
    (blockCarrier B) e N b
    (logWeight ((B : ℝ)^rho) canonicalLogBump)

/-- Canonical-model net reserve after the complete off-divisor remainder. -/
theorem canonicalAdjustedModelAt_nat_re_ge_localized_sub_remainderNorm
    (B N : ℕ) (rho b : ℝ)
    (e : CharacterSlot ⌊((B : ℝ)^rho)^2⌋₊)
    (hR : 1 < (B : ℝ)^rho) (hBN : B ≤ N) :
    (localizedLocalizedPairSum
          (log_cutoff_contains_one ((B : ℝ)^rho) hR)
          (blockCarrier B) e N b
          (logWeight ((B : ℝ)^rho) canonicalLogBump)).re -
        ‖offDivisorPairRemainder
          (log_cutoff_contains_one ((B : ℝ)^rho) hR)
          (blockCarrier B) e N b
          (logWeight ((B : ℝ)^rho) canonicalLogBump)‖ ≤
      (canonicalAdjustedModelAt B rho b e (N : ℤ)).re := by
  rw [canonicalAdjustedModelAt_nat_eq_amplitudeAdjustedFullPairSum
    B N rho b e hR hBN]
  exact amplitudeAdjustedFullPairSum_re_ge_localized_sub_remainderNorm
    (log_cutoff_contains_one ((B : ℝ)^rho) hR)
    (blockCarrier B) e N b
    (logWeight ((B : ℝ)^rho) canonicalLogBump)

/-- Fail-closed positivity interface for the actual canonical model. -/
theorem canonicalAdjustedModelAt_nat_re_pos_of_two_channel_budget
    (B N : ℕ) (rho b reserve : ℝ)
    (e : CharacterSlot ⌊((B : ℝ)^rho)^2⌋₊)
    (hR : 1 < (B : ℝ)^rho) (hBN : B ≤ N)
    (hmain : reserve ≤
      (localizedLocalizedPairSum
        (log_cutoff_contains_one ((B : ℝ)^rho) hR)
        (blockCarrier B) e N b
        (logWeight ((B : ℝ)^rho) canonicalLogBump)).re)
    (hloss : ‖offDivisorPairRemainder
        (log_cutoff_contains_one ((B : ℝ)^rho) hR)
        (blockCarrier B) e N b
        (logWeight ((B : ℝ)^rho) canonicalLogBump)‖ < reserve) :
    0 < (canonicalAdjustedModelAt B rho b e (N : ℤ)).re := by
  rw [canonicalAdjustedModelAt_nat_eq_amplitudeAdjustedFullPairSum
    B N rho b e hR hBN]
  exact amplitudeAdjustedFullPairSum_re_pos_of_localized_reserve
    (log_cutoff_contains_one ((B : ℝ)^rho) hR)
    (blockCarrier B) e N b
    (logWeight ((B : ℝ)^rho) canonicalLogBump) reserve hmain hloss

end GoldbachCircleMethodCanonicalAdjustedFourChannelBindingV18293
