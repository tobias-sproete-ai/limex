import GoldbachCircleMethodTwoScalePrincipalChannelBoundsV18240

/-!
# Goldbach V1.8.241: two-scale centered-contract mismatch

The two source scales repaired the literal convolution geometry and suffice
for the principal-model reserve.  They do not cover the full dyadic target
block inside the separate `[5B/4,7B/4]` target band required by the existing
V1.8.184 centered-error estimate.  Concrete finite witnesses prevent this
signature mismatch from being hidden by asymptotic prose.
-/

set_option autoImplicit false

namespace GoldbachCircleMethodTwoScaleCenteredContractMismatchV18241

open GoldbachCircleMethodTwoScaleEvenBlockDefectReserveV1833
open GoldbachCircleMethodTwoSourceScaleCoverV18232

/-- The lower endpoint of a concrete dyadic block belongs to the target
carrier but violates the lower `5B ≤ 4N` side of the V1.8.184 contract at
both old source scales. -/
theorem lower_endpoint_not_covered_by_old_centered_contract :
    32 ∈ evenTargetBlock 64 ∧
      ¬ (5 * lowerSourceScale 64 ≤ 4 * 32) ∧
      ¬ (5 * upperSourceScale 64 ≤ 4 * 32) := by
  norm_num [evenTargetBlock, lowerSourceScale, upperSourceScale]

/-- The upper endpoint of the same block violates the upper `4N ≤ 7B`
side of the V1.8.184 contract at both old source scales. -/
theorem upper_endpoint_not_covered_by_old_centered_contract :
    64 ∈ evenTargetBlock 64 ∧
      ¬ (4 * 64 ≤ 7 * lowerSourceScale 64) ∧
      ¬ (4 * 64 ≤ 7 * upperSourceScale 64) := by
  norm_num [evenTargetBlock, lowerSourceScale, upperSourceScale]

/-- Consequently, the two old source scales do not cover every target in
the block by the exact centered-error estimate signature. -/
theorem old_two_scales_do_not_cover_centered_contract :
    ¬ ∀ N ∈ evenTargetBlock 64,
      (5 * lowerSourceScale 64 ≤ 4 * N ∧
        4 * N ≤ 7 * lowerSourceScale 64) ∨
      (5 * upperSourceScale 64 ≤ 4 * N ∧
        4 * N ≤ 7 * upperSourceScale 64) := by
  intro h
  have h32 := h 32 lower_endpoint_not_covered_by_old_centered_contract.1
  rcases h32 with hLow | hHigh
  · exact lower_endpoint_not_covered_by_old_centered_contract.2.1 hLow.1
  · exact lower_endpoint_not_covered_by_old_centered_contract.2.2 hHigh.1

end GoldbachCircleMethodTwoScaleCenteredContractMismatchV18241

