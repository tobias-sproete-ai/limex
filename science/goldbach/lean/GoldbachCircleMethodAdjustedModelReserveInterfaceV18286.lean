import GoldbachCircleMethodSupportedAdjustedModelBindingAuditV18285

/-!
# Goldbach V1.8.286: adjusted-model reserve interface

This module states the exact two-channel contract that remains after V1.8.285:
a lower reserve for the amplitude-aware unit-pair contribution and a norm loss
for the non-unit complement.  It proves only the ordered-complex transfer from
those explicit premises to the actual supported adjusted-model convolution.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodAdjustedModelReserveInterfaceV18286

open GoldbachCircleMethodActiveExceptionalCenteringV18129
open GoldbachCircleMethodLogCutoffPresieveBindingV18120
open GoldbachCircleMethodPrincipalWindowBoundaryV18121
open GoldbachCircleMethodBlockPairCarrierV18227
open GoldbachCircleMethodActiveResidualExactDecompositionV18251
open GoldbachCircleMethodSupportedAdjustedModelBindingAuditV18285
open GoldbachCircleMethodCanonicalBumpPrincipalFloorV18220

/-- Generic ordered-complex transfer: a positive channel minus a norm-bounded
uncontrolled channel leaves the displayed net reserve. -/
theorem two_channel_net_reserve
    (whole unitPart complement : ℂ) (reserve loss : ℝ)
    (hIdentity : whole = unitPart + complement)
    (hUnit : reserve ≤ unitPart.re)
    (hComplement : ‖complement‖ ≤ loss) :
    reserve - loss ≤ whole.re := by
  have hAbs : |complement.re| ≤ ‖complement‖ :=
    Complex.abs_re_le_norm complement
  have hLower : -loss ≤ complement.re := by
    have hNeg : -‖complement‖ ≤ complement.re := neg_le_of_abs_le hAbs
    linarith
  have hReal : whole.re = unitPart.re + complement.re := by
    simpa only [Complex.add_re] using congrArg Complex.re hIdentity
  linarith

/-- The exact reserve interface for the literal canonical adjusted model. -/
theorem canonicalAdjustedModelAt_net_reserve
    (B N : ℕ) (rho b reserve loss : ℝ)
    (e : CharacterSlot ⌊((B : ℝ)^rho)^2⌋₊)
    (hR : 1 < (B : ℝ)^rho) (hBN : B ≤ N)
    (hUnit : reserve ≤
      (amplitudeAdjustedUnitPairSum
        (log_cutoff_contains_one ((B : ℝ)^rho) hR)
        (blockCarrier B) e N b
        (logWeight ((B : ℝ)^rho) canonicalLogBump)).re)
    (hComplement :
      ‖amplitudeAdjustedNonUnitPairSum
        (log_cutoff_contains_one ((B : ℝ)^rho) hR)
        (blockCarrier B) e N b
        (logWeight ((B : ℝ)^rho) canonicalLogBump)‖ ≤ loss) :
    reserve - loss ≤
      (canonicalAdjustedModelAt B rho b e (N : ℤ)).re := by
  apply two_channel_net_reserve
    (canonicalAdjustedModelAt B rho b e (N : ℤ))
    (amplitudeAdjustedUnitPairSum
      (log_cutoff_contains_one ((B : ℝ)^rho) hR)
      (blockCarrier B) e N b
      (logWeight ((B : ℝ)^rho) canonicalLogBump))
    (amplitudeAdjustedNonUnitPairSum
      (log_cutoff_contains_one ((B : ℝ)^rho) hR)
      (blockCarrier B) e N b
      (logWeight ((B : ℝ)^rho) canonicalLogBump))
    reserve loss
  · exact canonicalAdjustedModelAt_nat_eq_unit_add_nonunit
      B N rho b e hR hBN
  · exact hUnit
  · exact hComplement

/-- Strict adjusted-model positivity follows exactly when the certified unit
reserve strictly exceeds the certified complement loss. -/
theorem canonicalAdjustedModelAt_pos_of_reserve_gt_loss
    (B N : ℕ) (rho b reserve loss : ℝ)
    (e : CharacterSlot ⌊((B : ℝ)^rho)^2⌋₊)
    (hR : 1 < (B : ℝ)^rho) (hBN : B ≤ N)
    (hUnit : reserve ≤
      (amplitudeAdjustedUnitPairSum
        (log_cutoff_contains_one ((B : ℝ)^rho) hR)
        (blockCarrier B) e N b
        (logWeight ((B : ℝ)^rho) canonicalLogBump)).re)
    (hComplement :
      ‖amplitudeAdjustedNonUnitPairSum
        (log_cutoff_contains_one ((B : ℝ)^rho) hR)
        (blockCarrier B) e N b
        (logWeight ((B : ℝ)^rho) canonicalLogBump)‖ ≤ loss)
    (hNet : loss < reserve) :
    0 < (canonicalAdjustedModelAt B rho b e (N : ℤ)).re := by
  have h := canonicalAdjustedModelAt_net_reserve
    B N rho b reserve loss e hR hBN hUnit hComplement
  linarith

end GoldbachCircleMethodAdjustedModelReserveInterfaceV18286
