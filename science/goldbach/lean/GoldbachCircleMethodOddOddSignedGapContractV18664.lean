import GoldbachCircleMethodOddOddSoleGateV18663
import GoldbachCircleMethodSignedMagnitudeIdentityV18628

/-!
# V1.8.664: exact signed-gap contract for the dense odd-odd gate

V1.8.663 isolates one still-open analytic premise: an eventual
`M^2 / 12544` negative-part moment bound for the literal dense odd-odd
subchannel.  V1.8.628 identifies every finite negative-part moment with one
half of the corresponding signed-magnitude gap.

This module specializes that identity to the exact V1.8.663 signal and proves
the threshold conversion `12544 <-> 6272`.  It supplies no estimate of the
signed gap and therefore records no analytic progress.

`proof_status = NO_PROOF`.
-/

set_option autoImplicit false

open Filter Topology
open GoldbachCircleMethodExceptionalTransferV1823
open GoldbachCircleMethodTwoScaleEvenBlockDefectReserveV1833
open GoldbachCircleMethodExplicitJordanDeficitV18651
open GoldbachCircleMethodOddChannelEventualAbsorptionV18658
open GoldbachCircleMethodEvenSubchannelSplitV18660
open GoldbachCircleMethodOddOddSoleGateV18663
open GoldbachCircleMethodSignedMagnitudeIdentityV18628

namespace GoldbachCircleMethodOddOddSignedGapContractV18664

/-- The exact real-valued dense odd-odd signal appearing in V1.8.663. -/
noncomputable def projectOddOddSignal (M : Nat) : Nat → Real :=
  fun N => -explicitOddOddSubchannelDeficit M
    (oddProjectWidth M) (oddProjectRadius M) N

/-- The exact finite signed-magnitude gap on the unchanged even target block. -/
noncomputable def projectOddOddSignedGap (M : Nat) : Real :=
  squareEnergy (evenTargetBlock M) (projectOddOddSignal M) -
    signedMagnitudeCorrelation (evenTargetBlock M) (projectOddOddSignal M)

/-- The smallest honest analytic contract equivalent to the sole V1.8.663
premise.  No inhabitant is constructed in this module. -/
def ProjectOddOddSignedGapContract : Prop :=
  ∀ᶠ M : Nat in atTop,
    projectOddOddSignedGap M < (M : Real) ^ 2 / 6272

/-- Exact pointwise threshold conversion.  This is an algebraic translation,
not an estimate for the dense odd-odd channel. -/
theorem project_oddOdd_moment_lt_iff_signedGap (M : Nat) :
    negativePartSquaredMoment (evenTargetBlock M) (projectOddOddSignal M) <
        (M : Real) ^ 2 / 12544 ↔
      projectOddOddSignedGap M < (M : Real) ^ 2 / 6272 := by
  unfold projectOddOddSignedGap
  rw [negativePartSquaredMoment_eq_half_signed_gap]
  constructor <;> intro h <;> nlinarith

/-- The eventual V1.8.663 premise and the signed-gap contract are exactly
equivalent; no asymptotic input is added. -/
theorem project_oddOdd_eventual_moment_gate_iff_signedGapContract :
    (∀ᶠ M : Nat in atTop,
      negativePartSquaredMoment (evenTargetBlock M) (projectOddOddSignal M) <
        (M : Real) ^ 2 / 12544) ↔
      ProjectOddOddSignedGapContract := by
  constructor
  · intro hMoment
    unfold ProjectOddOddSignedGapContract
    filter_upwards [hMoment] with M hM
    exact (project_oddOdd_moment_lt_iff_signedGap M).1 hM
  · intro hGap
    unfold ProjectOddOddSignedGapContract at hGap
    filter_upwards [hGap] with M hM
    exact (project_oddOdd_moment_lt_iff_signedGap M).2 hM

/-- Exact composition with V1.8.663.  The conclusion remains conditional on
the unproved signed-gap contract. -/
theorem project_totalJordan_eventually_lt_one_over_784_of_oddOddSignedGap
    (hGap : ProjectOddOddSignedGapContract) :
    ∀ᶠ M : Nat in atTop,
      explicitJordanDeficitSquaredMoment M
          (oddProjectWidth M) (oddProjectRadius M) (evenTargetBlock M) <
        (M : Real) ^ 2 / 784 := by
  apply project_totalJordan_eventually_lt_one_over_784_of_oddOdd
  have hMoment :=
    (project_oddOdd_eventual_moment_gate_iff_signedGapContract).2 hGap
  exact hMoment

end GoldbachCircleMethodOddOddSignedGapContractV18664
