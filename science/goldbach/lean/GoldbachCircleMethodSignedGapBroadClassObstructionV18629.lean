import GoldbachCircleMethodSignedMagnitudeIdentityV18628
import GoldbachCircleMethodOriginalMaskCountermodelBindingV1882

/-!
# V1.8.629: broad-class obstruction for the signed-gap gate

V1.8.628 rewrites the one-sided negative moment as an exact signed-magnitude
gap.  V1.8.81--82 already provide a non-arithmetic comparator on the unchanged
minor mask showing that support and masked L2 energy alone cannot force an
arbitrarily small negative-part moment.  This module composes those two facts.

The conclusion is deliberately limited: it rules out a proof from the broad
support-and-energy class.  It says nothing adverse about the actual Lambda
square, whose arithmetic coefficient structure is much narrower.

`proof_status = NO_PROOF`.
-/
set_option autoImplicit false

open scoped BigOperators Classical
open MeasureTheory AddCircle Filter Topology
open GoldbachCircleMethodExceptionalTransferV1823
open GoldbachCircleMethodTwoScaleIntegralPartitionV1831
open GoldbachCircleMethodTwoScaleMaskAdapterV1829
open GoldbachCircleMethodCeilScaleEnvelopesV1864
open GoldbachCircleMethodMaskedFrequencyCountermodelV1881
open GoldbachCircleMethodOriginalMaskCountermodelBindingV1882
open GoldbachCircleMethodSignedMagnitudeIdentityV18628

namespace GoldbachCircleMethodSignedGapBroadClassObstructionV18629

/-- The V1.8.81 masked comparator also rejects the equivalent small signed-gap
claim.  No arithmetic realizability is asserted. -/
theorem negativeMaskedMode_rejects_small_signedGap
    (s : Set UnitAddCircle) (hs : MeasurableSet s)
    (hpos : 0 < haarAddCircle.real s)
    (T : Finset ℕ) (n : ℕ) (hn : n ∈ T) (ε : ℝ)
    (hε : ε < haarAddCircle.real s) :
    let H : ℕ → ℝ := fun N =>
      (fourierCoeff (negativeMaskedMode s n) (N : ℤ)).re
    let E : ℝ := ∫ x : UnitAddCircle, ‖negativeMaskedMode s n x‖ ^ 2 ∂haarAddCircle
    ¬ (squareEnergy T H - signedMagnitudeCorrelation T H ≤ 2 * ε * E) := by
  dsimp only
  intro hGap
  apply masked_mode_rejects_small_factor s hs hpos T n hn ε hε
  rw [negativePartSquaredMoment_eq_half_signed_gap]
  nlinarith

/-- On the unchanged logarithmic minor mask, every fixed factor below one is
eventually rejected by a comparator in the broad masked-L2 class.  Therefore a
uniform signed-gap estimate must use arithmetic structure of the actual Lambda
square, not mask support and total energy alone. -/
theorem eventually_original_mask_rejects_fixed_signedGap
    (K : ℕ) (ε : ℝ) (hε : ε < 1) :
    ∀ᶠ M : ℕ in atTop, ∀ (T : Finset ℕ) (n : ℕ), n ∈ T →
      let s := twoScaleMinorMask M (logWidth K M) (logRadius K M)
      let H : ℕ → ℝ := fun N =>
        (fourierCoeff (negativeMaskedMode s n) (N : ℤ)).re
      let E : ℝ := ∫ x : UnitAddCircle, ‖negativeMaskedMode s n x‖ ^ 2 ∂haarAddCircle
      ¬ (squareEnergy T H - signedMagnitudeCorrelation T H ≤ 2 * ε * E) := by
  have hOld := eventually_original_mask_rejects_fixed_factor K ε hε
  filter_upwards [hOld] with M hM
  intro T n hn
  dsimp only
  intro hGap
  apply hM T n hn
  rw [negativePartSquaredMoment_eq_half_signed_gap]
  nlinarith

end GoldbachCircleMethodSignedGapBroadClassObstructionV18629
