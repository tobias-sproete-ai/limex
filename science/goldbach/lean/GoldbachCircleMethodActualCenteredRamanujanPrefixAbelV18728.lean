import GoldbachCircleMethodActualMixedChannelRamanujanFactorizationV18727
import GoldbachCircleMethodSharpSourceSincVariationV18721
import GoldbachCircleMethodSelectedPairLocalPeriodAbelAdapterV18691

/-!
# V1.8.728: actual centered Ramanujan prefix and exact Abel identity

This append-only module defines the canonical finite prefix of the genuine
centered Lambda-pair source against the negative-orientation Ramanujan atom.
The positive orientation is identified with it only after the two literal
unit-mode aggregations of V1.8.727, through a separately proved sign-evenness
theorem for the finite Ramanujan sum.

Under the literal target gate, membership in the source carrier follows from
`Finset.range M.succ`; at the moving notch, the literal two-radius sinc is
exactly zero.  Consequently both centered unit aggregates have the same exact
finite summation-by-parts representation, with every prefix, endpoint, and
first difference retained.

V1.8.721 supplies endpoint and total-variation control for the sinc weight.
It does not supply a quantitative bound for the actual centered Ramanujan
prefix defined here.  No prefix estimate, channel smallness, absorption, or
Goldbach conclusion is asserted.  `proof_status = NO_PROOF`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

open scoped BigOperators Classical

namespace GoldbachCircleMethodActualCenteredRamanujanPrefixAbelV18728

open GoldbachCircleMethodTwoScaleEvenBlockDefectReserveV1833
open GoldbachCircleMethodOddOddSignedFiberAdapterV18665
open GoldbachCircleMethodOddChannelEventualAbsorptionV18658
open GoldbachCircleMethodFullDenominatorFourClassPartitionV18688
open GoldbachCircleMethodActualDemodulatedOneFiberRelativeConvolutionV18710
open GoldbachCircleMethodExactLambdaPairSourceMeanSplitV18716
open GoldbachCircleMethodActualLambdaPairSourceMeanV710AdapterV18717
open GoldbachCircleMethodSharpSourceSincVariationV18721
open GoldbachCircleMethodSelectedPairLocalPeriodAbelAdapterV18691
open GoldbachCircleMethodActualMixedChannelRamanujanFactorizationV18727
open GoldbachCircleMethodFiniteResiduePrefixV1866

/-- The canonical actual centered Ramanujan atom.  Its orientation is fixed as
the literal negative-unit frequency `2*(s-n)` obtained in V1.8.727. -/
noncomputable def actualCenteredRamanujanAtom
    (M : Nat)
    (q : PairedOddBase (oddProjectRadius M))
    (n s : Nat) : Complex :=
  (centeredActualLambdaPairSource M s : Complex) *
    unitCharacterSum q.val.val
      (((2 * ((s : Int) - (n : Int)) : Int) : ZMod q.val.val))

/-- Canonical finite prefix of the genuine centered source against the exact
Ramanujan atom.  No norm estimate is built into this definition. -/
noncomputable def actualCenteredRamanujanPrefix
    (M : Nat)
    (q : PairedOddBase (oddProjectRadius M))
    (n k : Nat) : Complex :=
  ∑ s ∈ Finset.range k, actualCenteredRamanujanAtom M q n s

/-- Exact sign-evenness bridge between the two frequencies produced by the
separate negative and positive unit aggregations. -/
theorem unitCharacterSum_two_sub_sign_even
    (M : Nat)
    (q : PairedOddBase (oddProjectRadius M))
    (n s : Nat) :
    unitCharacterSum q.val.val
        (((2 * ((n : Int) - (s : Int)) : Int) : ZMod q.val.val)) =
      unitCharacterSum q.val.val
        (((2 * ((s : Int) - (n : Int)) : Int) : ZMod q.val.val)) := by
  have h := unitCharacterSum_intCast_neg_eq q.val.val
    (2 * ((s : Int) - (n : Int)))
  simpa only [show
      2 * ((n : Int) - (s : Int)) =
        -(2 * ((s : Int) - (n : Int))) by ring] using h

/-- Under the unchanged target gate, the negative Ramanujan transform is the
sinc-weighted sum of the canonical actual centered atoms. -/
theorem selectedPairNegativeCenteredRamanujanTransform_eq_sinc_atom_sum
    (M : Nat)
    (q : PairedOddBase (oddProjectRadius M))
    (n : Nat)
    (hTarget : 2 * n ∈ evenTargetBlock M) :
    selectedPairNegativeCenteredRamanujanTransform M q n =
      ∑ s ∈ Finset.range M.succ,
        selectedPairSourceCoordinateSincWeight M q n s *
          actualCenteredRamanujanAtom M q n s := by
  unfold selectedPairNegativeCenteredRamanujanTransform
  apply Finset.sum_congr rfl
  intro s hs
  have hCarrier := two_mul_mem_oddOddSumCarrier_of_mem_range_succ hs
  by_cases hsn : s = n
  · subst s
    simp [hTarget, selectedPairSourceCoordinateSincWeight,
      selectedPairRelativeTwoRadiusSinc_self_eq_zero,
      actualCenteredRamanujanAtom]
  · have hNotch : 2 * s ≠ 2 * n := by omega
    simp only [hTarget, hCarrier, true_and]
    rw [if_pos hNotch]
    unfold selectedPairSourceCoordinateSincWeight actualCenteredRamanujanAtom
    ring

/-- Under the same target gate, the independently retained positive transform
has the canonical negative-orientation atom only after sign-evenness is used. -/
theorem selectedPairPositiveCenteredRamanujanTransform_eq_sinc_atom_sum
    (M : Nat)
    (q : PairedOddBase (oddProjectRadius M))
    (n : Nat)
    (hTarget : 2 * n ∈ evenTargetBlock M) :
    selectedPairPositiveCenteredRamanujanTransform M q n =
      ∑ s ∈ Finset.range M.succ,
        selectedPairSourceCoordinateSincWeight M q n s *
          actualCenteredRamanujanAtom M q n s := by
  unfold selectedPairPositiveCenteredRamanujanTransform
  apply Finset.sum_congr rfl
  intro s hs
  have hCarrier := two_mul_mem_oddOddSumCarrier_of_mem_range_succ hs
  by_cases hsn : s = n
  · subst s
    simp [hTarget, selectedPairSourceCoordinateSincWeight,
      selectedPairRelativeTwoRadiusSinc_self_eq_zero,
      actualCenteredRamanujanAtom]
  · have hNotch : 2 * s ≠ 2 * n := by omega
    simp only [hTarget, hCarrier, true_and]
    rw [if_pos hNotch]
    rw [unitCharacterSum_two_sub_sign_even M q n s]
    unfold selectedPairSourceCoordinateSincWeight actualCenteredRamanujanAtom
    ring

/-- Exact finite Abel identity for the sinc-weighted actual centered
Ramanujan atoms.  Prefixes and first differences remain unbounded. -/
theorem sinc_actualCenteredRamanujanAtom_sum_eq_endpoint_sub_variations
    (M : Nat)
    (q : PairedOddBase (oddProjectRadius M))
    (n : Nat) :
    (∑ s ∈ Finset.range M.succ,
        selectedPairSourceCoordinateSincWeight M q n s *
          actualCenteredRamanujanAtom M q n s) =
      selectedPairSourceCoordinateSincWeight M q n M *
          actualCenteredRamanujanPrefix M q n M.succ -
        ∑ a ∈ Finset.range M,
          selectedPairSourceCoordinateSincVariation M q n a *
            actualCenteredRamanujanPrefix M q n (a + 1) := by
  have habel := Finset.sum_range_by_parts
    (selectedPairSourceCoordinateSincWeight M q n)
    (actualCenteredRamanujanAtom M q n)
    M.succ
  simp only [Nat.succ_sub_one, smul_eq_mul] at habel
  simpa [actualCenteredRamanujanPrefix,
    selectedPairSourceCoordinateSincVariation] using habel

/-- Exact Abel representation of the negative centered unit aggregate under
the literal target gate. -/
theorem selectedPairNegativeCenteredUnitAggregate_eq_endpoint_sub_actualCenteredRamanujanPrefixes
    (M : Nat)
    (q : PairedOddBase (oddProjectRadius M))
    (n : Nat)
    (hTarget : 2 * n ∈ evenTargetBlock M) :
    selectedPairNegativeCenteredUnitAggregate M q n =
      selectedPairSourceCoordinateSincWeight M q n M *
          actualCenteredRamanujanPrefix M q n M.succ -
        ∑ a ∈ Finset.range M,
          selectedPairSourceCoordinateSincVariation M q n a *
            actualCenteredRamanujanPrefix M q n (a + 1) := by
  rw [selectedPairNegativeCenteredUnitAggregate_eq_ramanujanTransform]
  rw [selectedPairNegativeCenteredRamanujanTransform_eq_sinc_atom_sum
    M q n hTarget]
  exact sinc_actualCenteredRamanujanAtom_sum_eq_endpoint_sub_variations M q n

/-- Exact Abel representation of the positive centered unit aggregate.  The
sign bridge is theorematic and occurs after its independent V1.8.727 unit
aggregation. -/
theorem selectedPairPositiveCenteredUnitAggregate_eq_endpoint_sub_actualCenteredRamanujanPrefixes
    (M : Nat)
    (q : PairedOddBase (oddProjectRadius M))
    (n : Nat)
    (hTarget : 2 * n ∈ evenTargetBlock M) :
    selectedPairPositiveCenteredUnitAggregate M q n =
      selectedPairSourceCoordinateSincWeight M q n M *
          actualCenteredRamanujanPrefix M q n M.succ -
        ∑ a ∈ Finset.range M,
          selectedPairSourceCoordinateSincVariation M q n a *
            actualCenteredRamanujanPrefix M q n (a + 1) := by
  rw [selectedPairPositiveCenteredUnitAggregate_eq_ramanujanTransform]
  rw [selectedPairPositiveCenteredRamanujanTransform_eq_sinc_atom_sum
    M q n hTarget]
  exact sinc_actualCenteredRamanujanAtom_sum_eq_endpoint_sub_variations M q n

end GoldbachCircleMethodActualCenteredRamanujanPrefixAbelV18728
