import GoldbachCircleMethodActualQ3UnitDifferenceCharacterAdapterV18757
import GoldbachCircleMethodEvenEvenChannelCompositionV18661

/-!
# V1.8.758: full q=3 character prefix and even correction

V1.8.757 identifies the actual odd-carrier discrepancy with a single finite
nonprincipal residue-table sum.  Standard fixed-modulus distribution results
are naturally stated for the full von-Mangoldt prefix, not for the odd-only
carrier.  This append-only module closes that domain mismatch exactly.

The full prefix is the sum of the actual odd prefix and its literal even
correction.  The correction is bounded by the already kernel-checked
power-of-two Mangoldt budget `log M`.  No bound for the full nonprincipal
character prefix is asserted or inhabited.  `proof_status = NO_PROOF`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

open scoped BigOperators Classical ArithmeticFunction.vonMangoldt

namespace GoldbachCircleMethodActualQ3FullCharacterEvenCorrectionV18758

open GoldbachCircleMethodTwoScaleEvenBlockDefectReserveV1833
open GoldbachCircleMethodOddChannelEventualAbsorptionV18658
open GoldbachCircleMethodFullDenominatorFourClassPartitionV18688
open GoldbachCircleMethodOddOddFourierBesselBridgeV18668
open GoldbachCircleMethodActualMixedChannelRamanujanFactorizationV18727
open GoldbachCircleMethodActualOddLambdaQ3ResidueDiscrepancyV18752
open GoldbachCircleMethodActualQ3PrefixLocalDensityExtractionV18753
open GoldbachCircleMethodActualQ3UnitClassDifferenceV18754
open GoldbachCircleMethodActualQ3PrefixLocalDensitySignedReserveV18755
open GoldbachCircleMethodActualQ3UnitDifferenceScaleEnvelopeV18756
open GoldbachCircleMethodActualQ3UnitDifferenceCharacterAdapterV18757
open GoldbachCircleMethodArithmeticHalfShiftV1883
open GoldbachCircleMethodEvenEvenChannelCompositionV18661

/-- Full finite von-Mangoldt prefix against the q=3 nonprincipal residue
table, retaining the ambient endpoint `M`. -/
noncomputable def fullLambdaQ3CharacterPrefix
    (M B : Nat) : Complex :=
  ∑ a ∈ Finset.range M.succ,
    if a < B then
      (ArithmeticFunction.vonMangoldt a : Complex) *
        q3UnitDifferenceCharacterTable (a : ZMod 3)
    else 0

/-- Literal even-coordinate correction on the same finite prefix. -/
noncomputable def evenLambdaQ3CharacterPrefix
    (M B : Nat) : Complex :=
  ∑ a ∈ (Finset.range M.succ).filter Even,
    if a < B then
      (ArithmeticFunction.vonMangoldt a : Complex) *
        q3UnitDifferenceCharacterTable (a : ZMod 3)
    else 0

theorem fullLambdaQ3CharacterPrefix_eq_odd_add_even
    (M B : Nat) :
    fullLambdaQ3CharacterPrefix M B =
      oddLambdaQ3UnitDifferenceCharacterPrefix M B +
        evenLambdaQ3CharacterPrefix M B := by
  unfold fullLambdaQ3CharacterPrefix
    oddLambdaQ3UnitDifferenceCharacterPrefix
    evenLambdaQ3CharacterPrefix oddCarrier
  simpa only [Nat.not_odd_iff_even] using
    (Finset.sum_filter_add_sum_filter_not
      (Finset.range M.succ) Odd
      (fun a =>
        if a < B then
          (ArithmeticFunction.vonMangoldt a : Complex) *
            q3UnitDifferenceCharacterTable (a : ZMod 3)
        else 0)).symm

theorem oddLambdaQ3UnitDifferenceCharacterPrefix_eq_full_sub_even
    (M B : Nat) :
    oddLambdaQ3UnitDifferenceCharacterPrefix M B =
      fullLambdaQ3CharacterPrefix M B -
        evenLambdaQ3CharacterPrefix M B := by
  rw [fullLambdaQ3CharacterPrefix_eq_odd_add_even]
  ring

theorem q3UnitDifferenceCharacterTable_norm_le_one
    (r : ZMod 3) :
    ‖q3UnitDifferenceCharacterTable r‖ ≤ 1 := by
  by_cases h1 : r = 1
  · simp [q3UnitDifferenceCharacterTable, h1]
  · by_cases h2 : r = 2
    · have h21 : (2 : ZMod 3) ≠ 1 := by decide
      simp [q3UnitDifferenceCharacterTable, h2, h21]
    · simp [q3UnitDifferenceCharacterTable, h1, h2]

/-- The full-to-odd domain correction costs at most the existing logarithmic
even Mangoldt mass. -/
theorem evenLambdaQ3CharacterPrefix_norm_le_log
    (M B : Nat) (hM : 0 < M) :
    ‖evenLambdaQ3CharacterPrefix M B‖ ≤ Real.log (M : Real) := by
  unfold evenLambdaQ3CharacterPrefix
  calc
    _ ≤ ∑ a ∈ (Finset.range M.succ).filter Even,
        ‖if a < B then
            (ArithmeticFunction.vonMangoldt a : Complex) *
              q3UnitDifferenceCharacterTable (a : ZMod 3)
          else 0‖ := norm_sum_le _ _
    _ ≤ ∑ a ∈ (Finset.range M.succ).filter Even,
        ArithmeticFunction.vonMangoldt a := by
      apply Finset.sum_le_sum
      intro a _ha
      by_cases hB : a < B
      · simp only [hB, if_true, norm_mul]
        have hLambda :
            ‖(ArithmeticFunction.vonMangoldt a : Complex)‖ =
              ArithmeticFunction.vonMangoldt a := by
          rw [Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
        rw [hLambda]
        exact mul_le_of_le_one_right ArithmeticFunction.vonMangoldt_nonneg
          (q3UnitDifferenceCharacterTable_norm_le_one (a : ZMod 3))
      · simp [hB, ArithmeticFunction.vonMangoldt_nonneg]
    _ = evenMangoldtMass M := evenPrefixMangoldtMass_eq M
    _ ≤ Real.log (M : Real) := evenMangoldtMass_le_log M hM

/-- Literature-facing contract for the full fixed-modulus nonprincipal
von-Mangoldt prefix.  It remains an open proposition. -/
def ActualFullLambdaQ3CharacterPrefixCeiling
    (M : Nat) (D : Real) : Prop :=
  0 ≤ D ∧ ∀ B : Nat, ‖fullLambdaQ3CharacterPrefix M B‖ ≤ D

/-- Exact transfer from a full-prefix ceiling to the actual odd-prefix
ceiling, with the explicit logarithmic power-of-two correction. -/
theorem fullCharacterPrefixCeiling_implies_oddCharacterPrefixCeiling
    (M : Nat) (hM : 0 < M) (D : Real)
    (hD : ActualFullLambdaQ3CharacterPrefixCeiling M D) :
    ActualOddLambdaQ3CharacterPrefixCeiling M
      (D + Real.log (M : Real)) := by
  have hlog : 0 ≤ Real.log (M : Real) :=
    Real.log_nonneg (by exact_mod_cast hM)
  refine ⟨add_nonneg hD.1 hlog, ?_⟩
  intro B
  rw [oddLambdaQ3UnitDifferenceCharacterPrefix_eq_full_sub_even]
  exact (norm_sub_le _ _).trans <|
    add_le_add (hD.2 B) (evenLambdaQ3CharacterPrefix_norm_le_log M B hM)

/-- V1.8.756 composed with the exact full-to-odd correction.  The only
unresolved analytic premise is now a full fixed-modulus character-prefix
ceiling together with the separate signed-reserve dominance inequality. -/
theorem projectReserve_add_negativeAggregate_re_pos_of_fullCharacterPrefixCeiling
    (M : Nat) (hM : 0 < M)
    (q : PairedOddBase (oddProjectRadius M))
    (n : Nat)
    (hTarget : 2 * n ∈ evenTargetBlock M)
    (hq : q.val.val = 3)
    (D : Real)
    (hD : ActualFullLambdaQ3CharacterPrefixCeiling M D)
    (hAbsorb : actualQ3UnitDifferenceScaleEnvelope M q
        (D + Real.log (M : Real)) <
      actualQ3PrefixLocalDensityProjectReserve M q n) :
    0 < (M : Real) / 14 +
      (selectedPairNegativeCenteredUnitAggregate M q n).re := by
  exact projectReserve_add_negativeAggregate_re_pos_of_characterPrefixCeiling
    M hM q n hTarget hq (D + Real.log (M : Real))
      (fullCharacterPrefixCeiling_implies_oddCharacterPrefixCeiling M hM D hD)
      hAbsorb

end GoldbachCircleMethodActualQ3FullCharacterEvenCorrectionV18758
