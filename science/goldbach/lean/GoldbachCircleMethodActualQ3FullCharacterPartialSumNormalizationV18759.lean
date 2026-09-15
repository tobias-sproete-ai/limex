import GoldbachCircleMethodActualQ3FullCharacterEvenCorrectionV18758

/-!
# V1.8.759: one-parameter normalization of the full q=3 character prefix

V1.8.758 uses an ambient endpoint `M` and an independent prefix cutoff `B`.
The actual finite sum only sees indices below `min B (M+1)`.  This module
proves that fact exactly and replaces the two-cutoff contract by a single
partial-sum variable `X ≤ M+1`.

No cancellation estimate for that partial sum is asserted or inhabited.
`proof_status = NO_PROOF`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

open scoped BigOperators Classical ArithmeticFunction.vonMangoldt

namespace GoldbachCircleMethodActualQ3FullCharacterPartialSumNormalizationV18759

open GoldbachCircleMethodTwoScaleEvenBlockDefectReserveV1833
open GoldbachCircleMethodOddChannelEventualAbsorptionV18658
open GoldbachCircleMethodActualQ3UnitDifferenceCharacterAdapterV18757
open GoldbachCircleMethodActualQ3FullCharacterEvenCorrectionV18758
open GoldbachCircleMethodActualQ3UnitDifferenceScaleEnvelopeV18756
open GoldbachCircleMethodActualQ3PrefixLocalDensitySignedReserveV18755
open GoldbachCircleMethodFullDenominatorFourClassPartitionV18688
open GoldbachCircleMethodActualMixedChannelRamanujanFactorizationV18727

/-- Standard one-parameter finite prefix of the full von-Mangoldt sequence
against the fixed q=3 nonprincipal residue table. -/
noncomputable def fullLambdaQ3CharacterPartialSum (X : Nat) : Complex :=
  ∑ a ∈ Finset.range X,
    (ArithmeticFunction.vonMangoldt a : Complex) *
      q3UnitDifferenceCharacterTable (a : ZMod 3)

/-- Exact removal of the redundant ambient/cutoff pair: only the clamped
prefix length `min B (M+1)` contributes. -/
theorem fullLambdaQ3CharacterPrefix_eq_partialSum_min
    (M B : Nat) :
    fullLambdaQ3CharacterPrefix M B =
      fullLambdaQ3CharacterPartialSum (min B M.succ) := by
  unfold fullLambdaQ3CharacterPrefix fullLambdaQ3CharacterPartialSum
  rw [← Finset.sum_filter]
  congr 1
  ext a
  simp only [Finset.mem_filter, Finset.mem_range, Nat.lt_min]
  tauto

/-- Single-scale version of the still-open full q=3 cancellation contract. -/
def ActualFullLambdaQ3CharacterPartialSumCeiling
    (M : Nat) (D : Real) : Prop :=
  0 ≤ D ∧ ∀ X : Nat, X ≤ M.succ →
    ‖fullLambdaQ3CharacterPartialSum X‖ ≤ D

/-- The single-scale contract is exactly equivalent to the earlier
two-cutoff presentation, not a strengthening or weakening. -/
theorem fullCharacterPrefixCeiling_iff_partialSumCeiling
    (M : Nat) (D : Real) :
    ActualFullLambdaQ3CharacterPrefixCeiling M D ↔
      ActualFullLambdaQ3CharacterPartialSumCeiling M D := by
  constructor
  · intro hD
    refine ⟨hD.1, ?_⟩
    intro X hX
    have hmin : min X M.succ = X := Nat.min_eq_left hX
    have h := hD.2 X
    rw [fullLambdaQ3CharacterPrefix_eq_partialSum_min, hmin] at h
    exact h
  · intro hD
    refine ⟨hD.1, ?_⟩
    intro B
    rw [fullLambdaQ3CharacterPrefix_eq_partialSum_min]
    exact hD.2 (min B M.succ) (Nat.min_le_right B M.succ)

/-- Exact transfer from the normalized full partial-sum ceiling to the
actual odd-prefix ceiling, retaining only the explicit even correction. -/
theorem partialSumCeiling_implies_oddCharacterPrefixCeiling
    (M : Nat) (hM : 0 < M) (D : Real)
    (hD : ActualFullLambdaQ3CharacterPartialSumCeiling M D) :
    ActualOddLambdaQ3CharacterPrefixCeiling M
      (D + Real.log (M : Real)) := by
  exact fullCharacterPrefixCeiling_implies_oddCharacterPrefixCeiling
    M hM D ((fullCharacterPrefixCeiling_iff_partialSumCeiling M D).2 hD)

/-- V1.8.756 with the actual q=3 analytic obligation exposed as one bounded
family of full fixed-modulus partial sums.  Positivity remains conditional on
this ceiling and on its strict absorption by the signed project reserve. -/
theorem projectReserve_add_negativeAggregate_re_pos_of_partialSumCeiling
    (M : Nat) (hM : 0 < M)
    (q : PairedOddBase (oddProjectRadius M))
    (n : Nat)
    (hTarget : 2 * n ∈ evenTargetBlock M)
    (hq : q.val.val = 3)
    (D : Real)
    (hD : ActualFullLambdaQ3CharacterPartialSumCeiling M D)
    (hAbsorb : actualQ3UnitDifferenceScaleEnvelope M q
        (D + Real.log (M : Real)) <
      actualQ3PrefixLocalDensityProjectReserve M q n) :
    0 < (M : Real) / 14 +
      (selectedPairNegativeCenteredUnitAggregate M q n).re := by
  exact projectReserve_add_negativeAggregate_re_pos_of_fullCharacterPrefixCeiling
    M hM q n hTarget hq D
      ((fullCharacterPrefixCeiling_iff_partialSumCeiling M D).2 hD)
      hAbsorb

end GoldbachCircleMethodActualQ3FullCharacterPartialSumNormalizationV18759
