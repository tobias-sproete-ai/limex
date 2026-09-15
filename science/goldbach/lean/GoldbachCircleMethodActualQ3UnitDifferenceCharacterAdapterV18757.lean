import GoldbachCircleMethodActualQ3UnitDifferenceScaleEnvelopeV18756

/-!
# V1.8.757: actual q=3 unit-difference character adapter

The open arithmetic quantity in V1.8.756 is the difference between the
literal odd-von-Mangoldt masses in residue classes one and two modulo three.
This append-only module rewrites that difference exactly as one finite
von-Mangoldt sum against the real nonprincipal residue table modulo three.

No analytic estimate for that character-shaped sum is imported, asserted, or
inhabited.  In particular, the adapter is not a prime number theorem in
arithmetic progressions and does not prove scale absorption, an exceptional-set
bound, or Goldbach.  `proof_status = NO_PROOF`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

open scoped BigOperators Classical ArithmeticFunction.vonMangoldt

namespace GoldbachCircleMethodActualQ3UnitDifferenceCharacterAdapterV18757

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

/-- Real nonprincipal residue table modulo three, embedded in `Complex`:
zero on class zero, one on class one, and minus one on class two. -/
def q3UnitDifferenceCharacterTable (r : ZMod 3) : Complex :=
  if r = 1 then 1 else if r = 2 then -1 else 0

theorem q3UnitDifferenceCharacterTable_zero :
    q3UnitDifferenceCharacterTable (0 : ZMod 3) = 0 := by
  have h01 : (0 : ZMod 3) ≠ 1 := by decide
  have h02 : (0 : ZMod 3) ≠ 2 := by decide
  simp [q3UnitDifferenceCharacterTable, h01, h02]

theorem q3UnitDifferenceCharacterTable_one :
    q3UnitDifferenceCharacterTable (1 : ZMod 3) = 1 := by
  norm_num [q3UnitDifferenceCharacterTable]

theorem q3UnitDifferenceCharacterTable_two :
    q3UnitDifferenceCharacterTable (2 : ZMod 3) = -1 := by
  have h21 : (2 : ZMod 3) ≠ 1 := by decide
  simp [q3UnitDifferenceCharacterTable, h21]

/-- The literal incomplete odd-von-Mangoldt sum carrying that table. -/
noncomputable def oddLambdaQ3UnitDifferenceCharacterPrefix
    (M B : Nat) : Complex :=
  ∑ a ∈ oddCarrier M,
    if a < B then
      (ArithmeticFunction.vonMangoldt a : Complex) *
        q3UnitDifferenceCharacterTable (a : ZMod 3)
    else 0

/-- Exact finite identity between the two residue masses and the single
character-shaped sum.  No distribution estimate occurs in this proof. -/
theorem oddLambdaQ3ResidueMass_one_sub_two_eq_characterPrefix
    (M B : Nat) :
    oddLambdaQ3ResidueMass M B (1 : ZMod 3) -
        oddLambdaQ3ResidueMass M B (2 : ZMod 3) =
      oddLambdaQ3UnitDifferenceCharacterPrefix M B := by
  unfold oddLambdaQ3ResidueMass oddLambdaQ3UnitDifferenceCharacterPrefix
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a _ha
  have h12 : (1 : ZMod 3) ≠ 2 := by decide
  have h21 : (2 : ZMod 3) ≠ 1 := by decide
  by_cases hB : a < B
  · by_cases h1 : (a : ZMod 3) = 1
    · simp [hB, h1, h12, q3UnitDifferenceCharacterTable]
    · by_cases h2 : (a : ZMod 3) = 2
      · simp [hB, h2, h21, q3UnitDifferenceCharacterTable]
      · simp [hB, h1, h2, q3UnitDifferenceCharacterTable]
  · simp [hB]

theorem oddLambdaQ3UnitBalanceL1_eq_characterPrefixNorm
    (M B : Nat) :
    oddLambdaQ3UnitBalanceL1 M B =
      ‖oddLambdaQ3UnitDifferenceCharacterPrefix M B‖ := by
  rw [oddLambdaQ3UnitBalanceL1_eq_unitClassDifference]
  rw [oddLambdaQ3ResidueMass_one_sub_two_eq_characterPrefix]

/-- Literature-facing form of the remaining fixed-modulus contract.  It is a
named proposition, not an assumed or constructed inhabitant. -/
def ActualOddLambdaQ3CharacterPrefixCeiling
    (M : Nat) (D : Real) : Prop :=
  0 ≤ D ∧ ∀ B : Nat,
    ‖oddLambdaQ3UnitDifferenceCharacterPrefix M B‖ ≤ D

theorem characterPrefixCeiling_iff_unitClassDifferenceCeiling
    (M : Nat) (D : Real) :
    ActualOddLambdaQ3CharacterPrefixCeiling M D ↔
      ActualOddLambdaQ3UnitClassDifferenceCeiling M D := by
  constructor
  · intro hD
    refine ⟨hD.1, ?_⟩
    intro B
    rw [oddLambdaQ3ResidueMass_one_sub_two_eq_characterPrefix]
    exact hD.2 B
  · intro hD
    refine ⟨hD.1, ?_⟩
    intro B
    rw [← oddLambdaQ3ResidueMass_one_sub_two_eq_characterPrefix]
    exact hD.2 B

/-- The V1.8.756 envelope theorem with the remaining discrepancy expressed as
one literal fixed-modulus character-shaped von-Mangoldt prefix contract. -/
theorem projectReserve_add_negativeAggregate_re_pos_of_characterPrefixCeiling
    (M : Nat) (hM : 0 < M)
    (q : PairedOddBase (oddProjectRadius M))
    (n : Nat)
    (hTarget : 2 * n ∈ evenTargetBlock M)
    (hq : q.val.val = 3)
    (D : Real)
    (hD : ActualOddLambdaQ3CharacterPrefixCeiling M D)
    (hAbsorb : actualQ3UnitDifferenceScaleEnvelope M q D <
      actualQ3PrefixLocalDensityProjectReserve M q n) :
    0 < (M : Real) / 14 +
      (selectedPairNegativeCenteredUnitAggregate M q n).re := by
  exact projectReserve_add_negativeAggregate_re_pos_of_scaleEnvelope
    M hM q n hTarget hq D
      ((characterPrefixCeiling_iff_unitClassDifferenceCeiling M D).mp hD)
      hAbsorb

end GoldbachCircleMethodActualQ3UnitDifferenceCharacterAdapterV18757
