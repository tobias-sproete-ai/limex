import GoldbachCircleMethodActualQ3UnitBalanceScalarizationV18779

/-!
# V1.8.780: literal q=3 unit-character source binding

The scalar residue-class discrepancy from V1.8.779 is identified with one
literal finite von-Mangoldt sum against the nontrivial real character modulo
three.  This removes all remaining representation ambiguity from the q=3
arithmetic input.

No cancellation estimate for this character sum is proved here.  Goldbach
therefore remains undecided.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

open scoped BigOperators Classical ArithmeticFunction.vonMangoldt

namespace GoldbachCircleMethodActualQ3UnitCharacterSourceBindingV18780

open GoldbachCircleMethodTwoScaleEvenBlockDefectReserveV1833
open GoldbachCircleMethodOddOddFourierBesselBridgeV18668
open GoldbachCircleMethodActualOddLambdaQ3ResidueDiscrepancyV18752
open GoldbachCircleMethodActualQ3PrefixLocalDensityExtractionV18753
open GoldbachCircleMethodActualQ3UnitBalanceScalarizationV18779

/-- Real nonprincipal residue sign modulo three. -/
def q3UnitCharacterSign (a : Nat) : Real :=
  if (a : ZMod 3) = 1 then 1
  else if (a : ZMod 3) = 2 then -1
  else 0

/-- Literal finite odd-von-Mangoldt character sum on the unchanged carrier. -/
noncomputable def oddLambdaQ3UnitCharacterSum
    (M B : Nat) : Real :=
  ∑ a ∈ oddCarrier M,
    if a < B then
      ArithmeticFunction.vonMangoldt a * q3UnitCharacterSign a
    else 0

theorem oddLambdaQ3ResidueMass_re_eq_realSum
    (M B : Nat) (r : ZMod 3) :
    (oddLambdaQ3ResidueMass M B r).re =
      ∑ a ∈ oddCarrier M,
        if a < B ∧ (a : ZMod 3) = r then
          ArithmeticFunction.vonMangoldt a
        else 0 := by
  change Complex.reCLM (oddLambdaQ3ResidueMass M B r) = _
  unfold oddLambdaQ3ResidueMass
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro a _ha
  by_cases h : a < B ∧ (a : ZMod 3) = r
  · simp [h]
  · simp [h]

/-- Exact identification with the nonprincipal real character modulo three. -/
theorem oddLambdaQ3UnitResidueDifferenceReal_eq_unitCharacterSum
    (M B : Nat) :
    oddLambdaQ3UnitResidueDifferenceReal M B =
      oddLambdaQ3UnitCharacterSum M B := by
  unfold oddLambdaQ3UnitResidueDifferenceReal
    oddLambdaQ3UnitResidueDifference
  rw [Complex.sub_re,
    oddLambdaQ3ResidueMass_re_eq_realSum,
    oddLambdaQ3ResidueMass_re_eq_realSum]
  unfold oddLambdaQ3UnitCharacterSum
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a _ha
  have h12 : (1 : ZMod 3) ≠ 2 := by decide
  have h21 : (2 : ZMod 3) ≠ 1 := by decide
  by_cases hB : a < B
  · by_cases h1 : (a : ZMod 3) = 1
    · have h2 : (a : ZMod 3) ≠ 2 := by
        intro h
        rw [h1] at h
        exact (by decide : (1 : ZMod 3) ≠ 2) h
      simp [hB, h1, h12, q3UnitCharacterSign]
    · by_cases h2 : (a : ZMod 3) = 2
      · simp [hB, h2, h21, q3UnitCharacterSign]
      · simp [hB, h1, h2, q3UnitCharacterSign]
  · simp [hB]

/-- Final exact source form of the post-local-density L1 budget. -/
theorem oddLambdaQ3UnitBalanceL1_eq_abs_unitCharacterSum
    (M B : Nat) :
    oddLambdaQ3UnitBalanceL1 M B =
      |oddLambdaQ3UnitCharacterSum M B| := by
  rw [oddLambdaQ3UnitBalanceL1_eq_abs_unitResidueDifferenceReal,
    oddLambdaQ3UnitResidueDifferenceReal_eq_unitCharacterSum]

end GoldbachCircleMethodActualQ3UnitCharacterSourceBindingV18780
