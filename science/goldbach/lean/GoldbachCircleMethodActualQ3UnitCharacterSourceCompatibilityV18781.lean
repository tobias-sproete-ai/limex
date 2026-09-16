import GoldbachCircleMethodActualQ3UnitCharacterSourceBindingV18780

/-!
# V1.8.781: q=3 real/complex character-source compatibility

The real residue-sign sum introduced in V1.8.780 is proved to be exactly the
same finite arithmetic object as the complex residue table already bound in
V1.8.757.  Consequently V1.8.780 creates no second analytic premise and no
representation drift.

This is a source-compatibility result only.  It supplies no new cancellation
estimate for the character sum and no sign theorem for the q=3 weighted pair
correlation.  `proof_status = NO_PROOF`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

open scoped BigOperators Classical ArithmeticFunction.vonMangoldt

namespace GoldbachCircleMethodActualQ3UnitCharacterSourceCompatibilityV18781

open GoldbachCircleMethodActualQ3UnitDifferenceCharacterAdapterV18757
open GoldbachCircleMethodActualQ3UnitBalanceScalarizationV18779
open GoldbachCircleMethodActualQ3UnitCharacterSourceBindingV18780
open GoldbachCircleMethodOddOddFourierBesselBridgeV18668

/-- The real sign table and the earlier complex character table agree after
the canonical embedding of reals into complex numbers. -/
theorem q3UnitCharacterSign_cast_eq_characterTable (a : Nat) :
    ((q3UnitCharacterSign a : Real) : Complex) =
      q3UnitDifferenceCharacterTable (a : ZMod 3) := by
  have h21 : (2 : ZMod 3) ≠ 1 := by decide
  by_cases h1 : (a : ZMod 3) = 1
  · simp [q3UnitCharacterSign, q3UnitDifferenceCharacterTable, h1]
  · by_cases h2 : (a : ZMod 3) = 2
    · simp [q3UnitCharacterSign, q3UnitDifferenceCharacterTable, h2, h21]
    · simp [q3UnitCharacterSign, q3UnitDifferenceCharacterTable, h1, h2]

/-- The V1.8.780 real sum is the real coordinate of the V1.8.757 complex
character prefix on the identical finite carrier. -/
theorem oddLambdaQ3UnitDifferenceCharacterPrefix_re_eq_realSum
    (M B : Nat) :
    (oddLambdaQ3UnitDifferenceCharacterPrefix M B).re =
      oddLambdaQ3UnitCharacterSum M B := by
  unfold oddLambdaQ3UnitDifferenceCharacterPrefix
    oddLambdaQ3UnitCharacterSum
  change Complex.reCLM
      (∑ a ∈ oddCarrier M,
        if a < B then
          (ArithmeticFunction.vonMangoldt a : Complex) *
            q3UnitDifferenceCharacterTable (a : ZMod 3)
        else 0) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro a _ha
  have h21 : (2 : ZMod 3) ≠ 1 := by decide
  by_cases hB : a < B
  · rw [if_pos hB, if_pos hB]
    by_cases h1 : (a : ZMod 3) = 1
    · simp [q3UnitDifferenceCharacterTable, q3UnitCharacterSign, h1]
    · by_cases h2 : (a : ZMod 3) = 2
      · simp [q3UnitDifferenceCharacterTable, q3UnitCharacterSign, h2, h21]
      · simp [q3UnitDifferenceCharacterTable, q3UnitCharacterSign, h1, h2]
  · simp [hB]

/-- Norm/absolute-value compatibility for the two exact presentations. -/
theorem oddLambdaQ3UnitDifferenceCharacterPrefix_norm_eq_abs_realSum
    (M B : Nat) :
    ‖oddLambdaQ3UnitDifferenceCharacterPrefix M B‖ =
      |oddLambdaQ3UnitCharacterSum M B| := by
  rw [← oddLambdaQ3UnitBalanceL1_eq_characterPrefixNorm,
    oddLambdaQ3UnitBalanceL1_eq_abs_unitCharacterSum]

/-- The real source ceiling used by V1.8.780. -/
def ActualOddLambdaQ3RealCharacterSumCeiling
    (M : Nat) (D : Real) : Prop :=
  0 ≤ D ∧ ∀ B : Nat, |oddLambdaQ3UnitCharacterSum M B| ≤ D

/-- The real and complex source ceilings are propositionally identical. -/
theorem realCharacterSumCeiling_iff_characterPrefixCeiling
    (M : Nat) (D : Real) :
    ActualOddLambdaQ3RealCharacterSumCeiling M D ↔
      ActualOddLambdaQ3CharacterPrefixCeiling M D := by
  constructor <;> intro hD
  · refine ⟨hD.1, ?_⟩
    intro B
    rw [oddLambdaQ3UnitDifferenceCharacterPrefix_norm_eq_abs_realSum]
    exact hD.2 B
  · refine ⟨hD.1, ?_⟩
    intro B
    rw [← oddLambdaQ3UnitDifferenceCharacterPrefix_norm_eq_abs_realSum]
    exact hD.2 B

end GoldbachCircleMethodActualQ3UnitCharacterSourceCompatibilityV18781
