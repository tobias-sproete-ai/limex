import GoldbachCircleMethodLocalizedReducedPairExactFactorizationV18308
import GoldbachCircleMethodVariableWeightIntervalDiscrepancyV18272
import GoldbachCircleMethodSupportedModelIntervalDiagonalV18228

/-!
# Goldbach V1.8.309: localized shape interval adapter

This module identifies the reduced-pair shape carrier from V1.8.308 with the
literal unit-pair interval already audited in V1.8.272.  The bridge is exact:
no averaging, endpoint change, periodic replacement, or sign estimate occurs.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodLocalizedShapeIntervalAdapterV18309

open GoldbachCircleMethodActualUnitPairArithmeticV18194
open GoldbachCircleMethodActiveExceptionalCenteringV18129
open GoldbachCircleMethodBlockPairCarrierV18227
open GoldbachCircleMethodLogCutoffPresieveBindingV18120
open GoldbachCircleMethodLocalizedReducedPairExactFactorizationV18308
open GoldbachCircleMethodSupportedModelIntervalDiagonalV18228
open GoldbachCircleMethodVariableWeightIntervalDiscrepancyV18272

/-- Natural coprimality is exactly membership in the literal unit-pair
residue carrier once the complementary natural subtraction is known to be
genuine. -/
theorem natCast_mem_unitPairResidues_iff
    (r N n : ℕ) [NeZero r] (hn : n ≤ N) :
    ((n : ZMod r) ∈ unitPairResidues r (N : ℤ)) ↔
      Nat.Coprime n r ∧ Nat.Coprime (N - n) r := by
  rw [mem_unitPairResidues]
  simp only [Int.cast_natCast]
  rw [← Nat.cast_sub hn]
  simp only [ZMod.isUnit_iff_coprime]

/-- The reduced-pair shape on one closed natural interval. -/
noncomputable def localizedReducedPairShapeIcc {Q : ℕ}
    (e : CharacterSlot Q) (N A U : ℕ) (b : ℝ) : ℂ :=
  ∑ n ∈ (Finset.Icc A U).filter
      (fun n => Nat.Coprime n e.1.val ∧ Nat.Coprime (N - n) e.1.val),
    localizedReducedPairShape e N n b

/-- Exact reindexing of the closed reduced-pair interval into the existing
half-open literal unit-pair interval. -/
theorem localizedReducedPairShapeIcc_eq_variableUnitPairInterval
    {Q : ℕ} (e : CharacterSlot Q) (N A U : ℕ)
    (hAU : A ≤ U) (hUN : U ≤ N) (b : ℝ) :
    localizedReducedPairShapeIcc e N A U b =
      variableUnitPairInterval e.1.val N A (U - A + 1) e.2.val b := by
  unfold localizedReducedPairShapeIcc variableUnitPairInterval
  rw [Finset.sum_filter]
  rw [sum_Icc_eq_sum_range_shift A U hAU]
  apply Finset.sum_congr rfl
  intro i hi
  have hiT : i < U - A + 1 := Finset.mem_range.mp hi
  have hni : A + i ≤ N := by omega
  have hmem := natCast_mem_unitPairResidues_iff e.1.val N (A + i) hni
  by_cases hpair : Nat.Coprime (A + i) e.1.val ∧
      Nat.Coprime (N - (A + i)) e.1.val
  · rw [if_pos hpair, if_pos (hmem.mpr hpair)]
    unfold localizedReducedPairShape
    rw [Nat.cast_sub hni]
  · rw [if_neg hpair, if_neg]
    exact fun h => hpair (hmem.mp h)

/-- On the canonical block, the V1.8.308 reduced-pair shape is literally the
V1.8.272 variable unit-pair interval with the endpoint-exact length. -/
theorem localizedReducedPairShapeSum_block_eq_variableUnitPairInterval
    {Q : ℕ} (B N : ℕ) (e : CharacterSlot Q) (b : ℝ)
    (hB : 1 ≤ B) (hBN : B ≤ N)
    (hInterval : blockPairLower B N ≤ blockPairUpper B N) :
    localizedReducedPairShapeSum (blockCarrier B) e N b =
      variableUnitPairInterval e.1.val N (blockPairLower B N)
        (blockPairUpper B N - blockPairLower B N + 1) e.2.val b := by
  unfold localizedReducedPairShapeSum
  rw [pairFirstCarrier_block_eq_Icc B N hB hBN]
  change localizedReducedPairShapeIcc e N (blockPairLower B N)
      (blockPairUpper B N) b = _
  apply localizedReducedPairShapeIcc_eq_variableUnitPairInterval
    e N (blockPairLower B N) (blockPairUpper B N) hInterval
  unfold blockPairUpper
  omega

end GoldbachCircleMethodLocalizedShapeIntervalAdapterV18309
