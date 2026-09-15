import GoldbachCircleMethodCentralPrimePowerDefectAbsorptionV18444
import GoldbachCircleMethodNonGoldbachBlockSourceDefectBridgeV18237

/-!
# Goldbach V1.8.445: central pure-prime witness transfer

If the literal central von-Mangoldt source aggregate exceeds the sum of all
prime-power defects on the same targets, at least one target is Goldbach.
V1.8.443 and V1.8.444 provide exactly the two strict sides of that comparison
for sufficiently large central blocks once the named analytic error budgets
are supplied.

This closes the semantic transfer from the von-Mangoldt aggregate to one true
prime-pair witness in the central sweep.  It does not supply the analytic
residual or centered-error bounds and does not prove pointwise Goldbach.
`proof_status = NO_PROOF` remains mandatory.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodCentralPurePrimeWitnessTransferV18445

open GoldbachPurePrimeAdequacyV15
open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodCanonicalCentralAdjustedPositiveV18403
open GoldbachCircleMethodCanonicalCentralSourceTransferV18404
open GoldbachCircleMethodCentralPrimePowerDefectAbsorptionV18444
open GoldbachCircleMethodCentralQuantitativeSourceReserveV18443
open GoldbachCircleMethodLogCutoffPresieveBindingV18120
open GoldbachCircleMethodNonGoldbachBlockSourceDefectBridgeV18237
open GoldbachCircleMethodStructurallyAdmissibleActiveSlotV18258

/-- Aggregate source mass beyond the complete prime-power defect mass forces
one genuine Goldbach target in the central sweep. -/
theorem exists_goldbach_central_target_of_source_gt_defect_sum
    (m : ℕ)
    (hsource : centralPrimePowerDefectSum m < centralBlockSourceTargetSum m) :
    ∃ i ∈ Finset.range (2 * m + 1), GoldbachAt (centralTargetNat m i) := by
  by_contra hnone
  push Not at hnone
  have hpoint (i : ℕ) (hi : i ∈ Finset.range (2 * m + 1)) :
      (GoldbachCircleMethodActualResidualExactDecompositionV18225.canonicalBlockSourceAt
        (8 * m) ((centralTargetNat m i : ℕ) : ℤ)).re ≤
          GoldbachVonMangoldtDecompositionV16.primePowerDefect
            (centralTargetNat m i) := by
    apply canonicalBlockSourceAt_re_le_primePowerDefect_of_not_goldbachAt
    · simp only [centralTargetNat]
      omega
    · exact hnone i hi
  have hsum : centralBlockSourceTargetSum m ≤ centralPrimePowerDefectSum m := by
    unfold centralBlockSourceTargetSum centralPrimePowerDefectSum
    exact Finset.sum_le_sum hpoint
  linarith

/-- Once the quantitative central source reserve is available, the already
closed prime-power absorption yields one pure-prime witness eventually. -/
theorem eventual_exists_goldbach_central_target_of_separate_budgets :
    ∃ m₀ : ℕ, ∀ {K : ℕ} [NeZero K],
      ∀ (m : ℕ), m₀ ≤ m →
      ∀ (rho b : ℝ),
      ∀ (hR2 : 2 ≤ ((8 * m : ℕ) : ℝ) ^ rho),
      ∀ (e : StructurallyAdmissibleActiveSlot
        ⌊(((8 * m : ℕ) : ℝ) ^ rho) ^ 2⌋₊),
      (∀ q : PositiveLevel ⌊(((8 * m : ℕ) : ℝ) ^ rho) ^ 2⌋₊,
        q.val ∣ K) →
      0 < rho → rho ≤ (1 : ℝ) / 10000 →
      GoldbachCircleMethodResidualScaleAdmissionV18196.blockThreshold rho ≤ 8 * m →
      0 ≤ b → b ≤ 1 →
      1 < ((8 * m : ℕ) : ℝ) ^ rho →
      |centralActiveResidualTargetSum m rho hR2 b e| <
        ((8 * m : ℕ) : ℝ) ^ 2 / 256 →
      |centralAdjustedCenteredErrorTargetSum m rho b e| <
        ((8 * m : ℕ) : ℝ) ^ 2 / 2048 →
      ∃ i ∈ Finset.range (2 * m + 1), GoldbachAt (centralTargetNat m i) := by
  obtain ⟨m₀, hdefect⟩ := eventual_centralPrimePowerDefectSum_lt_reserve
  refine ⟨max m₀ 1, ?_⟩
  intro K hKinst m hm rho b hR2 e hK hrho hrhoUpper hScale hb hb1 hR
    hResidual hCentered
  have hm₀ : m₀ ≤ m := (le_max_left m₀ 1).trans hm
  have hmOne : 1 ≤ m := (le_max_right m₀ 1).trans hm
  have hdefect' := hdefect m hm₀
  have hreserve :=
    central_block_source_target_sum_gt_one_over_14336_of_separate_budgets
      m hmOne rho b hR2 e hK hrho hrhoUpper hScale hb hb1 hR
      hResidual hCentered
  exact exists_goldbach_central_target_of_source_gt_defect_sum m
    (hdefect'.trans hreserve)

end GoldbachCircleMethodCentralPurePrimeWitnessTransferV18445
