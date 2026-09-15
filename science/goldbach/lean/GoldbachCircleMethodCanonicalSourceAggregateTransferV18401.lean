import GoldbachCircleMethodCanonicalActualSourcePositiveV18400

/-!
# Goldbach V1.8.401: canonical source-aggregate transfer

The positive adjusted-source aggregate of V1.8.400 is placed inside the exact
active-branch source accounting identity.  This module does not estimate the
remaining active residual or adjusted centered-error terms.  It exposes their
precise joint absorption threshold and proves the finite witness extraction
that follows if that threshold is met.

The witness is positivity of the von-Mangoldt block convolution at one target.
Prime-power separation is still required before any pure-prime conclusion.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodCanonicalSourceAggregateTransferV18401

open GoldbachCircleMethodActiveResidualExactDecompositionV18251
open GoldbachCircleMethodActualResidualExactDecompositionV18225
open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodCanonicalActualSourcePositiveV18400
open GoldbachCircleMethodLogCutoffPresieveBindingV18120
open GoldbachCircleMethodPrincipalWindowBoundaryV18121
open GoldbachCircleMethodStructurallyAdmissibleActiveSlotV18258

/-- Actual von-Mangoldt block-convolution aggregate on the canonical even
target sweep. -/
noncomputable def canonicalBlockSourceTargetSum (m : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (2 * m),
    (canonicalBlockSourceAt (4 * m)
      ((4 * m + 2 + 2 * i : ℕ) : ℤ)).re

/-- Aggregate active residual from the exact source decomposition. -/
noncomputable def canonicalActiveResidualTargetSum
    (m : ℕ) (rho : ℝ)
    (hR2 : 2 ≤ ((4 * m : ℕ) : ℝ) ^ rho) (b : ℝ)
    (e : StructurallyAdmissibleActiveSlot
      ⌊(((4 * m : ℕ) : ℝ) ^ rho) ^ 2⌋₊) : ℝ :=
  ∑ i ∈ Finset.range (2 * m),
    (canonicalActiveResidualAt (4 * m) rho hR2 b e.val
      ((4 * m + 2 + 2 * i : ℕ) : ℤ)).re

/-- Aggregate adjusted centered-error correction from the exact source
decomposition. -/
noncomputable def canonicalAdjustedCenteredErrorTargetSum
    (m : ℕ) (rho b : ℝ)
    (e : StructurallyAdmissibleActiveSlot
      ⌊(((4 * m : ℕ) : ℝ) ^ rho) ^ 2⌋₊) : ℝ :=
  ∑ i ∈ Finset.range (2 * m),
    (canonicalAdjustedCenteredErrorCorrectionAt
      (4 * m) rho b e.val ((4 * m + 2 + 2 * i : ℕ) : ℤ)).re

/-- Exact target-summed source identity.  No estimate enters this theorem. -/
theorem canonical_block_source_target_sum_eq_adjusted_add_errors
    (m : ℕ) (rho : ℝ)
    (hR2 : 2 ≤ ((4 * m : ℕ) : ℝ) ^ rho) (b : ℝ)
    (e : StructurallyAdmissibleActiveSlot
      ⌊(((4 * m : ℕ) : ℝ) ^ rho) ^ 2⌋₊) :
    canonicalBlockSourceTargetSum m =
      canonicalAdjustedSourceTargetSum m rho b e +
        canonicalActiveResidualTargetSum m rho hR2 b e +
        canonicalAdjustedCenteredErrorTargetSum m rho b e := by
  unfold canonicalBlockSourceTargetSum canonicalAdjustedSourceTargetSum
    canonicalActiveResidualTargetSum canonicalAdjustedCenteredErrorTargetSum
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _hi
  have hsource := canonicalBlockSourceAt_eq_adjustedModel_add_activeResidual_add_adjustedError
    (4 * m) rho hR2 b e.val ((4 * m + 2 + 2 * i : ℕ) : ℤ)
  exact congrArg Complex.re hsource

/-- The V1.8.400 estimates retain the explicit reserve `5*B^2/336` after
both pairwise-period costs have been paid. -/
theorem admitted_canonical_adjusted_source_target_sum_gt_five_over_336
    {K : ℕ} [NeZero K]
    (m : ℕ) (hm : 1 ≤ m) (rho b : ℝ)
    (e : StructurallyAdmissibleActiveSlot
      ⌊(((4 * m : ℕ) : ℝ) ^ rho) ^ 2⌋₊)
    (hK : ∀ q : PositiveLevel ⌊(((4 * m : ℕ) : ℝ) ^ rho) ^ 2⌋₊,
      q.val ∣ K)
    (hrho : 0 < rho) (hrhoUpper : rho ≤ (1 : ℝ) / 10000)
    (hScale : GoldbachCircleMethodResidualScaleAdmissionV18196.blockThreshold rho ≤ 4 * m)
    (hb : 0 ≤ b) (hb1 : b ≤ 1)
    (hR : 1 < ((4 * m : ℕ) : ℝ) ^ rho) :
    5 * ((4 * m : ℕ) : ℝ) ^ 2 / 336 <
      canonicalAdjustedSourceTargetSum m rho b e := by
  let mean : ℝ :=
    GoldbachCircleMethodCanonicalSourceMeanPositiveV18399.canonicalSourceVariableMeanTargetSum
      (log_cutoff_contains_one (((4 * m : ℕ) : ℝ) ^ rho) hR)
      hK e
      (logWeight (((4 * m : ℕ) : ℝ) ^ rho)
        GoldbachCircleMethodCanonicalBumpPrincipalFloorV18220.canonicalLogBump)
      (logWeight (((4 * m : ℕ) : ℝ) ^ rho)
        GoldbachCircleMethodCanonicalBumpPrincipalFloorV18220.canonicalLogBump)
      m b
  have hmean := admitted_canonical_source_variable_mean_gt_one_forty_second
    m hm rho b e hK hrho hrhoUpper hScale hb hb1 hR
  have hboundary :=
    canonical_adjusted_source_target_sum_sub_mean_abs_le_boundary
      m hm rho b e hK hrho hrhoUpper hScale hb hb1 hR
  have hlower : -(((4 * m : ℕ) : ℝ) ^ 2 / 112) ≤
      canonicalAdjustedSourceTargetSum m rho b e - mean :=
    (abs_le.mp (by simpa only [mean] using hboundary)).1
  have hmean' : ((4 * m : ℕ) : ℝ) ^ 2 / 42 < mean := by
    simpa only [mean] using hmean
  have hBpos : 0 < ((4 * m : ℕ) : ℝ) := by positivity
  nlinarith [sq_pos_of_pos hBpos]

/-- If the two source-side error aggregates fit below the remaining explicit
reserve, the actual von-Mangoldt block aggregate is positive. -/
theorem admitted_canonical_block_source_target_sum_pos_of_error_absorption
    {K : ℕ} [NeZero K]
    (m : ℕ) (hm : 1 ≤ m) (rho b : ℝ)
    (hR2 : 2 ≤ ((4 * m : ℕ) : ℝ) ^ rho)
    (e : StructurallyAdmissibleActiveSlot
      ⌊(((4 * m : ℕ) : ℝ) ^ rho) ^ 2⌋₊)
    (hK : ∀ q : PositiveLevel ⌊(((4 * m : ℕ) : ℝ) ^ rho) ^ 2⌋₊,
      q.val ∣ K)
    (hrho : 0 < rho) (hrhoUpper : rho ≤ (1 : ℝ) / 10000)
    (hScale : GoldbachCircleMethodResidualScaleAdmissionV18196.blockThreshold rho ≤ 4 * m)
    (hb : 0 ≤ b) (hb1 : b ≤ 1)
    (hR : 1 < ((4 * m : ℕ) : ℝ) ^ rho)
    (herrors :
      |canonicalActiveResidualTargetSum m rho hR2 b e +
        canonicalAdjustedCenteredErrorTargetSum m rho b e| <
          5 * ((4 * m : ℕ) : ℝ) ^ 2 / 336) :
    0 < canonicalBlockSourceTargetSum m := by
  have hadjusted :=
    admitted_canonical_adjusted_source_target_sum_gt_five_over_336
      m hm rho b e hK hrho hrhoUpper hScale hb hb1 hR
  have herrorLower := (abs_lt.mp herrors).1
  rw [canonical_block_source_target_sum_eq_adjusted_add_errors
    m rho hR2 b e]
  nlinarith

/-- Positive aggregate mass has a concrete target witness.  The conclusion is
still von-Mangoldt support, not yet a pure-prime pair. -/
theorem exists_positive_canonical_block_source_target
    (m : ℕ)
    (hpos : 0 < canonicalBlockSourceTargetSum m) :
    ∃ i ∈ Finset.range (2 * m),
      0 < (canonicalBlockSourceAt (4 * m)
        ((4 * m + 2 + 2 * i : ℕ) : ℤ)).re := by
  unfold canonicalBlockSourceTargetSum at hpos
  by_contra hnone
  push Not at hnone
  have hnonpos :
      (∑ i ∈ Finset.range (2 * m),
        (canonicalBlockSourceAt (4 * m)
          ((4 * m + 2 + 2 * i : ℕ) : ℤ)).re) ≤ 0 := by
    apply Finset.sum_nonpos
    intro i hi
    exact hnone i hi
  linarith

end GoldbachCircleMethodCanonicalSourceAggregateTransferV18401
