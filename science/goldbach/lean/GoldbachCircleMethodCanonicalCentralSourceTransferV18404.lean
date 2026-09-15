import GoldbachCircleMethodCanonicalCentralAdjustedPositiveV18403

/-!
# Goldbach V1.8.404: canonical central source transfer

The strict `B^2/224` adjusted reserve from V1.8.403 is inserted into the exact
von-Mangoldt source decomposition on the same central sweep.  The active
residual and adjusted centered-error aggregates remain explicit and are not
estimated here.

The terminal witness is still von-Mangoldt block support.  Prime-power
separation is required before a pure-prime conclusion.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodCanonicalCentralSourceTransferV18404

open GoldbachCircleMethodActiveResidualExactDecompositionV18251
open GoldbachCircleMethodActualResidualExactDecompositionV18225
open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodCanonicalCentralAdjustedPositiveV18403
open GoldbachCircleMethodLogCutoffPresieveBindingV18120
open GoldbachCircleMethodStructurallyAdmissibleActiveSlotV18258

noncomputable def centralBlockSourceTargetSum (m : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (2 * m + 1),
    (canonicalBlockSourceAt (8 * m) ((centralTargetNat m i : ℕ) : ℤ)).re

noncomputable def centralActiveResidualTargetSum
    (m : ℕ) (rho : ℝ)
    (hR2 : 2 ≤ ((8 * m : ℕ) : ℝ) ^ rho) (b : ℝ)
    (e : StructurallyAdmissibleActiveSlot
      ⌊(((8 * m : ℕ) : ℝ) ^ rho) ^ 2⌋₊) : ℝ :=
  ∑ i ∈ Finset.range (2 * m + 1),
    (canonicalActiveResidualAt (8 * m) rho hR2 b e.val
      ((centralTargetNat m i : ℕ) : ℤ)).re

noncomputable def centralAdjustedCenteredErrorTargetSum
    (m : ℕ) (rho b : ℝ)
    (e : StructurallyAdmissibleActiveSlot
      ⌊(((8 * m : ℕ) : ℝ) ^ rho) ^ 2⌋₊) : ℝ :=
  ∑ i ∈ Finset.range (2 * m + 1),
    (canonicalAdjustedCenteredErrorCorrectionAt
      (8 * m) rho b e.val ((centralTargetNat m i : ℕ) : ℤ)).re

/-- Exact central target-summed source identity. -/
theorem central_block_source_target_sum_eq_adjusted_add_errors
    (m : ℕ) (rho : ℝ)
    (hR2 : 2 ≤ ((8 * m : ℕ) : ℝ) ^ rho) (b : ℝ)
    (e : StructurallyAdmissibleActiveSlot
      ⌊(((8 * m : ℕ) : ℝ) ^ rho) ^ 2⌋₊) :
    centralBlockSourceTargetSum m =
      centralAdjustedSourceTargetSum m rho b e +
        centralActiveResidualTargetSum m rho hR2 b e +
        centralAdjustedCenteredErrorTargetSum m rho b e := by
  unfold centralBlockSourceTargetSum centralAdjustedSourceTargetSum
    centralActiveResidualTargetSum centralAdjustedCenteredErrorTargetSum
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _hi
  have hsource := canonicalBlockSourceAt_eq_adjustedModel_add_activeResidual_add_adjustedError
    (8 * m) rho hR2 b e.val ((centralTargetNat m i : ℕ) : ℤ)
  exact congrArg Complex.re hsource

/-- Exact source positivity after both remaining aggregate errors fit below
the explicit central reserve. -/
theorem admitted_central_block_source_target_sum_pos_of_error_absorption
    {K : ℕ} [NeZero K]
    (m : ℕ) (hm : 1 ≤ m) (rho b : ℝ)
    (hR2 : 2 ≤ ((8 * m : ℕ) : ℝ) ^ rho)
    (e : StructurallyAdmissibleActiveSlot
      ⌊(((8 * m : ℕ) : ℝ) ^ rho) ^ 2⌋₊)
    (hK : ∀ q : PositiveLevel ⌊(((8 * m : ℕ) : ℝ) ^ rho) ^ 2⌋₊,
      q.val ∣ K)
    (hrho : 0 < rho) (hrhoUpper : rho ≤ (1 : ℝ) / 10000)
    (hScale : GoldbachCircleMethodResidualScaleAdmissionV18196.blockThreshold rho ≤ 8 * m)
    (hb : 0 ≤ b) (hb1 : b ≤ 1)
    (hR : 1 < ((8 * m : ℕ) : ℝ) ^ rho)
    (herrors :
      |centralActiveResidualTargetSum m rho hR2 b e +
        centralAdjustedCenteredErrorTargetSum m rho b e| <
          ((8 * m : ℕ) : ℝ) ^ 2 / 224) :
    0 < centralBlockSourceTargetSum m := by
  have hadjusted :=
    admitted_central_adjusted_source_target_sum_gt_one_over_224
      m hm rho b e hK hrho hrhoUpper hScale hb hb1 hR
  have herrorLower := (abs_lt.mp herrors).1
  rw [central_block_source_target_sum_eq_adjusted_add_errors
    m rho hR2 b e]
  nlinarith

/-- Positive central source aggregate supplies one explicit target. -/
theorem exists_positive_central_block_source_target
    (m : ℕ) (hpos : 0 < centralBlockSourceTargetSum m) :
    ∃ i ∈ Finset.range (2 * m + 1),
      0 < (canonicalBlockSourceAt (8 * m)
        ((centralTargetNat m i : ℕ) : ℤ)).re := by
  unfold centralBlockSourceTargetSum at hpos
  by_contra hnone
  push Not at hnone
  have hnonpos :
      (∑ i ∈ Finset.range (2 * m + 1),
        (canonicalBlockSourceAt (8 * m)
          ((centralTargetNat m i : ℕ) : ℤ)).re) ≤ 0 := by
    exact Finset.sum_nonpos (fun i hi => hnone i hi)
  linarith

end GoldbachCircleMethodCanonicalCentralSourceTransferV18404
