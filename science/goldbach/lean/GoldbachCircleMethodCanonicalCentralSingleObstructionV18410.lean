import GoldbachCircleMethodCanonicalCentralActiveEventualV18409

/-!
# Goldbach V1.8.410: central single-obstruction interface

After the admitted Vaughan estimate, V1.8.409 removes the active-residual
aggregate for all sufficiently large central blocks.  This module combines
that result with V1.8.407 and exposes exactly one remaining quantitative
source-side obstruction: the adjusted centered-error aggregate.

The divisibility witness `K` is quantified after the block scale, so no fixed
finite integer is incorrectly required to absorb an unbounded conductor
family.  The conclusion is still a von-Mangoldt source witness, not a
pure-prime witness and not pointwise Goldbach.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodCanonicalCentralSingleObstructionV18410

open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodCanonicalCentralActiveEventualV18409
open GoldbachCircleMethodCanonicalCentralSourceRecombinationV18407
open GoldbachCircleMethodCanonicalCentralSourceTransferV18404
open GoldbachCircleMethodLogCutoffPresieveBindingV18120
open GoldbachCircleMethodRealApproximationMinorAdapterV1873
open GoldbachCircleMethodResidualScaleAdmissionV18196
open GoldbachCircleMethodStructurallyAdmissibleActiveSlotV18258

/-- Conditional on the named Vaughan estimate, the adjusted centered-error
aggregate is the only remaining quantitative source-side input in this
central-sweep theorem. -/
theorem eventual_central_source_positive_of_centered_error_bound
    (C rho : ℝ) (hC : 0 ≤ C) (hV : RealVaughanEstimate C)
    (hrho : 0 < rho) (hrhoUpper : rho ≤ (1 : ℝ) / 10000) :
    ∃ m₀ : ℕ, ∀ (m : ℕ), m₀ ≤ m →
      ∀ {K : ℕ} [NeZero K],
      ∀ b : ℝ, 0 ≤ b → b ≤ 1 →
      ∀ e : StructurallyAdmissibleActiveSlot
        ⌊(((8 * m : ℕ) : ℝ) ^ rho) ^ 2⌋₊,
      (∀ q : PositiveLevel ⌊(((8 * m : ℕ) : ℝ) ^ rho) ^ 2⌋₊,
        q.val ∣ K) →
      |centralAdjustedCenteredErrorTargetSum m rho b e| <
          ((8 * m : ℕ) : ℝ) ^ 2 / 2048 →
      0 < centralBlockSourceTargetSum m ∧
        ∃ i ∈ Finset.range (2 * m + 1),
          0 < (GoldbachCircleMethodActualResidualExactDecompositionV18225.canonicalBlockSourceAt
            (8 * m) ((GoldbachCircleMethodCanonicalCentralAdjustedPositiveV18403.centralTargetNat
              m i : ℕ) : ℤ)).re := by
  obtain ⟨Crho, _hCrho, m₁, hactive⟩ :=
    eventual_central_active_residual_target_sum_abs_lt_one_over_256
      C rho hC hV hrho hrhoUpper
  let m₀ := max (max m₁ (blockThreshold rho)) 1
  refine ⟨m₀, ?_⟩
  intro m hm K hKinst b hb hb1 e hK hCentered
  have hinner : max m₁ (blockThreshold rho) ≤ m₀ := le_max_left _ _
  have hm₁ : m₁ ≤ m :=
    (le_max_left m₁ (blockThreshold rho)).trans (hinner.trans hm)
  have hthreshold_m : blockThreshold rho ≤ m :=
    (le_max_right m₁ (blockThreshold rho)).trans (hinner.trans hm)
  have hm1 : 1 ≤ m := (le_max_right (max m₁ (blockThreshold rho)) 1).trans hm
  have hthreshold_B : blockThreshold rho ≤ 8 * m := by omega
  obtain ⟨_hB6, hR2, _hlower, _hupper⟩ :=
    actual_scale_admission rho hrho hrhoUpper (8 * m) hthreshold_B
  have hR : 1 < ((8 * m : ℕ) : ℝ) ^ rho :=
    one_lt_power_of_admitted rho hrho hrhoUpper (8 * m) hthreshold_B
  have hResidual := hactive m hm₁ hR2 b hb hb1 e
  have hpos :=
    admitted_central_block_source_target_sum_pos_of_separate_budgets
      m hm1 rho b hR2 e hK hrho hrhoUpper hthreshold_B hb hb1 hR
      hResidual hCentered
  exact ⟨hpos,
    exists_positive_central_block_source_target_of_separate_budgets
      m hm1 rho b hR2 e hK hrho hrhoUpper hthreshold_B hb hb1 hR
      hResidual hCentered⟩

end GoldbachCircleMethodCanonicalCentralSingleObstructionV18410
