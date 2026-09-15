import GoldbachCircleMethodCrossConductorPairExpansionV18540

/-!
# Goldbach V1.8.541: cross-conductor block pair reindex

The exact signed residual from V1.8.540 is reindexed from a target-first sum
to a conductor-pair-first block correlation.  This is the literal carrier on
which a pairwise-period or incomplete-period estimate must act.  No
orthogonality, cancellation, or smallness is asserted.
-/

set_option autoImplicit false

open scoped BigOperators Classical ComplexConjugate

namespace GoldbachCircleMethodCrossConductorBlockPairReindexV18541

open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodCrossConductorPairExpansionV18540
open GoldbachCircleMethodExactCrossConductorResidualV18538
open GoldbachCircleMethodLogCutoffPresieveBindingV18120
open GoldbachCircleMethodNonprincipalConductorAlignedCorrelationV18527

/-- Real parts commute with an arbitrary finite sum. -/
theorem re_finset_sum
    {ι : Type} (s : Finset ι) (f : ι → ℂ) :
    (∑ i ∈ s, f i).re = ∑ i ∈ s, (f i).re := by
  let reHom : ℂ →+ ℝ :=
    { toFun := Complex.re
      map_zero' := rfl
      map_add' := fun x y => Complex.add_re x y }
  change reHom (∑ i ∈ s, f i) = ∑ i ∈ s, reHom (f i)
  exact map_sum reHom f s

/-- The literal real cross-correlation of two distinct conductor channels
over the unchanged dyadic target block.  Distinctness is carried by the
outer erased index rather than hidden in this definition. -/
noncomputable def conductorPairBlockCorrelation
    (Q B : ℕ) (H : ℝ) (w : ℕ → ℂ)
    (r s : PositiveLevel Q) : ℝ :=
  ∑ N ∈ blockCarrier B,
    (star (nonprincipalConductorCorrelation Q B N H w r) *
      nonprincipalConductorCorrelation Q B N H w s).re

/-- Exact target/pair Fubini reindexing of the block residual.  The outer
conductor count is not inserted and the signed cross terms remain intact. -/
theorem blockCrossConductorResidual_eq_sum_pair_block_correlations
    (Q B : ℕ) (H : ℝ) (w : ℕ → ℂ) :
    blockCrossConductorResidual Q B H w =
      ∑ r : PositiveLevel Q,
        ∑ s ∈ (Finset.univ.erase r),
          conductorPairBlockCorrelation Q B H w r s := by
  rw [blockCrossConductorResidual_eq_ordered_pair_sum]
  unfold orderedCrossConductorCorrelation orderedCrossTermSum
    conductorPairBlockCorrelation
  simp_rw [re_fintype_sum, re_finset_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _hr
  rw [Finset.sum_comm]

end GoldbachCircleMethodCrossConductorBlockPairReindexV18541
