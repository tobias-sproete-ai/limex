import GoldbachCircleMethodCrossDenominatorCollisionPartitionV18547
import GoldbachCircleMethodCrossConductorBlockPairReindexV18541

/-!
# Goldbach V1.8.575: global collision-residual split

The actual cross-conductor block residual is split exactly into the
product-denominator collision branch and its complement.  The literal
expansion from V1.8.546 is valid only for nontrivial conductor levels, so
both branches are guarded explicitly at level one.  This makes the global
identity total without assigning literal mass to the channel removed by the
definition of `nonprincipalConductorCorrelation`.

No cancellation, asymptotic estimate, or Goldbach statement is asserted.
-/

set_option autoImplicit false

open scoped BigOperators Classical ComplexConjugate

namespace GoldbachCircleMethodGlobalCollisionResidualSplitV18575

open GoldbachCircleMethodActualCrossLiteralBlockExpansionV18546
open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodCrossConductorBlockPairReindexV18541
open GoldbachCircleMethodCrossDenominatorCollisionPartitionV18547
open GoldbachCircleMethodExactCrossConductorResidualV18538
open GoldbachCircleMethodNonprincipalConductorAlignedCorrelationV18527

/-- Collision contribution of one ordered conductor pair, with the
conductor-one channel removed exactly as in the actual nonprincipal source. -/
noncomputable def guardedCollisionPairResidual
    (Q B : ℕ) (H : ℝ) (w : ℕ → ℂ)
    (r s : PositiveLevel Q) : ℝ :=
  if r.val = 1 ∨ s.val = 1 then 0 else
    collisionLiteralCrossBlockCorrelation Q B H w r s

/-- Noncollision contribution of one ordered conductor pair, with the same
conductor-one guard as the collision branch. -/
noncomputable def guardedSeparatedPairResidual
    (Q B : ℕ) (H : ℝ) (w : ℕ → ℂ)
    (r s : PositiveLevel Q) : ℝ :=
  if r.val = 1 ∨ s.val = 1 then 0 else
    separatedLiteralCrossBlockCorrelation Q B H w r s

/-- The actual pair correlation is exactly the sum of its guarded collision
and separated pieces, including the conductor-one edge case. -/
theorem conductorPairBlockCorrelation_eq_guarded_collision_add_separated
    (Q B : ℕ) (H : ℝ) (w : ℕ → ℂ)
    (r s : PositiveLevel Q) :
    conductorPairBlockCorrelation Q B H w r s =
      guardedCollisionPairResidual Q B H w r s +
        guardedSeparatedPairResidual Q B H w r s := by
  by_cases hlevel : r.val = 1 ∨ s.val = 1
  · rw [guardedCollisionPairResidual, if_pos hlevel,
      guardedSeparatedPairResidual, if_pos hlevel, add_zero]
    rcases hlevel with hr | hs
    · unfold conductorPairBlockCorrelation
      simp [nonprincipalConductorCorrelation, hr]
    · unfold conductorPairBlockCorrelation
      simp [nonprincipalConductorCorrelation, hs]
  · have hr : r.val ≠ 1 := fun h => hlevel (Or.inl h)
    have hs : s.val ≠ 1 := fun h => hlevel (Or.inr h)
    rw [guardedCollisionPairResidual, if_neg hlevel,
      guardedSeparatedPairResidual, if_neg hlevel,
      conductorPairBlockCorrelation_eq_literalCrossBlockCorrelation
        Q B H w r s hr hs,
      literalCrossBlockCorrelation_eq_collision_add_separated]

/-- Global collision part of the genuine ordered cross-conductor residual. -/
noncomputable def blockCollisionResidual
    (Q B : ℕ) (H : ℝ) (w : ℕ → ℂ) : ℝ :=
  ∑ r : PositiveLevel Q,
    ∑ s ∈ (Finset.univ.erase r),
      guardedCollisionPairResidual Q B H w r s

/-- Global noncollision part of the genuine ordered cross-conductor residual. -/
noncomputable def blockSeparatedResidual
    (Q B : ℕ) (H : ℝ) (w : ℕ → ℂ) : ℝ :=
  ∑ r : PositiveLevel Q,
    ∑ s ∈ (Finset.univ.erase r),
      guardedSeparatedPairResidual Q B H w r s

/-- Exact global connector from the actual residual to the collision and
noncollision branches.  This is an identity only; neither branch is bounded. -/
theorem blockCrossConductorResidual_eq_collision_add_separated
    (Q B : ℕ) (H : ℝ) (w : ℕ → ℂ) :
    blockCrossConductorResidual Q B H w =
      blockCollisionResidual Q B H w +
        blockSeparatedResidual Q B H w := by
  rw [blockCrossConductorResidual_eq_sum_pair_block_correlations]
  unfold blockCollisionResidual blockSeparatedResidual
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r _hr
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro s _hs
  exact conductorPairBlockCorrelation_eq_guarded_collision_add_separated
    Q B H w r s

end GoldbachCircleMethodGlobalCollisionResidualSplitV18575
