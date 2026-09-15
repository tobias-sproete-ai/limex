import GoldbachMainTermDominanceBridgeV162

/-!
# Circle-method target interface, V1.7 candidate

This module contains only a conditional, algebraic main-term/remainder-term
interface. It does not define the major or minor arcs, prove a Fourier
identity, or construct bounds satisfying the interface.
-/

set_option autoImplicit false

namespace GoldbachCircleMethodTargetV17

open GoldbachVonMangoldtDecompositionV16

/-- The exact threshold already consumed by the kernel-checked V1.6.2 bridge. -/
noncomputable def explicitDefectThreshold (N : Nat) : Real :=
  4 * Real.sqrt (N : Real) * (Real.log (N : Real)) ^ 2

/-- No Fourier or circle-method identity is claimed by this candidate. -/
inductive AnalyticIdentityStatus where
  | open
deriving Repr, DecidableEq

def analyticIdentityStatus : AnalyticIdentityStatus := .open

/--
Pointwise algebraic interface at the same natural number `N` as the exact
von-Mangoldt pair sum. The fields are not asserted to be actual major- and
minor-arc integrals.
-/
structure MainRemainderDecompositionAt (N : Nat) where
  mainTerm : Real
  remainderTerm : Real
  exact_sum_identity :
    vonMangoldtPairSum N = mainTerm + remainderTerm

/--
Explicit pointwise bounds sufficient to make the main term dominate both the
remainder budget and V1.6.2's defect threshold. No inhabitant is constructed.
-/
structure ExplicitDominanceBoundsAt
    {N : Nat} (decomposition : MainRemainderDecompositionAt N) where
  mainLowerBound : Real
  remainderBudget : Real
  main_lower_bound : mainLowerBound ≤ decomposition.mainTerm
  remainder_absolute_bound :
    |decomposition.remainderTerm| ≤ remainderBudget
  threshold_plus_budget_lt_main_lower :
    explicitDefectThreshold N + remainderBudget < mainLowerBound

/--
Pure algebraic consequence of an exact decomposition and explicit bounds.
This theorem does not prove or construct those hypotheses.
-/
theorem explicit_bounds_imply_required_threshold
    {N : Nat}
    (decomposition : MainRemainderDecompositionAt N)
    (bounds : ExplicitDominanceBoundsAt decomposition) :
    4 * Real.sqrt (N : Real) * (Real.log (N : Real)) ^ 2 <
      vonMangoldtPairSum N := by
  change explicitDefectThreshold N < vonMangoldtPairSum N
  have hRemainderLower :
      -bounds.remainderBudget ≤ decomposition.remainderTerm := by
    exact (neg_le_neg bounds.remainder_absolute_bound).trans
      (neg_abs_le decomposition.remainderTerm)
  rw [decomposition.exact_sum_identity]
  linarith [bounds.main_lower_bound,
    bounds.threshold_plus_budget_lt_main_lower,
    hRemainderLower]

/--
The unchanged outer quantifiers for a future analytic result: every even
`N ≥ N0` must receive its own exact decomposition and bounds. This structure
is an input contract, not an existence theorem.
-/
structure UniformMainRemainderInterface (N0 : Nat) where
  decomposition :
    ∀ (N : Nat), N0 ≤ N → Even N → MainRemainderDecompositionAt N
  bounds :
    ∀ (N : Nat) (hN0 : N0 ≤ N) (hEven : Even N),
      ExplicitDominanceBoundsAt (decomposition N hN0 hEven)

/-- The output retains exactly the input domain `∀ even N ≥ N0`. -/
theorem uniform_interface_implies_required_threshold
    {N0 : Nat}
    (interface : UniformMainRemainderInterface N0) :
    ∀ (N : Nat), N0 ≤ N → Even N →
      4 * Real.sqrt (N : Real) * (Real.log (N : Real)) ^ 2 <
        vonMangoldtPairSum N := by
  intro N hN0 hEven
  exact explicit_bounds_imply_required_threshold
    (interface.decomposition N hN0 hEven)
    (interface.bounds N hN0 hEven)

end GoldbachCircleMethodTargetV17
