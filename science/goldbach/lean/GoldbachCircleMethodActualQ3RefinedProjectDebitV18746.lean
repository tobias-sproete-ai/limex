import GoldbachCircleMethodActualQ3EndpointSpectralBudgetV18745

/-!
# V1.8.746: source-bound refined q=3 project debit

The literal q=3 project debit from V1.8.740 consists of the negative part of
the complete local-density endpoint and the incomplete source-weighted prefix
fluctuation budget.  V1.8.745 bounds the first term by a source-bound spectral
quantity.  This module composes those facts without changing either the
project reserve or the incomplete-prefix contract.

The resulting criterion is sufficient but not proved to hold for the actual
von-Mangoldt source.  In particular, this module proves no arithmetic decay of
the nonzero q=3 modes and no nontrivial bound for the incomplete triangular
prefixes.  `proof_status = NO_PROOF`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

open scoped Classical

namespace GoldbachCircleMethodActualQ3RefinedProjectDebitV18746

open GoldbachCircleMethodActualQ3EndpointSpectralBudgetV18745
open GoldbachCircleMethodActualQ3SignPrefixFluctuationProjectReserveV18740
open GoldbachCircleMethodTwoScaleEvenBlockDefectReserveV1833
open GoldbachCircleMethodFullDenominatorFourClassPartitionV18688
open GoldbachCircleMethodOddChannelEventualAbsorptionV18658
open GoldbachCircleMethodUniformModelReserveCubicScaleV18639
open GoldbachCircleMethodDiscreteArcModelReserveV1855
open GoldbachCircleMethodActualMixedChannelRamanujanFactorizationV18727

/-- Source-bound upper envelope for the actual q=3 project debit.  The first
term is the exact complete-endpoint spectral budget; the second remains the
already kernelized incomplete-prefix fluctuation budget. -/
noncomputable def actualQ3RefinedProjectDebit
    (M : Nat)
    (q : PairedOddBase (oddProjectRadius M))
    (n : Nat) : Real :=
  actualQ3EndpointSpectralBudget M q n +
    actualQ3SourceBoundPrefixFluctuationBudget M q n

theorem actualQ3RefinedProjectDebit_nonneg
    (M : Nat)
    (q : PairedOddBase (oddProjectRadius M))
    (n : Nat) :
    0 ≤ actualQ3RefinedProjectDebit M q n := by
  unfold actualQ3RefinedProjectDebit
  exact add_nonneg
    (actualQ3EndpointSpectralBudget_nonneg M q n)
    (actualQ3SourceBoundPrefixFluctuationBudget_nonneg M q n)

/-- At the genuine denominator-three branch, the literal deterministic debit
is bounded by the refined source-bound debit. -/
theorem actualQ3ProjectDebit_le_refinedProjectDebit
    (M : Nat)
    (q : PairedOddBase (oddProjectRadius M))
    (n : Nat)
    (hq : q.val.val = 3) :
    actualQ3ProjectDebit M q n ≤ actualQ3RefinedProjectDebit M q n := by
  unfold actualQ3ProjectDebit actualQ3RefinedProjectDebit
  exact add_le_add
    (actualQ3LocalDensitySignDebit_le_endpointSpectralBudget M q n hq)
    le_rfl

/-- A strict refined-debit estimate therefore discharges the original exact
project-debit premise. -/
theorem actualQ3ProjectDebit_lt_one_fourteenth_of_refinedProjectDebit
    {M : Nat}
    (q : PairedOddBase (oddProjectRadius M))
    (n : Nat)
    (hq : q.val.val = 3)
    (hRefined : actualQ3RefinedProjectDebit M q n < (M : Real) / 14) :
    actualQ3ProjectDebit M q n < (M : Real) / 14 :=
  (actualQ3ProjectDebit_le_refinedProjectDebit M q n hq).trans_lt hRefined

/-- Direct reserve absorption from the refined source-bound criterion. -/
theorem projectReserve_add_negativeAggregate_re_pos_of_refinedProjectDebit
    {M : Nat} (hM : 0 < M)
    (q : PairedOddBase (oddProjectRadius M))
    (n : Nat) (hTarget : 2 * n ∈ evenTargetBlock M)
    (hq : q.val.val = 3)
    (hRefined : actualQ3RefinedProjectDebit M q n < (M : Real) / 14) :
    0 < (M : Real) / 14 +
      (selectedPairNegativeCenteredUnitAggregate M q n).re := by
  exact projectReserve_add_negativeAggregate_re_pos_of_projectDebit hM q n
    hTarget hq
    (actualQ3ProjectDebit_lt_one_fourteenth_of_refinedProjectDebit
      q n hq hRefined)

/-- Kernelized link to the discrete project main term at cubic scale.  The
only unproved mathematical premise is the displayed strict refined-debit
inequality. -/
theorem discreteProjectMain_add_negativeAggregate_re_pos_of_refinedProjectDebit
    {M R : Nat} (hM : 32 ≤ M) (hR : 1 ≤ R)
    (hcubic : 16 * R ^ 3 < M)
    (q : PairedOddBase (oddProjectRadius M))
    (n : Nat) (hTarget : 2 * n ∈ evenTargetBlock M)
    (hq : q.val.val = 3)
    (hRefined : actualQ3RefinedProjectDebit M q n < (M : Real) / 14) :
    0 < discreteArcMainModel M (2 * n) R (cubicModelScale R) +
      (selectedPairNegativeCenteredUnitAggregate M q n).re := by
  exact discreteProjectMain_add_negativeAggregate_re_pos_of_projectDebit
    hM hR hcubic q n hTarget hq
    (actualQ3ProjectDebit_lt_one_fourteenth_of_refinedProjectDebit
      q n hq hRefined)

end GoldbachCircleMethodActualQ3RefinedProjectDebitV18746
