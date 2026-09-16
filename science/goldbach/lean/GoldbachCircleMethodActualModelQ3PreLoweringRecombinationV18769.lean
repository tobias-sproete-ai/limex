import GoldbachCircleMethodActualQ3PrefixLocalDensityReserveFloorDecisionV18768

/-!
# V1.8.769: actual model/q=3 recombination before global reserve lowering

V1.8.768 quarantines the attempt to prove a positive eventual floor for the
isolated `q = 3` local-density reserve after the discrete model has already
been lowered to `M / 14`.  This successor restores the information discarded
by that early lowering.

The discrete model is kept at its literal value.  Its surplus above `M / 14`
is composed with the exact V1.8.755 prefix-local-density reserve before any
positivity test is applied.  The resulting identity is exact and source-bound.
It shows that the old isolated reserve is only a conservative sub-reserve of
the new composite whenever the established model floor holds.

No lower bound for the new composite reserve is asserted here.  In particular,
this module does not prove the local major approximation, an exceptional-set
estimate, or Goldbach.  `proof_status = NO_PROOF`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

open scoped BigOperators Classical

namespace GoldbachCircleMethodActualModelQ3PreLoweringRecombinationV18769

open GoldbachCircleMethodTwoScaleEvenBlockDefectReserveV1833
open GoldbachCircleMethodOddChannelEventualAbsorptionV18658
open GoldbachCircleMethodFullDenominatorFourClassPartitionV18688
open GoldbachCircleMethodDiscreteArcModelReserveV1855
open GoldbachCircleMethodActualMixedChannelRamanujanFactorizationV18727
open GoldbachCircleMethodActualQ3PrefixLocalDensityExtractionV18753
open GoldbachCircleMethodActualQ3PrefixLocalDensitySignedReserveV18755
open GoldbachCircleMethodActualQ3PrefixLocalDensityReserveFloorDecisionV18768

/-- The reserve retained when the literal discrete model is not prematurely
replaced by its coarse lower bound `M / 14`.  The first summand is precisely
the information lost by that replacement; the second is the exact actual
`q = 3` prefix-local-density reserve from V1.8.755. -/
noncomputable def actualModelQ3PreLoweringCompositeReserve
    (M R n : Nat) (P : Real)
    (q : PairedOddBase (oddProjectRadius M)) : Real :=
  (discreteArcMainModel M (2 * n) R P - (M : Real) / 14) +
    actualQ3PrefixLocalDensityProjectReserve M q n

/-- Exact recombination before lowering.  No estimate is used: the identity
is the V1.8.755 source decomposition plus the literal model surplus that the
old `M / 14` substitution discarded. -/
theorem discreteModel_add_negativeAggregate_re_eq_compositeReserve_add_unitBalance_re
    (M R n : Nat) (P : Real)
    (q : PairedOddBase (oddProjectRadius M))
    (hTarget : 2 * n ∈ evenTargetBlock M)
    (hq : q.val.val = 3) :
    discreteArcMainModel M (2 * n) R P +
        (selectedPairNegativeCenteredUnitAggregate M q n).re =
      actualModelQ3PreLoweringCompositeReserve M R n P q +
        (actualQ3UnitBalanceTriangularRemainder M q n).re := by
  have hExact :=
    projectReserve_add_negativeAggregate_re_eq_prefixLocalDensityReserve_add_unitBalance_re
      M q n hTarget hq
  unfold actualModelQ3PreLoweringCompositeReserve
  linarith

/-- The old isolated V1.8.755 reserve is a lower bound for the correctly
recombined reserve whenever the already established discrete-model floor is
available. -/
theorem prefixLocalDensityReserve_le_compositeReserve_of_modelFloor
    (M R n : Nat) (P : Real)
    (q : PairedOddBase (oddProjectRadius M))
    (hModel : (M : Real) / 14 ≤ discreteArcMainModel M (2 * n) R P) :
    actualQ3PrefixLocalDensityProjectReserve M q n ≤
      actualModelQ3PreLoweringCompositeReserve M R n P q := by
  unfold actualModelQ3PreLoweringCompositeReserve
  linarith

/-- Correct sign-sensitive positivity gate.  The adverse unit-balance term is
charged against the complete pre-lowering composite, not against the isolated
`q = 3` reserve. -/
theorem discreteModel_add_negativeAggregate_re_pos_of_unitBalanceDebit_lt_compositeReserve
    (M R n : Nat) (P : Real)
    (q : PairedOddBase (oddProjectRadius M))
    (hTarget : 2 * n ∈ evenTargetBlock M)
    (hq : q.val.val = 3)
    (hDebit : actualQ3UnitBalanceSignDebit M q n <
      actualModelQ3PreLoweringCompositeReserve M R n P q) :
    0 < discreteArcMainModel M (2 * n) R P +
      (selectedPairNegativeCenteredUnitAggregate M q n).re := by
  have hNonneg := unitBalanceRemainder_re_add_signDebit_nonneg M q n
  rw [discreteModel_add_negativeAggregate_re_eq_compositeReserve_add_unitBalance_re
    M R n P q hTarget hq]
  linarith

/-- Every proof through the older, stronger debit gate transports to the new
pre-lowering gate.  The converse is deliberately not claimed. -/
theorem old_unitBalanceDebit_gate_implies_preLowering_gate
    (M R n : Nat) (P : Real)
    (q : PairedOddBase (oddProjectRadius M))
    (hModel : (M : Real) / 14 ≤ discreteArcMainModel M (2 * n) R P)
    (hOld : actualQ3UnitBalanceSignDebit M q n <
      actualQ3PrefixLocalDensityProjectReserve M q n) :
    actualQ3UnitBalanceSignDebit M q n <
      actualModelQ3PreLoweringCompositeReserve M R n P q := by
  exact hOld.trans_le
    (prefixLocalDensityReserve_le_compositeReserve_of_modelFloor
      M R n P q hModel)

end GoldbachCircleMethodActualModelQ3PreLoweringRecombinationV18769
