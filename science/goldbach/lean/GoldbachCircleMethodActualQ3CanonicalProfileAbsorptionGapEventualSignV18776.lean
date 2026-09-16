import GoldbachCircleMethodActualQ3CanonicalProfileCeilingReserveDominanceDecisionV18775

/-!
# V1.8.776: canonical q=3 absorption-gap sign decision

This module makes the loss in the canonical profile-ceiling route exact.  The
literal actual-source composite reserve is the canonical absorption gap plus a
nonnegative slack.  The slack is the canonical debit together with the real
part of the exact Abel remainder.

Consequently, negativity of the canonical gap is not an actual-source
negative witness.  In the opposite direction, every negative value of the
literal actual-source reserve forces the canonical gap to be negative, and an
unbounded actual negative sequence transports to an unbounded negative-gap
sequence.

Neither an eventual positive sign for the canonical gap nor an unbounded
negative sequence for the literal actual-source reserve is proved here.  The
requested decision gate therefore remains fail-closed and
`proof_status = NO_PROOF`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

open scoped BigOperators Classical
open Filter Topology

namespace GoldbachCircleMethodActualQ3CanonicalProfileAbsorptionGapEventualSignV18776

open GoldbachCircleMethodTwoScaleEvenBlockDefectReserveV1833
open GoldbachCircleMethodOddChannelEventualAbsorptionV18658
open GoldbachCircleMethodFullDenominatorFourClassPartitionV18688
open GoldbachCircleMethodUniformModelReserveCubicScaleV18639
open GoldbachCircleMethodActualQ3PrefixLocalDensityExtractionV18753
open GoldbachCircleMethodActualModelQ3PreLoweringRecombinationV18769
open GoldbachCircleMethodActualModelQ3CompositeReserveFloorDecisionV18770
open GoldbachCircleMethodActualQ3ResidueSelectorMainProfileAbsorptionV18774
open GoldbachCircleMethodActualQ3CanonicalProfileCeilingReserveDominanceDecisionV18775

/-- Exact compensation left after the canonical total-variation debit has
been subtracted. -/
noncomputable def actualQ3CanonicalProfileAbsorptionSlack
    (M n : Nat)
    (q : PairedOddBase (oddProjectRadius M)) : Real :=
  actualQ3CanonicalCenteredProfileDebit M n q +
    (actualQ3LocalDensityTriangularRemainder M q n).re

/-- The compensation is nonnegative: the canonical debit majorizes the norm,
and hence the negative real part, of the literal Abel remainder. -/
theorem actualQ3CanonicalProfileAbsorptionSlack_nonneg
    {M n : Nat} (hM : 0 < M)
    (q : PairedOddBase (oddProjectRadius M))
    (hn : n ≤ M) :
    0 ≤ actualQ3CanonicalProfileAbsorptionSlack M n q := by
  have hNorm :=
    actualQ3LocalDensityTriangularRemainder_norm_le_canonicalDebit
      hM q hn
  have hAbsRe :
      |(actualQ3LocalDensityTriangularRemainder M q n).re| ≤
        ‖actualQ3LocalDensityTriangularRemainder M q n‖ :=
    Complex.abs_re_le_norm _
  have hNegAbs :
      -|(actualQ3LocalDensityTriangularRemainder M q n).re| ≤
        (actualQ3LocalDensityTriangularRemainder M q n).re :=
    neg_abs_le _
  unfold actualQ3CanonicalProfileAbsorptionSlack
  linarith

/-- Exact identity: the literal reserve is the pessimistic canonical gap plus
the nonnegative compensation that the norm estimate discarded. -/
theorem actualModelQ3CompositeReserve_eq_canonicalGap_add_slack
    (M R n : Nat) (P : Real)
    (q : PairedOddBase (oddProjectRadius M)) :
    actualModelQ3PreLoweringCompositeReserve M R n P q =
      actualQ3CanonicalProfileAbsorptionGap M R n P q +
        actualQ3CanonicalProfileAbsorptionSlack M n q := by
  rw [actualModelQ3PreLoweringCompositeReserve_eq_literal_source]
  unfold actualQ3CanonicalProfileAbsorptionGap
    actualQ3CanonicalProfileAbsorptionSlack
    actualQ3ResidueSelectorBaseReserve
  ring

/-- A negative literal actual-source reserve forces the canonical lower
envelope itself to be negative.  The converse is deliberately not claimed. -/
theorem canonicalGap_neg_of_actualCompositeReserve_neg
    {M R n : Nat} {P : Real}
    (hM : 0 < M)
    (q : PairedOddBase (oddProjectRadius M))
    (hn : n ≤ M)
    (hNegative :
      actualModelQ3PreLoweringCompositeReserve M R n P q < 0) :
    actualQ3CanonicalProfileAbsorptionGap M R n P q < 0 := by
  have hSlack :=
    actualQ3CanonicalProfileAbsorptionSlack_nonneg hM q hn
  rw [actualModelQ3CompositeReserve_eq_canonicalGap_add_slack] at hNegative
  linarith

/-- Negative canonical gaps at arbitrarily large admissible scales.  This is
only a necessary image of an actual negative sequence, not a sufficient
actual-source witness. -/
def UnboundedActualQ3CanonicalProfileAbsorptionGapNegative : Prop :=
  ∀ M₀ : Nat, ∃ M R : Nat, M₀ ≤ M ∧ 1 ≤ R ∧
    16 * R ^ 3 < M ∧
      ∃ q : PairedOddBase (oddProjectRadius M), ∃ n : Nat,
        2 * n ∈ evenTargetBlock M ∧ q.val.val = 3 ∧
          actualQ3CanonicalProfileAbsorptionGap M R n
            (cubicModelScale R) q < 0

/-- Every unbounded literal actual-source negative sequence projects to an
unbounded negative sequence for the canonical gap. -/
theorem unboundedCanonicalGapNegative_of_unboundedActualCompositeNegative
    (hNegative : UnboundedActualModelQ3CompositeReserveNegative) :
    UnboundedActualQ3CanonicalProfileAbsorptionGapNegative := by
  intro M₀
  rcases hNegative (max M₀ 1) with
    ⟨M, R, hM, hR, hScale, q, n, hTarget, hq, hNegativeM⟩
  have hM₀M : M₀ ≤ M := (le_max_left M₀ 1).trans hM
  have hMpos : 0 < M :=
    lt_of_lt_of_le Nat.zero_lt_one ((le_max_right M₀ 1).trans hM)
  have hUpper :=
    ((mem_evenTargetBlock_iff M (2 * n)).mp hTarget).2.1
  have hn : n ≤ M := by omega
  refine ⟨M, R, hM₀M, hR, hScale, q, n, hTarget, hq, ?_⟩
  exact canonicalGap_neg_of_actualCompositeReserve_neg
    hMpos q hn hNegativeM

end GoldbachCircleMethodActualQ3CanonicalProfileAbsorptionGapEventualSignV18776
