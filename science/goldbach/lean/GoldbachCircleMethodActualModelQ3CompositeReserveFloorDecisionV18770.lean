import GoldbachCircleMethodActualModelQ3PreLoweringRecombinationV18769

/-!
# V1.8.770: actual-model/q=3 composite-reserve floor decision

This module fixes the two genuinely opposing outcomes for the correctly
recombined V1.8.769 reserve at the established cubic project scale.  It also
removes the bookkeeping constant `M / 14` definitionally: the composite is
the literal discrete model plus the signed q=3 pair-residue endpoint and the
local-density Abel remainder.

Neither the positive floor nor the unbounded negative-witness proposition is
inhabited.  The module therefore records the exact open analytic interface;
it is not a proof of Goldbach.  `proof_status = NO_PROOF`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

open Filter Topology

namespace GoldbachCircleMethodActualModelQ3CompositeReserveFloorDecisionV18770

open GoldbachCircleMethodTwoScaleEvenBlockDefectReserveV1833
open GoldbachCircleMethodDiscreteArcModelReserveV1855
open GoldbachCircleMethodOddChannelEventualAbsorptionV18658
open GoldbachCircleMethodFullDenominatorFourClassPartitionV18688
open GoldbachCircleMethodUniformModelReserveCubicScaleV18639
open GoldbachCircleMethodActualLambdaPairSourceMeanV710AdapterV18717
open GoldbachCircleMethodActualQ3PairResidueSignedTriangularGateV18748
open GoldbachCircleMethodActualQ3PrefixLocalDensityExtractionV18753
open GoldbachCircleMethodActualQ3PrefixLocalDensitySignedReserveV18755
open GoldbachCircleMethodActualModelQ3PreLoweringRecombinationV18769

/-- Exact source expansion.  In particular, `M / 14` is not an additional
positive contribution: it cancels between the two reserve definitions. -/
theorem actualModelQ3PreLoweringCompositeReserve_eq_literal_source
    (M R n : Nat) (P : Real)
    (q : PairedOddBase (oddProjectRadius M)) :
    actualModelQ3PreLoweringCompositeReserve M R n P q =
      discreteArcMainModel M (2 * n) R P +
        (3 * selectedPairSourceCoordinateSincWeight M q n M *
          actualQ3PairResidueDefect M n).re +
        (actualQ3LocalDensityTriangularRemainder M q n).re := by
  unfold actualModelQ3PreLoweringCompositeReserve
    actualQ3PrefixLocalDensityProjectReserve
    actualQ3PairResidueProjectReserve
  ring

/-- Uniform eventual positive linear floor on the actual project carrier. -/
def EventualActualModelQ3CompositeReserveFloor (rho : Real) : Prop :=
  ∀ᶠ M : Nat in atTop,
    ∀ R : Nat, 1 ≤ R → 16 * R ^ 3 < M →
      ∀ q : PairedOddBase (oddProjectRadius M),
        ∀ n : Nat, 2 * n ∈ evenTargetBlock M → q.val.val = 3 →
          rho * (M : Real) ≤
            actualModelQ3PreLoweringCompositeReserve M R n
              (cubicModelScale R) q

/-- Actual-source negative values at arbitrarily large admissible project
scales.  This is evidence against every strictly positive eventual floor. -/
def UnboundedActualModelQ3CompositeReserveNegative : Prop :=
  ∀ M₀ : Nat, ∃ M R : Nat, M₀ ≤ M ∧ 1 ≤ R ∧
    16 * R ^ 3 < M ∧
      ∃ q : PairedOddBase (oddProjectRadius M), ∃ n : Nat,
        2 * n ∈ evenTargetBlock M ∧ q.val.val = 3 ∧
          actualModelQ3PreLoweringCompositeReserve M R n
            (cubicModelScale R) q < 0

theorem not_eventual_positive_floor_of_unbounded_actual_negative
    (rho : Real) (hrho : 0 < rho)
    (hnegative : UnboundedActualModelQ3CompositeReserveNegative) :
    ¬ EventualActualModelQ3CompositeReserveFloor rho := by
  intro hfloor
  rcases (eventually_atTop.1 hfloor) with ⟨M₀, hM₀⟩
  rcases hnegative (max M₀ 1) with
    ⟨M, R, hM, hR, hcubic, q, n, hTarget, hq, hnegativeM⟩
  have hM₀M : M₀ ≤ M := (le_max_left M₀ 1).trans hM
  have hMposNat : 0 < M :=
    lt_of_lt_of_le Nat.zero_lt_one ((le_max_right M₀ 1).trans hM)
  have hMposReal : (0 : Real) < M := by exact_mod_cast hMposNat
  have hpositive : 0 < rho * (M : Real) := mul_pos hrho hMposReal
  have hbound := hM₀ M hM₀M R hR hcubic q n hTarget hq
  linarith

end GoldbachCircleMethodActualModelQ3CompositeReserveFloorDecisionV18770
