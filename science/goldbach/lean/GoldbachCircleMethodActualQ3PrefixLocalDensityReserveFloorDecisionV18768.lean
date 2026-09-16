import GoldbachCircleMethodActualQ3FullConditionalClosureV18767

/-!
# V1.8.768: actual q=3 prefix-local-density reserve-floor decision gate

V1.8.767 exposes a positive eventual linear floor on the literal q=3
prefix-local-density project reserve as an open premise.  This module fixes
the exact opposing proposition on the same source and carrier: negative
values occur at arbitrarily large project scales.

The kernel proves that this actual-source negative-witness proposition is
incompatible with every strictly positive eventual floor.  It does not
inhabit either side.  Finite floating-point probes are therefore evidence
only and cannot be promoted to a theorem through this module.

`proof_status = NO_PROOF`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

open Filter Topology

namespace GoldbachCircleMethodActualQ3PrefixLocalDensityReserveFloorDecisionV18768

open GoldbachCircleMethodTwoScaleEvenBlockDefectReserveV1833
open GoldbachCircleMethodCeilScaleEnvelopesV1864
open GoldbachCircleMethodUniformMajorPrefixReductionV1865
open GoldbachCircleMethodOddChannelEventualAbsorptionV18658
open GoldbachCircleMethodFullDenominatorFourClassPartitionV18688
open GoldbachCircleMethodActualQ3PrefixLocalDensitySignedReserveV18755
open GoldbachCircleMethodActualQ3FullConditionalClosureV18767

/-- Actual-source negative witness at arbitrarily large project scales.
The reserve is the literal V1.8.755 von-Mangoldt reserve; no model carrier is
substituted. -/
def UnboundedActualQ3PrefixLocalDensityReserveNegative : Prop :=
  ∀ M₀ : Nat, ∃ M : Nat, M₀ ≤ M ∧
    ∃ q : PairedOddBase (oddProjectRadius M), ∃ n : Nat,
      2 * n ∈ evenTargetBlock M ∧ q.val.val = 3 ∧
        actualQ3PrefixLocalDensityProjectReserve M q n < 0

/-- A genuine unbounded negative witness on the literal source rules out
every positive eventual linear floor on that same reserve. -/
theorem not_eventual_positive_floor_of_unbounded_actual_negative
    (rho : Real) (hrho : 0 < rho)
    (hnegative : UnboundedActualQ3PrefixLocalDensityReserveNegative) :
    ¬ EventualActualQ3PrefixLocalDensityReserveFloor rho := by
  intro hfloor
  rcases (eventually_atTop.1 hfloor) with ⟨M₀, hM₀⟩
  rcases hnegative (max M₀ 1) with
    ⟨M, hM, q, n, hTarget, hq, hnegativeM⟩
  have hM₀M : M₀ ≤ M := (le_max_left M₀ 1).trans hM
  have hMposNat : 0 < M := by
    exact lt_of_lt_of_le Nat.zero_lt_one ((le_max_right M₀ 1).trans hM)
  have hMposReal : (0 : Real) < M := by exact_mod_cast hMposNat
  have hpositive : 0 < rho * (M : Real) := mul_pos hrho hMposReal
  have hbound := hM₀ M hM₀M q n hTarget hq
  linarith

end GoldbachCircleMethodActualQ3PrefixLocalDensityReserveFloorDecisionV18768
