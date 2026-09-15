import GoldbachCircleMethodFullChannelPartitionedGramV18689

/-!
# V1.8.690: exact selected-pair cross-correlation expansion

V1.8.689 exposes the ordered off-diagonal Gram term of the selected odd/double
pair family.  This append-only module expands each such correlation into the
literal finite sum over target `N` and the two independent off-diagonal fiber
indices `t,u`.

The two selected denominator pairs remain separate.  No common global period,
absolute value, Cauchy bound, cardinality factor, or cancellation estimate is
introduced.  The local pairwise-period analysis is a subsequent obligation.

`proof_status = NO_PROOF`.
-/

set_option autoImplicit false

open scoped BigOperators Classical

open GoldbachCircleMethodExceptionalTransferV1823
open GoldbachCircleMethodTwoScaleEvenBlockDefectReserveV1833
open GoldbachCircleMethodUniformModelReserveCubicScaleV18639
open GoldbachCircleMethodOddChannelEventualAbsorptionV18658
open GoldbachCircleMethodOddOddSignedFiberAdapterV18665
open GoldbachCircleMethodOddDoubleSignedRealBridgeV18682
open GoldbachCircleMethodFullDenominatorFourClassPartitionV18688
open GoldbachCircleMethodFullChannelPartitionedGramV18689

namespace GoldbachCircleMethodSelectedPairCrossCorrelationExpansionV18690

/-- Literal real summand of one selected odd/double contribution at one
off-diagonal arithmetic fiber. -/
noncomputable def projectPairedBaseFiberTerm
    (M : Nat) (q : PairedOddBase (oddProjectRadius M))
    (N t : Nat) : Real :=
  oddOddPairFiberMass M t *
    (explicitDenominatorSincTerm M
        (oddProjectWidth M) (oddProjectRadius M)
        ((N : Int) - (t : Int)) q.val +
      explicitDenominatorSincTerm M
        (oddProjectWidth M) (oddProjectRadius M)
        ((N : Int) - (t : Int)) (pairedDoubleDenominator q)).re

/-- Exact one-pair fiber expansion, including the inherited outer minus sign. -/
theorem projectPairedBaseContribution_eq_neg_fiberSum
    (M : Nat) (q : PairedOddBase (oddProjectRadius M)) (N : Nat) :
    projectPairedBaseContribution M q N =
      -∑ t ∈ oddOddOffDiagonalSumCarrier M N,
        projectPairedBaseFiberTerm M q N t := by
  unfold projectPairedBaseContribution projectOddDoubleSignedContribution
    projectPairedBaseFiberTerm
  rfl

/-- Exact `N,t,u` expansion of the correlation of two selected pair
contributions.  The signs cancel only because both inherited outer signs are
present. -/
theorem finiteCorrelation_projectPairedBaseContribution_eq_ntu
    (M : Nat)
    (q r : PairedOddBase (oddProjectRadius M)) :
    finiteCorrelation (evenTargetBlock M)
        (projectPairedBaseContribution M q)
        (projectPairedBaseContribution M r) =
      ∑ N ∈ evenTargetBlock M,
        ∑ t ∈ oddOddOffDiagonalSumCarrier M N,
          ∑ u ∈ oddOddOffDiagonalSumCarrier M N,
            projectPairedBaseFiberTerm M q N t *
              projectPairedBaseFiberTerm M r N u := by
  unfold finiteCorrelation
  apply Finset.sum_congr rfl
  intro N _hN
  rw [projectPairedBaseContribution_eq_neg_fiberSum,
    projectPairedBaseContribution_eq_neg_fiberSum]
  rw [neg_mul_neg, Finset.sum_mul]
  simp_rw [Finset.mul_sum]

/-- The complete ordered pair Gram term from V1.8.689 in literal finite
`q,r,N,t,u` coordinates.  The `erase q` carrier keeps exactly `q != r`. -/
theorem orderedOffDiagonalGram_eq_qrntu (M : Nat) :
    orderedOffDiagonalGram (evenTargetBlock M)
        (projectPairedBaseContribution M) =
      ∑ q : PairedOddBase (oddProjectRadius M),
        ∑ r ∈ (Finset.univ.erase q),
          ∑ N ∈ evenTargetBlock M,
            ∑ t ∈ oddOddOffDiagonalSumCarrier M N,
              ∑ u ∈ oddOddOffDiagonalSumCarrier M N,
                projectPairedBaseFiberTerm M q N t *
                  projectPairedBaseFiberTerm M r N u := by
  unfold orderedOffDiagonalGram
  simp_rw [finiteCorrelation_projectPairedBaseContribution_eq_ntu]

end GoldbachCircleMethodSelectedPairCrossCorrelationExpansionV18690
