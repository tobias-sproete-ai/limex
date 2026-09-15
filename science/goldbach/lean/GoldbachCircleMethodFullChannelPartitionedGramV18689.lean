import GoldbachCircleMethodFullDenominatorFourClassPartitionV18688
import GoldbachCircleMethodSignedMagnitudeIdentityV18628

/-!
# V1.8.689: zero-loss full-channel Gram normal form

V1.8.688 partitions the actual project coefficient into the small core, the
selected odd/double aggregate, the four-divisible residual, and the unpaired
odd residual.  This module keeps that identity exact and expands only the
ordinary square energy.

The selected-pair cross terms are retained as an ordered off-diagonal Gram
sum.  The covariance between the paired aggregate and all remaining channels
is retained exactly.  The nonlinear signed-magnitude correlation is not split.

No energy estimate, channel allocation, cardinality factor, common-period
argument, asymptotic bound, exceptional-set estimate, or Goldbach conclusion
is introduced.

`proof_status = NO_PROOF`.
-/

set_option autoImplicit false

open scoped BigOperators Classical

open Filter Topology
open GoldbachCircleMethodExceptionalTransferV1823
open GoldbachCircleMethodTwoScaleEvenBlockDefectReserveV1833
open GoldbachCircleMethodSignedMagnitudeIdentityV18628
open GoldbachCircleMethodUniformModelReserveCubicScaleV18639
open GoldbachCircleMethodEventualAnalyticInputReductionV18642
open GoldbachCircleMethodOddChannelEventualAbsorptionV18658
open GoldbachCircleMethodDiagonalCompensatedEvenSubchannelsV18667
open GoldbachCircleMethodOddOddExactSignedBudgetV18669
open GoldbachCircleMethodOddOddSmallCoreLargePerturbationV18670
open GoldbachCircleMethodOddDoubleSignedRealBridgeV18682
open GoldbachCircleMethodFullDenominatorFourClassPartitionV18688

namespace GoldbachCircleMethodFullChannelPartitionedGramV18689

/-- Bilinear correlation on an exact finite target carrier. -/
def finiteCorrelation {ι : Type*} (s : Finset ι)
    (f g : ι → Real) : Real :=
  ∑ i ∈ s, f i * g i

/-- Ordered off-diagonal Gram contribution of a finite real family.  `erase`
removes exactly the diagonal index and therefore introduces no factor two. -/
def orderedOffDiagonalGram
    {ι α : Type*} [Fintype α] [DecidableEq α]
    (s : Finset ι) (F : α → ι → Real) : Real :=
  ∑ q : α, ∑ r ∈ (Finset.univ.erase q), finiteCorrelation s (F q) (F r)

/-- Pointwise diagonal/off-diagonal expansion of a finite real family. -/
theorem fintype_sum_sq_eq_diagonal_add_orderedOffDiagonal
    {α : Type*} [Fintype α] [DecidableEq α]
    (f : α → Real) :
    (∑ q : α, f q) ^ 2 =
      (∑ q : α, (f q) ^ 2) +
        ∑ q : α, ∑ r ∈ (Finset.univ.erase q), f q * f r := by
  rw [pow_two, Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  calc
    (∑ q : α, ∑ r : α, f q * f r) =
        ∑ q : α,
          ((f q) ^ 2 + ∑ r ∈ (Finset.univ.erase q), f q * f r) := by
      apply Finset.sum_congr rfl
      intro q _hq
      rw [pow_two]
      calc
        (∑ r : α, f q * f r) =
            (∑ r ∈ (Finset.univ.erase q), f q * f r) + f q * f q :=
          (Finset.sum_erase_add _ _ (Finset.mem_univ q)).symm
        _ = f q * f q +
            ∑ r ∈ (Finset.univ.erase q), f q * f r := add_comm _ _
    _ = _ := by rw [Finset.sum_add_distrib]

/-- Exact square-energy Gram expansion. -/
theorem squareEnergy_fintype_sum_eq_diagonal_add_orderedGram
    {ι α : Type*} [Fintype α] [DecidableEq α]
    (s : Finset ι) (F : α → ι → Real) :
    squareEnergy s (fun i => ∑ q : α, F q i) =
      (∑ q : α, squareEnergy s (F q)) +
        orderedOffDiagonalGram s F := by
  unfold squareEnergy orderedOffDiagonalGram finiteCorrelation
  simp_rw [fintype_sum_sq_eq_diagonal_add_orderedOffDiagonal]
  rw [Finset.sum_add_distrib]
  congr 1
  · rw [Finset.sum_comm]
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro q _hq
    rw [Finset.sum_comm]

/-- Exact polarization identity on a finite target carrier. -/
theorem squareEnergy_add_eq
    {ι : Type*} (s : Finset ι) (f g : ι → Real) :
    squareEnergy s (fun i => f i + g i) =
      squareEnergy s f + squareEnergy s g +
        2 * finiteCorrelation s f g := by
  unfold squareEnergy finiteCorrelation
  simp_rw [add_sq]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  rw [Finset.mul_sum]
  ring_nf

/-- One selected odd/double pair as an actual project-normalized function of
the target `N`. -/
noncomputable def projectPairedBaseContribution
    (M : Nat) (q : PairedOddBase (oddProjectRadius M)) (N : Nat) : Real :=
  projectOddDoubleSignedContribution M N q.val
    (pairedDoubleDenominator q)

/-- All non-paired channels, with the inherited signs from V1.8.688. -/
noncomputable def projectNonPairedAggregate (M N : Nat) : Real :=
  compensatedSmallDenominatorCore M (oddProjectWidth M)
      (oddProjectRadius M) N +
    projectFourDivisibleResidual M N +
    projectUnpairedOddResidual M N

/-- The V1.8.688 coefficient identity regrouped as `C = U + P`. -/
theorem projectOddOddCoefficient_eq_nonPaired_add_paired
    (M N : Nat)
    (hscale : 2 * oddProjectWidth M * oddProjectRadius M < M) :
    projectOddOddCoefficient M N =
      projectNonPairedAggregate M N +
        projectPairedOddDoubleAggregate M N := by
  rw [projectOddOddCoefficient_eq_four_class_partition M N hscale]
  unfold projectNonPairedAggregate
  ring_nf

/-- The paired aggregate is literally the finite sum of selected pair
functions; this is the semantic bridge from V1.8.688 to the Gram form. -/
theorem projectPairedOddDoubleAggregate_eq_sum_baseContributions
    (M N : Nat) :
    projectPairedOddDoubleAggregate M N =
      ∑ q : PairedOddBase (oddProjectRadius M),
        projectPairedBaseContribution M q N := by
  rw [projectPairedOddDoubleAggregate_eq_sum_selectedContributions]
  rfl

/-- The actual paired-channel energy equals its diagonal pair energies plus
the full ordered off-diagonal Gram term. -/
theorem projectPairedAggregate_squareEnergy_eq_gram (M : Nat) :
    squareEnergy (evenTargetBlock M)
        (projectPairedOddDoubleAggregate M) =
      (∑ q : PairedOddBase (oddProjectRadius M),
        squareEnergy (evenTargetBlock M)
          (projectPairedBaseContribution M q)) +
      orderedOffDiagonalGram (evenTargetBlock M)
        (projectPairedBaseContribution M) := by
  have hfun : projectPairedOddDoubleAggregate M =
      fun N => ∑ q : PairedOddBase (oddProjectRadius M),
        projectPairedBaseContribution M q N := by
    funext N
    exact projectPairedOddDoubleAggregate_eq_sum_baseContributions M N
  rw [hfun]
  exact squareEnergy_fintype_sum_eq_diagonal_add_orderedGram
    (evenTargetBlock M) (projectPairedBaseContribution M)

/-- Exact scalar named by the full partitioned Gram expansion. -/
noncomputable def partitionedGramEnergy (M : Nat) : Real :=
  squareEnergy (evenTargetBlock M) (projectNonPairedAggregate M) +
    (∑ q : PairedOddBase (oddProjectRadius M),
      squareEnergy (evenTargetBlock M)
        (projectPairedBaseContribution M q)) +
    orderedOffDiagonalGram (evenTargetBlock M)
      (projectPairedBaseContribution M) +
    2 * finiteCorrelation (evenTargetBlock M)
      (projectNonPairedAggregate M)
      (projectPairedOddDoubleAggregate M)

/-- Zero-loss full-channel square-energy identity. -/
theorem projectOddOdd_squareEnergy_eq_partitionedGram
    (M : Nat)
    (hscale : 2 * oddProjectWidth M * oddProjectRadius M < M) :
    squareEnergy (evenTargetBlock M) (projectOddOddCoefficient M) =
      partitionedGramEnergy M := by
  have hfun : projectOddOddCoefficient M =
      fun N => projectNonPairedAggregate M N +
        projectPairedOddDoubleAggregate M N := by
    funext N
    exact projectOddOddCoefficient_eq_nonPaired_add_paired M N hscale
  rw [hfun, squareEnergy_add_eq]
  rw [projectPairedAggregate_squareEnergy_eq_gram]
  unfold partitionedGramEnergy
  ring_nf

/-- Exact one-sided moment identity after the full channel partition.  The
total signed-magnitude correlation remains a single nonlinear object. -/
theorem projectOddOdd_negativePartMoment_eq_partitionedSignedGram
    (M : Nat)
    (hscale : 2 * oddProjectWidth M * oddProjectRadius M < M) :
    negativePartSquaredMoment (evenTargetBlock M)
        (projectOddOddCoefficient M) =
      (partitionedGramEnergy M -
        signedMagnitudeCorrelation (evenTargetBlock M)
          (projectOddOddCoefficient M)) / 2 := by
  rw [projectOddOdd_negativePartMoment_eq_half_signedGap]
  rw [projectOddOdd_squareEnergy_eq_partitionedGram M hscale]

/-- The exact project budget in the partitioned Gram coordinates.  This is an
equivalence only; the strict right-hand inequality is not proved here. -/
theorem projectOddOdd_budget_iff_partitionedSignedGap
    (M : Nat)
    (hscale : 2 * oddProjectWidth M * oddProjectRadius M < M) :
    negativePartSquaredMoment (evenTargetBlock M)
        (projectOddOddCoefficient M) < (M : Real) ^ 2 / 12544 ↔
      partitionedGramEnergy M -
          signedMagnitudeCorrelation (evenTargetBlock M)
            (projectOddOddCoefficient M) <
        (M : Real) ^ 2 / 6272 := by
  rw [projectOddOdd_negativePartMoment_eq_partitionedSignedGram M hscale]
  constructor <;> intro h <;> nlinarith

end GoldbachCircleMethodFullChannelPartitionedGramV18689
