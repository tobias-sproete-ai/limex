import GoldbachCircleMethodActualCenteredSourcePrefixComplementBudgetV18736

/-!
# V1.8.737: inhabited source-bound envelope for the actual q=3 defect

V1.8.736 leaves one open prefix envelope `D` for the actual progression defect
modulo three.  This append-only module constructs a canonical inhabitant from
the definitionally fixed centered Lambda-pair source itself: the full absolute
mass in the selected residue class.

This removes the logical risk of a vacuous conditional theorem.  It does not
prove the resulting deterministic envelope small; the analytic absorption
problem remains completely open.

No distribution theorem, minor-arc absorption, exceptional-set estimate, or
Goldbach conclusion is proved.  `proof_status = NO_PROOF`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

open scoped BigOperators Classical

namespace GoldbachCircleMethodActualQ3SourceBoundDefectEnvelopeV18737

open GoldbachCircleMethodTwoScaleEvenBlockDefectReserveV1833
open GoldbachCircleMethodOddChannelEventualAbsorptionV18658
open GoldbachCircleMethodFullDenominatorFourClassPartitionV18688
open GoldbachCircleMethodActualLambdaPairSourceMeanV710AdapterV18717
open GoldbachCircleMethodSharpSourceSincVariationV18721
open GoldbachCircleMethodActualMixedChannelRamanujanFactorizationV18727
open GoldbachCircleMethodActualCenteredQ3MassRecombinationV18731
open GoldbachCircleMethodActualQ3AbelProgressionSubstitutionV18734
open GoldbachCircleMethodActualQ3SplitPrefixBudgetV18735
open GoldbachCircleMethodActualCenteredSourcePrefixComplementBudgetV18736
open GoldbachCircleMethodExactLambdaPairSourceMeanSplitV18716

/-- Canonical full absolute mass of the actual centered source in one residue
class modulo three. -/
noncomputable def actualQ3CenteredClassAbsoluteMassBudget
    (M : Nat) (r : ZMod 3) : Real :=
  ∑ s ∈ Finset.range M.succ,
    if (s : ZMod 3) = r then
      ‖(centeredActualLambdaPairSource M s : Complex)‖
    else 0

/-- The canonical class budget is nonnegative. -/
theorem actualQ3CenteredClassAbsoluteMassBudget_nonneg
    (M : Nat) (r : ZMod 3) :
    0 ≤ actualQ3CenteredClassAbsoluteMassBudget M r := by
  unfold actualQ3CenteredClassAbsoluteMassBudget
  exact Finset.sum_nonneg fun s _hs => by
    by_cases h : (s : ZMod 3) = r <;> simp [h]

/-- Every actual progression-defect prefix is bounded by the full absolute
mass of its own residue class.  This is a finite triangle inequality, not a
distribution estimate. -/
theorem actualQ3ProgressionDefectPrefix_norm_le_classAbsoluteMassBudget
    (M : Nat) (r : ZMod 3) (k : Nat) (hk : k ≤ M.succ) :
    ‖actualQ3ProgressionDefectPrefix M r k‖ ≤
      actualQ3CenteredClassAbsoluteMassBudget M r := by
  rw [← q3ClassMass_centered_eq_actualProgressionDefectPrefix M r k]
  unfold q3ClassMass actualQ3CenteredClassAbsoluteMassBudget
  calc
    _ ≤ ∑ s ∈ Finset.range k,
        ‖if (s : ZMod 3) = r then
          (centeredActualLambdaPairSource M s : Complex) else 0‖ :=
      norm_sum_le _ _
    _ = ∑ s ∈ Finset.range k,
        if (s : ZMod 3) = r then
          ‖(centeredActualLambdaPairSource M s : Complex)‖ else 0 := by
      apply Finset.sum_congr rfl
      intro s _hs
      by_cases h : (s : ZMod 3) = r <;> simp [h]
    _ ≤ ∑ s ∈ Finset.range M.succ,
        if (s : ZMod 3) = r then
          ‖(centeredActualLambdaPairSource M s : Complex)‖ else 0 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hk)
      intro s _hs _hnot
      by_cases h : (s : ZMod 3) = r <;> simp [h]

/-- Canonical inhabitant of the reduced V1.8.736 envelope.  The carrier is
actual arithmetic data and cannot be supplied by the caller. -/
theorem actualQ3DefectPrefixEnvelope_sourceBound
    (M : Nat)
    (q : PairedOddBase (oddProjectRadius M))
    (n : Nat) :
    ActualQ3DefectPrefixEnvelope M q n
      (actualQ3CenteredClassAbsoluteMassBudget M (n : ZMod 3)) := by
  refine {
    defect_nonneg := actualQ3CenteredClassAbsoluteMassBudget_nonneg M (n : ZMod 3)
    defect_bound := ?_
  }
  intro k hk
  exact actualQ3ProgressionDefectPrefix_norm_le_classAbsoluteMassBudget
    M (n : ZMod 3) k hk

/-- Fully source-bound q=3 budget.  Its magnitude is not estimated here. -/
noncomputable def actualQ3FullySourceBoundUnitBudget
    (M : Nat)
    (q : PairedOddBase (oddProjectRadius M))
    (n : Nat) : Real :=
  actualQ3ComplementResolvedUnitBudget M
    (actualQ3CenteredClassAbsoluteMassBudget M (n : ZMod 3)) q n

/-- Unconditional finite bound for the negative q=3 channel.  It is
non-vacuous because the sole envelope is explicitly inhabited. -/
theorem selectedPairNegativeCenteredUnitAggregate_q3_norm_le_fullySourceBound
    {M : Nat} (hM : 0 < M)
    (q : PairedOddBase (oddProjectRadius M))
    (n : Nat) (hTarget : 2 * n ∈ evenTargetBlock M)
    (hq : q.val.val = 3) :
    ‖selectedPairNegativeCenteredUnitAggregate M q n‖ ≤
      actualQ3FullySourceBoundUnitBudget M q n := by
  exact selectedPairNegativeCenteredUnitAggregate_q3_norm_le_complementResolved
    hM q n hTarget hq (actualQ3DefectPrefixEnvelope_sourceBound M q n)

/-- Unconditional finite bound for the positive q=3 orientation. -/
theorem selectedPairPositiveCenteredUnitAggregate_q3_norm_le_fullySourceBound
    {M : Nat} (hM : 0 < M)
    (q : PairedOddBase (oddProjectRadius M))
    (n : Nat) (hTarget : 2 * n ∈ evenTargetBlock M)
    (hq : q.val.val = 3) :
    ‖selectedPairPositiveCenteredUnitAggregate M q n‖ ≤
      actualQ3FullySourceBoundUnitBudget M q n := by
  exact selectedPairPositiveCenteredUnitAggregate_q3_norm_le_complementResolved
    hM q n hTarget hq (actualQ3DefectPrefixEnvelope_sourceBound M q n)

end GoldbachCircleMethodActualQ3SourceBoundDefectEnvelopeV18737
