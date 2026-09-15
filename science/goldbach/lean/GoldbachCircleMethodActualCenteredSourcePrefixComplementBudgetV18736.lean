import GoldbachCircleMethodActualQ3SplitPrefixBudgetV18735

/-!
# V1.8.736: exact complement budget for the actual centered source prefix

V1.8.735 exposes two independent prefix envelopes in the actual denominator-
three Abel channel.  The ordinary centered-source envelope is not genuinely
free: V1.8.716 proves that the complete centered source has total mass zero.

This append-only module splits that exact complete sum at every prefix length.
Consequently, the norm of an incomplete prefix is bounded by the smaller of
the literal head and complementary-tail absolute-mass budgets.  Substitution
into the scalar Abel correction removes the caller-supplied scalar envelope
`S`; only the actual arithmetic-progression defect envelope remains open.

The resulting deterministic budget is not proved small.  No progression-
distribution estimate, minor-arc absorption, exceptional-set estimate, or
Goldbach conclusion is proved.  `proof_status = NO_PROOF`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

open scoped BigOperators Classical

namespace GoldbachCircleMethodActualCenteredSourcePrefixComplementBudgetV18736

open GoldbachCircleMethodTwoScaleEvenBlockDefectReserveV1833
open GoldbachCircleMethodOddChannelEventualAbsorptionV18658
open GoldbachCircleMethodFullDenominatorFourClassPartitionV18688
open GoldbachCircleMethodActualLambdaPairSourceMeanV710AdapterV18717
open GoldbachCircleMethodConstantChannelSourceVariationV18718
open GoldbachCircleMethodSharpSourceSincVariationV18721
open GoldbachCircleMethodActualMixedChannelRamanujanFactorizationV18727
open GoldbachCircleMethodActualQ3AbelProgressionSubstitutionV18734
open GoldbachCircleMethodActualQ3SplitPrefixBudgetV18735
open GoldbachCircleMethodExactLambdaPairSourceMeanSplitV18716

/-- Complementary tail of the definitionally fixed centered source. -/
noncomputable def actualCenteredSourceTail (M k : Nat) : Complex :=
  ∑ s ∈ Finset.Ico k M.succ,
    (centeredActualLambdaPairSource M s : Complex)

/-- The prefix and its complementary tail reconstruct the complete centered
source, whose exact total is zero. -/
theorem actualCenteredSourcePrefix_add_tail_eq_zero
    (M k : Nat) (hk : k ≤ M.succ) :
    actualCenteredSourcePrefix M k + actualCenteredSourceTail M k = 0 := by
  unfold actualCenteredSourcePrefix actualCenteredSourceTail
  rw [Finset.sum_range_add_sum_Ico _ hk]
  exact_mod_cast sum_centeredActualLambdaPairSource_eq_zero M

/-- Exact complement identity for every admissible prefix length. -/
theorem actualCenteredSourcePrefix_eq_neg_tail
    (M k : Nat) (hk : k ≤ M.succ) :
    actualCenteredSourcePrefix M k = -actualCenteredSourceTail M k := by
  have hzero := actualCenteredSourcePrefix_add_tail_eq_zero M k hk
  linear_combination hzero

/-- Taking norms preserves the exact prefix/complement symmetry. -/
theorem actualCenteredSourcePrefix_norm_eq_tail_norm
    (M k : Nat) (hk : k ≤ M.succ) :
    ‖actualCenteredSourcePrefix M k‖ = ‖actualCenteredSourceTail M k‖ := by
  rw [actualCenteredSourcePrefix_eq_neg_tail M k hk, norm_neg]

/-- Deterministic two-sided absolute-mass budget.  It is derived from the
actual source and is not a caller-selectable analytic hypothesis. -/
noncomputable def actualCenteredSourceTwoSidedMassBudget
    (M k : Nat) : Real :=
  min
    (∑ s ∈ Finset.range k,
      ‖(centeredActualLambdaPairSource M s : Complex)‖)
    (∑ s ∈ Finset.Ico k M.succ,
      ‖(centeredActualLambdaPairSource M s : Complex)‖)

/-- Every admissible centered-source prefix is controlled by the smaller of
its literal head and complementary-tail absolute masses. -/
theorem actualCenteredSourcePrefix_norm_le_twoSidedMassBudget
    (M k : Nat) (hk : k ≤ M.succ) :
    ‖actualCenteredSourcePrefix M k‖ ≤
      actualCenteredSourceTwoSidedMassBudget M k := by
  unfold actualCenteredSourceTwoSidedMassBudget
  apply le_min
  · unfold actualCenteredSourcePrefix
    exact norm_sum_le _ _
  · rw [actualCenteredSourcePrefix_norm_eq_tail_norm M k hk]
    unfold actualCenteredSourceTail
    exact norm_sum_le _ _

/-- The scalar Abel correction is now bounded by a fully deterministic finite
quantity; no free scalar-prefix envelope remains. -/
theorem actualCenteredScalarPrefixAbelCorrection_norm_le_complementBudget
    {M : Nat} (q : PairedOddBase (oddProjectRadius M))
    (n : Nat) :
    ‖actualCenteredScalarPrefixAbelCorrection M q n‖ ≤
      ∑ a ∈ Finset.range M,
        ‖selectedPairSourceCoordinateSincVariation M q n a‖ *
          actualCenteredSourceTwoSidedMassBudget M (a + 1) := by
  unfold actualCenteredScalarPrefixAbelCorrection
  calc
    _ ≤ ∑ a ∈ Finset.range M,
        ‖selectedPairSourceCoordinateSincVariation M q n a *
          actualCenteredSourcePrefix M (a + 1)‖ := norm_sum_le _ _
    _ = ∑ a ∈ Finset.range M,
        ‖selectedPairSourceCoordinateSincVariation M q n a‖ *
          ‖actualCenteredSourcePrefix M (a + 1)‖ := by
      apply Finset.sum_congr rfl
      intro a _ha
      rw [norm_mul]
    _ ≤ ∑ a ∈ Finset.range M,
        ‖selectedPairSourceCoordinateSincVariation M q n a‖ *
          actualCenteredSourceTwoSidedMassBudget M (a + 1) := by
      apply Finset.sum_le_sum
      intro a ha
      apply mul_le_mul_of_nonneg_left
      · apply actualCenteredSourcePrefix_norm_le_twoSidedMassBudget
        have ha' := Finset.mem_range.mp ha
        omega
      · exact norm_nonneg _

/-- Only the genuinely arithmetic q=3 progression-defect prefix remains as a
free analytic envelope after the exact scalar complement reduction. -/
structure ActualQ3DefectPrefixEnvelope
    (M : Nat)
    (q : PairedOddBase (oddProjectRadius M))
    (n : Nat)
    (D : Real) : Prop where
  defect_nonneg : 0 ≤ D
  defect_bound : ∀ k : Nat, k ≤ M.succ →
    ‖actualQ3ProgressionDefectPrefix M (n : ZMod 3) k‖ ≤ D

/-- Source-bound q=3 budget after eliminating the free scalar envelope. -/
noncomputable def actualQ3ComplementResolvedUnitBudget
    (M : Nat) (D : Real)
    (q : PairedOddBase (oddProjectRadius M))
    (n : Nat) : Real :=
  3 * ((actualQ3EndpointScale M q + actualQ3VariationScale M q) * D) +
    ∑ a ∈ Finset.range M,
      ‖selectedPairSourceCoordinateSincVariation M q n a‖ *
        actualCenteredSourceTwoSidedMassBudget M (a + 1)

/-- The progression-defect Abel functional only needs the reduced envelope. -/
theorem actualQ3ProgressionDefectAbelFunctional_norm_le_reduced
    {M : Nat} {D : Real} (hM : 0 < M)
    (q : PairedOddBase (oddProjectRadius M))
    (n : Nat) (hn : n ≤ M)
    (henv : ActualQ3DefectPrefixEnvelope M q n D) :
    ‖actualQ3ProgressionDefectAbelFunctional M q n‖ ≤
      (actualQ3EndpointScale M q + actualQ3VariationScale M q) * D := by
  let hsplit : ActualQ3SplitPrefixEnvelope M q n D
      (∑ s ∈ Finset.range M.succ,
        ‖(centeredActualLambdaPairSource M s : Complex)‖) := {
    defect_nonneg := henv.defect_nonneg
    scalar_nonneg := Finset.sum_nonneg fun _ _ => norm_nonneg _
    defect_bound := henv.defect_bound
    scalar_bound := by
      intro k hk
      unfold actualCenteredSourcePrefix
      exact (norm_sum_le _ _).trans
        (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hk)
          (fun _ _ _ => norm_nonneg _))
  }
  exact actualQ3ProgressionDefectAbelFunctional_norm_le hM q n hn hsplit

/-- Conditional bound for the actual negative q=3 channel with only the
progression-defect envelope open. -/
theorem selectedPairNegativeCenteredUnitAggregate_q3_norm_le_complementResolved
    {M : Nat} {D : Real} (hM : 0 < M)
    (q : PairedOddBase (oddProjectRadius M))
    (n : Nat) (hTarget : 2 * n ∈ evenTargetBlock M)
    (hq : q.val.val = 3)
    (henv : ActualQ3DefectPrefixEnvelope M q n D) :
    ‖selectedPairNegativeCenteredUnitAggregate M q n‖ ≤
      actualQ3ComplementResolvedUnitBudget M D q n := by
  have hn : n ≤ M := by
    have hUpper := ((mem_evenTargetBlock_iff M (2 * n)).mp hTarget).2.1
    omega
  rw [selectedPairNegativeCenteredUnitAggregate_q3_eq_defectAbel_add_scalarCorrection
    M q n hTarget hq]
  calc
    _ ≤ ‖3 * actualQ3ProgressionDefectAbelFunctional M q n‖ +
        ‖actualCenteredScalarPrefixAbelCorrection M q n‖ := norm_add_le _ _
    _ ≤ 3 * ((actualQ3EndpointScale M q + actualQ3VariationScale M q) * D) +
        ∑ a ∈ Finset.range M,
          ‖selectedPairSourceCoordinateSincVariation M q n a‖ *
            actualCenteredSourceTwoSidedMassBudget M (a + 1) := by
      apply add_le_add
      · calc
          ‖3 * actualQ3ProgressionDefectAbelFunctional M q n‖ =
              3 * ‖actualQ3ProgressionDefectAbelFunctional M q n‖ := by simp
          _ ≤ 3 * ((actualQ3EndpointScale M q +
              actualQ3VariationScale M q) * D) :=
            mul_le_mul_of_nonneg_left
              (actualQ3ProgressionDefectAbelFunctional_norm_le_reduced
                hM q n hn henv) (by norm_num)
      · exact actualCenteredScalarPrefixAbelCorrection_norm_le_complementBudget q n
    _ = actualQ3ComplementResolvedUnitBudget M D q n := rfl

/-- The exact sign bridge gives the same reduced budget to the retained
positive orientation. -/
theorem selectedPairPositiveCenteredUnitAggregate_q3_norm_le_complementResolved
    {M : Nat} {D : Real} (hM : 0 < M)
    (q : PairedOddBase (oddProjectRadius M))
    (n : Nat) (hTarget : 2 * n ∈ evenTargetBlock M)
    (hq : q.val.val = 3)
    (henv : ActualQ3DefectPrefixEnvelope M q n D) :
    ‖selectedPairPositiveCenteredUnitAggregate M q n‖ ≤
      actualQ3ComplementResolvedUnitBudget M D q n := by
  have hn : n ≤ M := by
    have hUpper := ((mem_evenTargetBlock_iff M (2 * n)).mp hTarget).2.1
    omega
  rw [selectedPairPositiveCenteredUnitAggregate_q3_eq_defectAbel_add_scalarCorrection
    M q n hTarget hq]
  calc
    _ ≤ ‖3 * actualQ3ProgressionDefectAbelFunctional M q n‖ +
        ‖actualCenteredScalarPrefixAbelCorrection M q n‖ := norm_add_le _ _
    _ ≤ 3 * ((actualQ3EndpointScale M q + actualQ3VariationScale M q) * D) +
        ∑ a ∈ Finset.range M,
          ‖selectedPairSourceCoordinateSincVariation M q n a‖ *
            actualCenteredSourceTwoSidedMassBudget M (a + 1) := by
      apply add_le_add
      · calc
          ‖3 * actualQ3ProgressionDefectAbelFunctional M q n‖ =
              3 * ‖actualQ3ProgressionDefectAbelFunctional M q n‖ := by simp
          _ ≤ 3 * ((actualQ3EndpointScale M q +
              actualQ3VariationScale M q) * D) :=
            mul_le_mul_of_nonneg_left
              (actualQ3ProgressionDefectAbelFunctional_norm_le_reduced
                hM q n hn henv) (by norm_num)
      · exact actualCenteredScalarPrefixAbelCorrection_norm_le_complementBudget q n
    _ = actualQ3ComplementResolvedUnitBudget M D q n := rfl

end GoldbachCircleMethodActualCenteredSourcePrefixComplementBudgetV18736
