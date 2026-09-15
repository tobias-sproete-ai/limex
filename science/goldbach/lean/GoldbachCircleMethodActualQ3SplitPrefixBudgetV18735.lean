import GoldbachCircleMethodActualQ3AbelProgressionSubstitutionV18734

/-!
# V1.8.735: source-bound split prefix budget for the actual q=3 channel

V1.8.734 writes the actual denominator-three centered channel as the sum of
two exact Abel quantities: three times the arithmetic-progression defect and
the ordinary centered-source prefix correction.  This append-only module
keeps those two missing analytic inputs separate.

The declared envelope is local to one actual denominator-three channel.  It
does not pretend to bound every denominator, and no inhabitant is constructed.
The V1.8.721 endpoint and total-variation estimates are then reused literally.
The complete scalar prefix contributes no endpoint cost because V1.8.734
already proves that it is zero.

No progression-distribution estimate, no centered-source prefix estimate, no
minor-arc absorption, and no Goldbach conclusion is proved.
`proof_status = NO_PROOF`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

open scoped BigOperators Classical

namespace GoldbachCircleMethodActualQ3SplitPrefixBudgetV18735

open GoldbachCircleMethodTwoScaleEvenBlockDefectReserveV1833
open GoldbachCircleMethodOddChannelEventualAbsorptionV18658
open GoldbachCircleMethodFullDenominatorFourClassPartitionV18688
open GoldbachCircleMethodActualLambdaPairSourceMeanV710AdapterV18717
open GoldbachCircleMethodConstantChannelSourceVariationV18718
open GoldbachCircleMethodSharpSourceSincVariationV18721
open GoldbachCircleMethodActualMixedChannelRamanujanFactorizationV18727
open GoldbachCircleMethodActualQ3AbelProgressionSubstitutionV18734

/-- The two genuinely open prefix envelopes for one actual q=3 channel.
Neither field is inferred from a full-prefix identity. -/
structure ActualQ3SplitPrefixEnvelope
    (M : Nat)
    (q : PairedOddBase (oddProjectRadius M))
    (n : Nat)
    (D S : Real) : Prop where
  defect_nonneg : 0 ≤ D
  scalar_nonneg : 0 ≤ S
  defect_bound : ∀ k : Nat, k ≤ M.succ →
    ‖actualQ3ProgressionDefectPrefix M (n : ZMod 3) k‖ ≤ D
  scalar_bound : ∀ k : Nat, k ≤ M.succ →
    ‖actualCenteredSourcePrefix M k‖ ≤ S

/-- Exact V1.8.721 endpoint scale for the selected q=3 sinc weight. -/
noncomputable def actualQ3EndpointScale
    (M : Nat) (q : PairedOddBase (oddProjectRadius M)) : Real :=
  3 * (oddProjectWidth M : Real) /
    ((q.val.val : Real) * (M : Real))

/-- Exact V1.8.721 harmonic total-variation scale. -/
noncomputable def actualQ3VariationScale
    (M : Nat) (q : PairedOddBase (oddProjectRadius M)) : Real :=
  (12 * (oddProjectWidth M : Real) /
    ((q.val.val : Real) * (M : Real))) * (harmonic M : Real)

/-- The split budget preserves the factor three on the progression defect and
does not charge the vanishing complete scalar prefix an endpoint cost. -/
noncomputable def actualQ3SplitUnitBudget
    (M : Nat) (D S : Real)
    (q : PairedOddBase (oddProjectRadius M)) : Real :=
  3 * ((actualQ3EndpointScale M q + actualQ3VariationScale M q) * D) +
    actualQ3VariationScale M q * S

/-- The progression-defect Abel functional is bounded by its own prefix
envelope times the literal endpoint-plus-variation budget. -/
theorem actualQ3ProgressionDefectAbelFunctional_norm_le
    {M : Nat} {D S : Real} (hM : 0 < M)
    (q : PairedOddBase (oddProjectRadius M))
    (n : Nat) (hn : n ≤ M)
    (henv : ActualQ3SplitPrefixEnvelope M q n D S) :
    ‖actualQ3ProgressionDefectAbelFunctional M q n‖ ≤
      (actualQ3EndpointScale M q + actualQ3VariationScale M q) * D := by
  have hEnd := selectedPairSourceCoordinateSincWeight_terminal_norm_le
    M hM q n
  have hVar := sum_selectedPairSourceCoordinateSincVariation_norm_le_harmonic
    M hM q n hn
  have hEndScale : 0 ≤ actualQ3EndpointScale M q := by
    unfold actualQ3EndpointScale
    positivity
  have hVar' :
      (∑ a ∈ Finset.range M,
        ‖selectedPairSourceCoordinateSincVariation M q n a‖) ≤
        actualQ3VariationScale M q := by
    simpa only [actualQ3VariationScale] using hVar
  unfold actualQ3ProgressionDefectAbelFunctional
  calc
    _ ≤
        ‖selectedPairSourceCoordinateSincWeight M q n M *
          actualQ3ProgressionDefectPrefix M (n : ZMod 3) M.succ‖ +
        ‖∑ a ∈ Finset.range M,
          selectedPairSourceCoordinateSincVariation M q n a *
            actualQ3ProgressionDefectPrefix M (n : ZMod 3) (a + 1)‖ :=
      norm_sub_le _ _
    _ ≤
        actualQ3EndpointScale M q * D +
          ∑ a ∈ Finset.range M,
            ‖selectedPairSourceCoordinateSincVariation M q n a‖ * D := by
      apply add_le_add
      · rw [norm_mul]
        exact mul_le_mul hEnd (henv.defect_bound M.succ le_rfl)
          (norm_nonneg _) hEndScale
      · calc
          _ ≤ ∑ a ∈ Finset.range M,
              ‖selectedPairSourceCoordinateSincVariation M q n a *
                actualQ3ProgressionDefectPrefix M (n : ZMod 3) (a + 1)‖ :=
            norm_sum_le _ _
          _ ≤ ∑ a ∈ Finset.range M,
              ‖selectedPairSourceCoordinateSincVariation M q n a‖ * D := by
            apply Finset.sum_le_sum
            intro a ha
            rw [norm_mul]
            exact mul_le_mul_of_nonneg_left
              (henv.defect_bound (a + 1) (by
                have ha' := Finset.mem_range.mp ha
                omega)) (norm_nonneg _)
    _ = actualQ3EndpointScale M q * D +
        (∑ a ∈ Finset.range M,
          ‖selectedPairSourceCoordinateSincVariation M q n a‖) * D := by
      rw [Finset.sum_mul]
    _ ≤ actualQ3EndpointScale M q * D +
        actualQ3VariationScale M q * D := by
      exact add_le_add (le_refl _)
        (mul_le_mul_of_nonneg_right hVar' henv.defect_nonneg)
    _ = (actualQ3EndpointScale M q + actualQ3VariationScale M q) * D := by
      ring

/-- The scalar correction has only variation cost: its terminal prefix is
definitionally absent after the exact complete-prefix cancellation. -/
theorem actualCenteredScalarPrefixAbelCorrection_norm_le
    {M : Nat} {D S : Real} (hM : 0 < M)
    (q : PairedOddBase (oddProjectRadius M))
    (n : Nat) (hn : n ≤ M)
    (henv : ActualQ3SplitPrefixEnvelope M q n D S) :
    ‖actualCenteredScalarPrefixAbelCorrection M q n‖ ≤
      actualQ3VariationScale M q * S := by
  have hVar := sum_selectedPairSourceCoordinateSincVariation_norm_le_harmonic
    M hM q n hn
  unfold actualCenteredScalarPrefixAbelCorrection
  calc
    _ ≤ ∑ a ∈ Finset.range M,
        ‖selectedPairSourceCoordinateSincVariation M q n a *
          actualCenteredSourcePrefix M (a + 1)‖ := norm_sum_le _ _
    _ ≤ ∑ a ∈ Finset.range M,
        ‖selectedPairSourceCoordinateSincVariation M q n a‖ * S := by
      apply Finset.sum_le_sum
      intro a ha
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left
        (henv.scalar_bound (a + 1) (by
          have ha' := Finset.mem_range.mp ha
          omega)) (norm_nonneg _)
    _ = (∑ a ∈ Finset.range M,
        ‖selectedPairSourceCoordinateSincVariation M q n a‖) * S := by
      rw [Finset.sum_mul]
    _ ≤ actualQ3VariationScale M q * S :=
      mul_le_mul_of_nonneg_right hVar henv.scalar_nonneg

/-- Conditional norm bound for the literal negative q=3 centered aggregate.
The only analytic debt is visible in the two fields of `henv`. -/
theorem selectedPairNegativeCenteredUnitAggregate_q3_norm_le_splitBudget
    {M : Nat} {D S : Real} (hM : 0 < M)
    (q : PairedOddBase (oddProjectRadius M))
    (n : Nat) (hTarget : 2 * n ∈ evenTargetBlock M)
    (hq : q.val.val = 3)
    (henv : ActualQ3SplitPrefixEnvelope M q n D S) :
    ‖selectedPairNegativeCenteredUnitAggregate M q n‖ ≤
      actualQ3SplitUnitBudget M D S q := by
  have hn : n ≤ M := by
    have hUpper := ((mem_evenTargetBlock_iff M (2 * n)).mp hTarget).2.1
    omega
  rw [selectedPairNegativeCenteredUnitAggregate_q3_eq_defectAbel_add_scalarCorrection
    M q n hTarget hq]
  calc
    _ ≤ ‖3 * actualQ3ProgressionDefectAbelFunctional M q n‖ +
        ‖actualCenteredScalarPrefixAbelCorrection M q n‖ := norm_add_le _ _
    _ ≤ 3 * ((actualQ3EndpointScale M q + actualQ3VariationScale M q) * D) +
        actualQ3VariationScale M q * S := by
      apply add_le_add
      · calc
          ‖3 * actualQ3ProgressionDefectAbelFunctional M q n‖ =
              3 * ‖actualQ3ProgressionDefectAbelFunctional M q n‖ := by
            simp
          _ ≤ 3 * ((actualQ3EndpointScale M q +
              actualQ3VariationScale M q) * D) :=
            mul_le_mul_of_nonneg_left
              (actualQ3ProgressionDefectAbelFunctional_norm_le hM q n hn henv)
              (by norm_num)
      · exact actualCenteredScalarPrefixAbelCorrection_norm_le hM q n hn henv
    _ = actualQ3SplitUnitBudget M D S q := rfl

/-- The independently retained positive orientation obeys the identical split
budget only after the exact V1.8.734 sign bridge. -/
theorem selectedPairPositiveCenteredUnitAggregate_q3_norm_le_splitBudget
    {M : Nat} {D S : Real} (hM : 0 < M)
    (q : PairedOddBase (oddProjectRadius M))
    (n : Nat) (hTarget : 2 * n ∈ evenTargetBlock M)
    (hq : q.val.val = 3)
    (henv : ActualQ3SplitPrefixEnvelope M q n D S) :
    ‖selectedPairPositiveCenteredUnitAggregate M q n‖ ≤
      actualQ3SplitUnitBudget M D S q := by
  have hn : n ≤ M := by
    have hUpper := ((mem_evenTargetBlock_iff M (2 * n)).mp hTarget).2.1
    omega
  rw [selectedPairPositiveCenteredUnitAggregate_q3_eq_defectAbel_add_scalarCorrection
    M q n hTarget hq]
  calc
    _ ≤ ‖3 * actualQ3ProgressionDefectAbelFunctional M q n‖ +
        ‖actualCenteredScalarPrefixAbelCorrection M q n‖ := norm_add_le _ _
    _ ≤ 3 * ((actualQ3EndpointScale M q + actualQ3VariationScale M q) * D) +
        actualQ3VariationScale M q * S := by
      apply add_le_add
      · calc
          ‖3 * actualQ3ProgressionDefectAbelFunctional M q n‖ =
              3 * ‖actualQ3ProgressionDefectAbelFunctional M q n‖ := by
            simp
          _ ≤ 3 * ((actualQ3EndpointScale M q +
              actualQ3VariationScale M q) * D) :=
            mul_le_mul_of_nonneg_left
              (actualQ3ProgressionDefectAbelFunctional_norm_le hM q n hn henv)
              (by norm_num)
      · exact actualCenteredScalarPrefixAbelCorrection_norm_le hM q n hn henv
    _ = actualQ3SplitUnitBudget M D S q := rfl

end GoldbachCircleMethodActualQ3SplitPrefixBudgetV18735
