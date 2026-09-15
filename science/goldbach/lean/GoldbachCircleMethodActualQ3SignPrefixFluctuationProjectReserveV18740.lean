import GoldbachCircleMethodActualQ3LocalDensitySignedReserveV18739

/-!
# V1.8.740: actual q=3 sign, prefix fluctuation, and project-reserve binding

V1.8.739 extracts the exact complete-prefix endpoint of the actual denominator-
three Abel identity but deliberately leaves its sign and the size of the
remaining prefix fluctuation open.  This append-only successor closes the
*binding* problem without inventing a favorable sign.

The local-density endpoint is charged by its literal negative part
`max 0 (-re endpoint)`.  The progression-prefix and scalar-prefix fluctuations
are bounded by deterministic finite quantities derived from the actual centered
Lambda-pair source.  Their sum is then compared with the already kernelized
project reserve `M / 14`.  The final theorem connects this exact debit test to
the concrete discrete project main term at the cubic scale.

The debit inequality itself is not proved.  In particular, no pointwise
progression-distribution estimate, minor-arc absorption, exceptional-set bound,
or Goldbach conclusion is asserted.  `proof_status = NO_PROOF`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

open scoped BigOperators Classical

namespace GoldbachCircleMethodActualQ3SignPrefixFluctuationProjectReserveV18740

open GoldbachCircleMethodTwoScaleEvenBlockDefectReserveV1833
open GoldbachCircleMethodOddChannelEventualAbsorptionV18658
open GoldbachCircleMethodUniformModelReserveCubicScaleV18639
open GoldbachCircleMethodDiscreteArcModelReserveV1855
open GoldbachCircleMethodFullDenominatorFourClassPartitionV18688
open GoldbachCircleMethodExactLambdaPairSourceMeanSplitV18716
open GoldbachCircleMethodActualLambdaPairSourceMeanV710AdapterV18717
open GoldbachCircleMethodSharpSourceSincVariationV18721
open GoldbachCircleMethodActualMixedChannelRamanujanFactorizationV18727
open GoldbachCircleMethodActualQ3AbelProgressionSubstitutionV18734
open GoldbachCircleMethodActualQ3SplitPrefixBudgetV18735
open GoldbachCircleMethodActualCenteredSourcePrefixComplementBudgetV18736
open GoldbachCircleMethodActualQ3SourceBoundDefectEnvelopeV18737
open GoldbachCircleMethodActualQ3LocalDensitySignedReserveV18739

/-- Deterministic finite budget for the fluctuation left after the exact q=3
endpoint is extracted.  Both prefix factors come from the actual centered
Lambda-pair source; no caller-selected envelope remains. -/
noncomputable def actualQ3SourceBoundPrefixFluctuationBudget
    (M : Nat)
    (q : PairedOddBase (oddProjectRadius M))
    (n : Nat) : Real :=
  3 * actualQ3VariationScale M q *
      actualQ3CenteredClassAbsoluteMassBudget M (n : ZMod 3) +
    ∑ a ∈ Finset.range M,
      ‖selectedPairSourceCoordinateSincVariation M q n a‖ *
        actualCenteredSourceTwoSidedMassBudget M (a + 1)

theorem actualQ3SourceBoundPrefixFluctuationBudget_nonneg
    (M : Nat)
    (q : PairedOddBase (oddProjectRadius M))
    (n : Nat) :
    0 ≤ actualQ3SourceBoundPrefixFluctuationBudget M q n := by
  unfold actualQ3SourceBoundPrefixFluctuationBudget
  have hHarmonic : 0 ≤ (harmonic M : Real) := by
    rw [real_harmonic_eq_sum]
    exact Finset.sum_nonneg fun _ _ => by positivity
  have hVar : 0 ≤ actualQ3VariationScale M q := by
    unfold actualQ3VariationScale
    exact mul_nonneg (div_nonneg (by positivity) (by positivity)) hHarmonic
  have hClass :
      0 ≤ actualQ3CenteredClassAbsoluteMassBudget M (n : ZMod 3) :=
    actualQ3CenteredClassAbsoluteMassBudget_nonneg M (n : ZMod 3)
  have hSum :
      0 ≤ ∑ a ∈ Finset.range M,
        ‖selectedPairSourceCoordinateSincVariation M q n a‖ *
          actualCenteredSourceTwoSidedMassBudget M (a + 1) := by
    apply Finset.sum_nonneg
    intro a _ha
    apply mul_nonneg (norm_nonneg _)
    unfold actualCenteredSourceTwoSidedMassBudget
    apply le_min
    · exact Finset.sum_nonneg fun _ _ => norm_nonneg _
    · exact Finset.sum_nonneg fun _ _ => norm_nonneg _
  positivity

/-- The actual q=3 fluctuation is bounded unconditionally by the deterministic
source-derived prefix budget.  This is a finite triangle estimate, not a
claim that the budget is asymptotically small. -/
theorem actualQ3SignedFluctuationRemainder_norm_le_sourceBoundPrefixBudget
    {M : Nat} (hM : 0 < M)
    (q : PairedOddBase (oddProjectRadius M))
    (n : Nat) (hn : n ≤ M) :
    ‖actualQ3SignedFluctuationRemainder M q n‖ ≤
      actualQ3SourceBoundPrefixFluctuationBudget M q n := by
  let D : Real :=
    actualQ3CenteredClassAbsoluteMassBudget M (n : ZMod 3)
  let S : Real :=
    ∑ s ∈ Finset.range M.succ,
      ‖(centeredActualLambdaPairSource M s : Complex)‖
  have henv : ActualQ3SplitPrefixEnvelope M q n D S := {
    defect_nonneg := actualQ3CenteredClassAbsoluteMassBudget_nonneg
      M (n : ZMod 3)
    scalar_nonneg := Finset.sum_nonneg fun _ _ => norm_nonneg _
    defect_bound := by
      intro k hk
      exact actualQ3ProgressionDefectPrefix_norm_le_classAbsoluteMassBudget
        M (n : ZMod 3) k hk
    scalar_bound := by
      intro k hk
      unfold actualCenteredSourcePrefix
      exact (norm_sum_le _ _).trans
        (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hk)
          (fun _ _ _ => norm_nonneg _))
  }
  have hProgression := actualQ3ProgressionVariationRemainder_norm_le
    hM q n hn henv
  have hScalar :=
    actualCenteredScalarPrefixAbelCorrection_norm_le_complementBudget q n
  unfold actualQ3SignedFluctuationRemainder
    actualQ3SourceBoundPrefixFluctuationBudget
  calc
    _ ≤ ‖-(3 * actualQ3ProgressionVariationRemainder M q n)‖ +
        ‖actualCenteredScalarPrefixAbelCorrection M q n‖ := norm_add_le _ _
    _ = 3 * ‖actualQ3ProgressionVariationRemainder M q n‖ +
        ‖actualCenteredScalarPrefixAbelCorrection M q n‖ := by simp
    _ ≤ 3 * (actualQ3VariationScale M q * D) +
        ∑ a ∈ Finset.range M,
          ‖selectedPairSourceCoordinateSincVariation M q n a‖ *
            actualCenteredSourceTwoSidedMassBudget M (a + 1) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left hProgression (by norm_num)) hScalar
    _ = 3 * actualQ3VariationScale M q *
          actualQ3CenteredClassAbsoluteMassBudget M (n : ZMod 3) +
        ∑ a ∈ Finset.range M,
          ‖selectedPairSourceCoordinateSincVariation M q n a‖ *
            actualCenteredSourceTwoSidedMassBudget M (a + 1) := by
      dsimp [D]
      ring

/-- Literal negative part of the exact local-density endpoint.  This prevents
the global mean-zero identity from being misreported as pointwise positivity. -/
noncomputable def actualQ3LocalDensitySignDebit
    (M : Nat)
    (q : PairedOddBase (oddProjectRadius M))
    (n : Nat) : Real :=
  max 0 (-(actualQ3LocalDensityMainTerm M q n).re)

theorem actualQ3LocalDensitySignDebit_nonneg
    (M : Nat)
    (q : PairedOddBase (oddProjectRadius M))
    (n : Nat) :
    0 ≤ actualQ3LocalDensitySignDebit M q n := by
  unfold actualQ3LocalDensitySignDebit
  exact le_max_left _ _

/-- Charging the exact negative part makes the signed endpoint nonnegative,
without any unproved local-density sign assumption. -/
theorem localDensityMainTerm_re_add_signDebit_nonneg
    (M : Nat)
    (q : PairedOddBase (oddProjectRadius M))
    (n : Nat) :
    0 ≤ (actualQ3LocalDensityMainTerm M q n).re +
      actualQ3LocalDensitySignDebit M q n := by
  unfold actualQ3LocalDensitySignDebit
  have h := le_max_right 0 (-(actualQ3LocalDensityMainTerm M q n).re)
  linarith

/-- Exact project reserve used throughout the existing exceptional-set chain. -/
noncomputable def actualQ3ProjectSignedReserve
    (M : Nat)
    (q : PairedOddBase (oddProjectRadius M))
    (n : Nat) : Real :=
  (M : Real) / 14 + (actualQ3LocalDensityMainTerm M q n).re

/-- Conservative project reserve after paying the literal local sign debit. -/
noncomputable def actualQ3ProjectReserveAfterSign
    (M : Nat)
    (q : PairedOddBase (oddProjectRadius M))
    (n : Nat) : Real :=
  (M : Real) / 14 - actualQ3LocalDensitySignDebit M q n

/-- Total deterministic q=3 debit against the concrete project reserve. -/
noncomputable def actualQ3ProjectDebit
    (M : Nat)
    (q : PairedOddBase (oddProjectRadius M))
    (n : Nat) : Real :=
  actualQ3LocalDensitySignDebit M q n +
    actualQ3SourceBoundPrefixFluctuationBudget M q n

theorem actualQ3ProjectSignedReserve_eq_existingSignedReserve
    (M : Nat)
    (q : PairedOddBase (oddProjectRadius M))
    (n : Nat) :
    actualQ3ProjectSignedReserve M q n =
      actualQ3SignedReserve ((M : Real) / 14) M q n := by
  rfl

/-- The sign-debited reserve is a sound lower bound for the exact signed
project reserve. -/
theorem actualQ3ProjectReserveAfterSign_le_signedReserve
    (M : Nat)
    (q : PairedOddBase (oddProjectRadius M))
    (n : Nat) :
    actualQ3ProjectReserveAfterSign M q n ≤
      actualQ3ProjectSignedReserve M q n := by
  have h := localDensityMainTerm_re_add_signDebit_nonneg M q n
  unfold actualQ3ProjectReserveAfterSign actualQ3ProjectSignedReserve
  linarith

/-- The single project-debit test is exactly the prefix-budget test against
the reserve remaining after the local sign is paid. -/
theorem projectDebit_lt_one_fourteenth_iff_prefixBudget_lt_reserveAfterSign
    (M : Nat)
    (q : PairedOddBase (oddProjectRadius M))
    (n : Nat) :
    actualQ3ProjectDebit M q n < (M : Real) / 14 ↔
      actualQ3SourceBoundPrefixFluctuationBudget M q n <
        actualQ3ProjectReserveAfterSign M q n := by
  unfold actualQ3ProjectDebit actualQ3ProjectReserveAfterSign
  constructor <;> intro h <;> linarith

/-- Exact negative-orientation composition at the project reserve `M/14`. -/
theorem projectReserve_add_negativeAggregate_re_eq_signedReserve_add_fluctuation_re
    (M : Nat)
    (q : PairedOddBase (oddProjectRadius M))
    (n : Nat)
    (hTarget : 2 * n ∈ evenTargetBlock M)
    (hq : q.val.val = 3) :
    (M : Real) / 14 +
        (selectedPairNegativeCenteredUnitAggregate M q n).re =
      actualQ3ProjectSignedReserve M q n +
        (actualQ3SignedFluctuationRemainder M q n).re := by
  simpa only [actualQ3ProjectSignedReserve_eq_existingSignedReserve] using
    baseReserve_add_negativeAggregate_re_eq_signedReserve_add_fluctuation_re
      ((M : Real) / 14) M q n hTarget hq

/-- Once the deterministic sign-plus-prefix debit fits below `M/14`, the
project reserve plus the actual negative q=3 channel is strictly positive. -/
theorem projectReserve_add_negativeAggregate_re_pos_of_projectDebit
    {M : Nat} (hM : 0 < M)
    (q : PairedOddBase (oddProjectRadius M))
    (n : Nat) (hTarget : 2 * n ∈ evenTargetBlock M)
    (hq : q.val.val = 3)
    (hDebit : actualQ3ProjectDebit M q n < (M : Real) / 14) :
    0 < (M : Real) / 14 +
      (selectedPairNegativeCenteredUnitAggregate M q n).re := by
  have hn : n ≤ M := by
    have hUpper := ((mem_evenTargetBlock_iff M (2 * n)).mp hTarget).2.1
    omega
  have hFluct :=
    actualQ3SignedFluctuationRemainder_norm_le_sourceBoundPrefixBudget
      hM q n hn
  have hAbs :
      |(actualQ3SignedFluctuationRemainder M q n).re| ≤
        ‖actualQ3SignedFluctuationRemainder M q n‖ :=
    Complex.abs_re_le_norm _
  have hFluctLower :
      -actualQ3SourceBoundPrefixFluctuationBudget M q n ≤
        (actualQ3SignedFluctuationRemainder M q n).re := by
    have hNegNorm :
        -‖actualQ3SignedFluctuationRemainder M q n‖ ≤
          (actualQ3SignedFluctuationRemainder M q n).re :=
      neg_le_of_abs_le hAbs
    linarith
  have hSign := localDensityMainTerm_re_add_signDebit_nonneg M q n
  rw [projectReserve_add_negativeAggregate_re_eq_signedReserve_add_fluctuation_re
    M q n hTarget hq]
  unfold actualQ3ProjectDebit at hDebit
  unfold actualQ3ProjectSignedReserve
  linarith

/-- Direct binding to the already kernelized discrete project main term at
the cubic scale.  The only remaining premise is the explicit deterministic
q=3 debit inequality. -/
theorem discreteProjectMain_add_negativeAggregate_re_pos_of_projectDebit
    {M R : Nat} (hM : 32 ≤ M) (hR : 1 ≤ R)
    (hcubic : 16 * R ^ 3 < M)
    (q : PairedOddBase (oddProjectRadius M))
    (n : Nat) (hTarget : 2 * n ∈ evenTargetBlock M)
    (hq : q.val.val = 3)
    (hDebit : actualQ3ProjectDebit M q n < (M : Real) / 14) :
    0 < discreteArcMainModel M (2 * n) R (cubicModelScale R) +
      (selectedPairNegativeCenteredUnitAggregate M q n).re := by
  have hModel := uniform_discrete_model_reserve_cubic_scale
    M R hM hR hcubic (2 * n) hTarget
  have hPositive := projectReserve_add_negativeAggregate_re_pos_of_projectDebit
    (M := M) (by omega) q n hTarget hq hDebit
  linarith

end GoldbachCircleMethodActualQ3SignPrefixFluctuationProjectReserveV18740
