import GoldbachCircleMethodActualQ3UnitModeSquareBudgetV18744
import GoldbachCircleMethodActualCompanionIntervalTransferV18205
import GoldbachCircleMethodCoupledSecondMarginalPairwisePeriodV18383

/-!
# V1.8.745: periodic mean removal and spectral q=3 endpoint budget

The complete q=3 endpoint from V1.8.744 contains a raw pair mode and the
constant channel introduced by exact source centering.  This append-only
module bounds the latter by one incomplete period: the denominator-three
Ramanujan prefix has norm at most four, uniformly in the target and prefix
length.  The endpoint sign debit is therefore controlled by the two genuine
nonzero odd-Lambda mode squares plus an explicit linear mean correction.

This is a strict improvement in information type over the rejected total-
mass envelope: the quadratic term now contains only nonzero additive Fourier
modes.  Their arithmetic smallness is not proved here.  No incomplete source-
weighted prefix bound, minor-arc absorption, exceptional-set result, or
Goldbach conclusion is asserted.  `proof_status = NO_PROOF`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

open scoped BigOperators Classical ArithmeticFunction.vonMangoldt

namespace GoldbachCircleMethodActualQ3EndpointSpectralBudgetV18745

open GoldbachCircleMethodFiniteResiduePrefixV1866
open GoldbachCircleMethodActualCompanionPeriodicLiftV18202
open GoldbachCircleMethodActualCompanionIntervalTransferV18205
open GoldbachCircleMethodCoupledSecondMarginalPairwisePeriodV18383
open GoldbachCircleMethodActualCenteredQ3ResidueObstructionV18730
open GoldbachCircleMethodActualQ3WeightedFiberPullbackV18742
open GoldbachCircleMethodActualQ3PairFourierFactorizationV18743
open GoldbachCircleMethodActualQ3UnitModeSquareBudgetV18744
open GoldbachCircleMethodActualQ3SourceBudgetScaleAuditV18738
open GoldbachCircleMethodExactLambdaPairSourceMeanSplitV18716
open GoldbachCircleMethodActualQ3SignPrefixFluctuationProjectReserveV18740
open GoldbachCircleMethodActualQ3LocalDensitySignedReserveV18739
open GoldbachCircleMethodActualLambdaPairSourceMeanV710AdapterV18717
open GoldbachCircleMethodOddChannelEventualAbsorptionV18658
open GoldbachCircleMethodFullDenominatorFourClassPartitionV18688

/-- In characteristic three, the original integer-difference q=3 phase is
the forward even-step residue phase with start `n`. -/
theorem q3DifferencePhase_eq_forwardPhase (n s : Nat) :
    (((2 * ((s : Int) - (n : Int)) : Int) : ZMod 3)) =
      ((n + 2 * s : Nat) : ZMod 3) := by
  push_cast
  have hminusTwo : (-2 : ZMod 3) = 1 := by decide
  calc
    (2 : ZMod 3) * ((s : ZMod 3) - (n : ZMod 3)) =
        (2 : ZMod 3) * (s : ZMod 3) +
          (-2 : ZMod 3) * (n : ZMod 3) := by ring
    _ = (2 : ZMod 3) * (s : ZMod 3) + (n : ZMod 3) := by
      rw [hminusTwo, one_mul]
    _ = (n : ZMod 3) + (2 : ZMod 3) * (s : ZMod 3) := by ring

/-- Pointwise q=3 Ramanujan norm bound. -/
theorem unitCharacterSum_three_norm_le_two (x : ZMod 3) :
    ‖@unitCharacterSum 3 ⟨by norm_num⟩ x‖ ≤ 2 := by
  rw [unitCharacterSum_three_eq_if_zero]
  by_cases hx : x = 0
  · simp only [hx, if_true]
    norm_num
  · simp only [hx, if_false]
    norm_num

/-- The forward even-step q=3 atom has zero complete-period sum. -/
theorem q3ForwardAtom_complete_sum_zero (n : Nat) :
    (∑ x : ZMod 3,
      @unitCharacterSum 3 ⟨by norm_num⟩
        ((n : ZMod 3) + (2 : ZMod 3) * x)) = 0 := by
  rw [← sum_range_residues_complex 3 (fun x : ZMod 3 =>
    @unitCharacterSum 3 ⟨by norm_num⟩
      ((n : ZMod 3) + (2 : ZMod 3) * x))]
  simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using
    even_step_unitCharacterSum_complete_period_eq_zero 3 (by norm_num) n

/-- Every constant q=3 prefix consists of complete zero periods and at most
two residual terms, hence has uniform norm at most four. -/
theorem q3ConstantPrefix_norm_le_four (n k : Nat) :
    ‖q3ConstantPrefix n k‖ ≤ 4 := by
  have hdecomp := residue_interval_decomposition
    (fun x : ZMod 3 =>
      @unitCharacterSum 3 ⟨by norm_num⟩
        ((n : ZMod 3) + (2 : ZMod 3) * x)) 0 k
  rw [q3ForwardAtom_complete_sum_zero n, mul_zero, zero_add] at hdecomp
  unfold q3ConstantPrefix q3EvenStepTransform
  simp_rw [q3DifferencePhase_eq_forwardPhase]
  simp only [one_mul]
  have hresidue :
      (∑ x ∈ Finset.range k,
        @unitCharacterSum 3 ⟨by norm_num⟩
          ((n + 2 * x : Nat) : ZMod 3)) =
      ∑ i ∈ Finset.range (k % 3),
        @unitCharacterSum 3 ⟨by norm_num⟩
          ((n : ZMod 3) + (2 : ZMod 3) * (i : ZMod 3)) := by
    simpa only [zero_add, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using hdecomp
  rw [hresidue]
  calc
    _ ≤ ∑ i ∈ Finset.range (k % 3),
        ‖@unitCharacterSum 3 ⟨by norm_num⟩
          ((n : ZMod 3) + (2 : ZMod 3) * (i : ZMod 3))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _i ∈ Finset.range (k % 3), (2 : Real) := by
      apply Finset.sum_le_sum
      intro i _hi
      exact unitCharacterSum_three_norm_le_two
        ((n : ZMod 3) + (2 : ZMod 3) * (i : ZMod 3))
    _ = (k % 3 : Nat) * (2 : Real) := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ ≤ 4 := by
      have hmod : k % 3 ≤ 2 := by
        have hlt := Nat.mod_lt k (by norm_num : 0 < 3)
        omega
      exact_mod_cast (Nat.mul_le_mul_right 2 hmod)

/-- Endpoint budget after exact replacement of total source mass by the two
nonzero q=3 mode squares and the finite constant-prefix remainder. -/
noncomputable def actualQ3EndpointSpectralBudget
    (M : Nat)
    (q : PairedOddBase (oddProjectRadius M))
    (n : Nat) : Real :=
  ‖selectedPairSourceCoordinateSincWeight M q n M‖ *
    (actualQ3UnitModeSquareBudget M + 4 * actualLambdaPairSourceMean M)

theorem actualQ3EndpointSpectralBudget_nonneg
    (M : Nat)
    (q : PairedOddBase (oddProjectRadius M))
    (n : Nat) :
    0 ≤ actualQ3EndpointSpectralBudget M q n := by
  unfold actualQ3EndpointSpectralBudget
  have hMean : 0 ≤ actualLambdaPairSourceMean M :=
    actualLambdaPairSourceMean_nonneg_local M
  exact mul_nonneg (norm_nonneg _)
    (add_nonneg (actualQ3UnitModeSquareBudget_nonneg M)
      (mul_nonneg (by norm_num) hMean))

/-- The literal q=3 local-density endpoint obeys the spectral budget. -/
theorem actualQ3LocalDensityMainTerm_norm_le_endpointSpectralBudget
    (M : Nat)
    (q : PairedOddBase (oddProjectRadius M))
    (n : Nat)
    (hq : q.val.val = 3) :
    ‖actualQ3LocalDensityMainTerm M q n‖ ≤
      actualQ3EndpointSpectralBudget M q n := by
  rw [actualQ3LocalDensityMainTerm_eq_weight_mul_pairTransform_sub_meanConstant
    M q n hq]
  unfold actualQ3EndpointSpectralBudget
  rw [norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  calc
    ‖actualQ3RawPairTransform M n -
        (actualLambdaPairSourceMean M : Complex) *
          q3ConstantPrefix n M.succ‖ ≤
      ‖actualQ3RawPairTransform M n‖ +
        ‖(actualLambdaPairSourceMean M : Complex) *
          q3ConstantPrefix n M.succ‖ := norm_sub_le _ _
    _ = ‖actualQ3RawPairTransform M n‖ +
        ‖(actualLambdaPairSourceMean M : Complex)‖ *
          ‖q3ConstantPrefix n M.succ‖ := by rw [norm_mul]
    _ ≤ actualQ3UnitModeSquareBudget M +
        actualLambdaPairSourceMean M * 4 := by
      apply add_le_add
      · exact actualQ3RawPairTransform_norm_le_unitModeSquareBudget M n
      · rw [Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (actualLambdaPairSourceMean_nonneg_local M)]
        exact mul_le_mul_of_nonneg_left
          (q3ConstantPrefix_norm_le_four n M.succ)
          (actualLambdaPairSourceMean_nonneg_local M)
    _ = actualQ3UnitModeSquareBudget M +
        4 * actualLambdaPairSourceMean M := by ring

/-- In particular, the literal sign debit is controlled by the same spectral
budget. -/
theorem actualQ3LocalDensitySignDebit_le_endpointSpectralBudget
    (M : Nat)
    (q : PairedOddBase (oddProjectRadius M))
    (n : Nat)
    (hq : q.val.val = 3) :
    actualQ3LocalDensitySignDebit M q n ≤
      actualQ3EndpointSpectralBudget M q n := by
  have hNorm := actualQ3LocalDensityMainTerm_norm_le_endpointSpectralBudget
    M q n hq
  unfold actualQ3LocalDensitySignDebit
  apply max_le
  · exact actualQ3EndpointSpectralBudget_nonneg M q n
  · have hAbsNeg :
        |-(actualQ3LocalDensityMainTerm M q n).re| ≤
          ‖actualQ3LocalDensityMainTerm M q n‖ := by
        simpa only [abs_neg] using
          (Complex.abs_re_le_norm (actualQ3LocalDensityMainTerm M q n))
    exact (le_of_abs_le hAbsNeg).trans hNorm

end GoldbachCircleMethodActualQ3EndpointSpectralBudgetV18745
