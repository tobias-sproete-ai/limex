import GoldbachCircleMethodDiscreteModelExceptionDetectorV18632

/-!
# V1.8.635: quantitative discrete-model exception-count transfer

V1.8.632 showed that one Goldbach exception in the fixed even block forces
at least `M / 28` of positive discrete-model overshoot.  This module keeps
the same model and turns that pointwise forcing statement into the exact
finite second-moment counting inequality

`#exceptions * (M / 28)^2 <= modelOvershootSquaredMoment`.

Thus any independently proved moment budget gives a corresponding
exceptional-set bound.  No moment estimate, model reserve, or Goldbach
theorem is supplied here.

`proof_status = NO_PROOF`.
-/
set_option autoImplicit false

open scoped BigOperators Classical
open GoldbachPurePrimeAdequacyV15
open GoldbachCircleMethodTwoScaleEvenBlockDefectReserveV1833
open GoldbachCircleMethodDiscreteArcModelReserveV1855
open GoldbachCircleMethodActualOvershootTwoChannelV18631
open GoldbachCircleMethodDiscreteModelExceptionDetectorV18632

namespace GoldbachCircleMethodDiscreteModelExceptionCountTransferV18635

/-- Every exceptional target contributes at least `(M / 28)^2` to the
unchanged discrete-model overshoot moment.  This is a finite counting
identity/inequality; the analytic hypotheses remain visible. -/
theorem exception_card_mul_threshold_sq_le_modelOvershootMoment
    (M P R : ℕ)
    (hScale : 112 * (Real.log (M : ℝ)) ^ 2 ≤ Real.sqrt (M : ℝ))
    (hModel : ∀ N ∈ evenTargetBlock M,
      (M : ℝ) / 14 ≤ discreteArcMainModel M N R P) :
    ((((evenTargetBlock M).filter (fun N => ¬ GoldbachAt N)).card : ℝ) *
        ((M : ℝ) / 28) ^ 2) ≤
      discreteModelOvershootSquaredMoment M P R (evenTargetBlock M) := by
  classical
  let exceptions := (evenTargetBlock M).filter (fun N => ¬ GoldbachAt N)
  calc
    (((exceptions.card : ℝ) * ((M : ℝ) / 28) ^ 2)) =
        ∑ _N ∈ exceptions, ((M : ℝ) / 28) ^ 2 := by simp
    _ ≤ ∑ N ∈ exceptions, (discreteModelOvershoot M P R N) ^ 2 := by
      exact Finset.sum_le_sum fun N hN => by
        have hData := Finset.mem_filter.mp hN
        have hOvershoot :=
          discreteModelOvershoot_ge_M_div_28_of_not_goldbachAt
            M P R N hData.1 hScale (hModel N hData.1) hData.2
        have hLeft : 0 ≤ (M : ℝ) / 28 := by positivity
        have hRight : 0 ≤ discreteModelOvershoot M P R N := by
          unfold discreteModelOvershoot
          exact le_max_right _ _
        nlinarith [mul_nonneg hLeft hRight]
    _ ≤ ∑ N ∈ evenTargetBlock M, (discreteModelOvershoot M P R N) ^ 2 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.filter_subset _ _
      · intro N _ _
        exact sq_nonneg (discreteModelOvershoot M P R N)
    _ = discreteModelOvershootSquaredMoment M P R (evenTargetBlock M) := by
      rfl

/-- A concrete moment budget `((M^2)/784) * B` bounds the real-valued
cardinality of the Goldbach-exception filter by `B`.  The positivity of `M`
is required only to divide by the nonzero threshold. -/
theorem exception_card_le_of_modelOvershootMoment_budget
    (M P R : ℕ) (B : ℝ) (hM : 0 < M)
    (hScale : 112 * (Real.log (M : ℝ)) ^ 2 ≤ Real.sqrt (M : ℝ))
    (hModel : ∀ N ∈ evenTargetBlock M,
      (M : ℝ) / 14 ≤ discreteArcMainModel M N R P)
    (hMoment :
      discreteModelOvershootSquaredMoment M P R (evenTargetBlock M) ≤
        ((M : ℝ) ^ 2 / 784) * B) :
    (((evenTargetBlock M).filter (fun N => ¬ GoldbachAt N)).card : ℝ) ≤ B := by
  have hCount :=
    exception_card_mul_threshold_sq_le_modelOvershootMoment
      M P R hScale hModel
  have hThreshold : 0 < ((M : ℝ) / 28) ^ 2 := by
    positivity
  have hNormalize : ((M : ℝ) / 28) ^ 2 = (M : ℝ) ^ 2 / 784 := by
    ring
  rw [hNormalize] at hCount
  have hCombined := hCount.trans hMoment
  have hMReal : 0 < (M : ℝ) ^ 2 / 784 := by positivity
  have hCombined' :
      ((M : ℝ) ^ 2 / 784) *
          (((evenTargetBlock M).filter (fun N => ¬ GoldbachAt N)).card : ℝ) ≤
        ((M : ℝ) ^ 2 / 784) * B := by
    simpa [mul_comm] using hCombined
  exact le_of_mul_le_mul_left hCombined' hMReal

/-- Effective-threshold wrapper.  It closes only the finite counting
transfer.  The uniform model reserve and model-overshoot moment budget are
still external number-theoretic inputs. -/
theorem exception_card_le_of_threshold_and_modelOvershootMoment_budget
    (M P R : ℕ) (B : ℝ) (hLarge : defectScaleThreshold ≤ M)
    (hModel : ∀ N ∈ evenTargetBlock M,
      (M : ℝ) / 14 ≤ discreteArcMainModel M N R P)
    (hMoment :
      discreteModelOvershootSquaredMoment M P R (evenTargetBlock M) ≤
        ((M : ℝ) ^ 2 / 784) * B) :
    (((evenTargetBlock M).filter (fun N => ¬ GoldbachAt N)).card : ℝ) ≤ B := by
  have hExp : Real.exp 40 ≤ (M : ℝ) :=
    (Nat.le_ceil (Real.exp 40)).trans (by exact_mod_cast hLarge)
  have hM : 0 < M := by
    exact_mod_cast (Real.exp_pos 40).trans_le hExp
  exact exception_card_le_of_modelOvershootMoment_budget
    M P R B hM (log_sq_gate_of_threshold_le M hLarge) hModel hMoment

end GoldbachCircleMethodDiscreteModelExceptionCountTransferV18635
