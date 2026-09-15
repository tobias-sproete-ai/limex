import GoldbachCircleMethodVariableFourChannelAbelV18330

/-!
# Goldbach V1.8.331: power-weight Abel interval

The canonical power weights on both sides of the Goldbach pair have total
variation at most `2*b*T/B` on an admissible block interval.  Substitution in
the four-channel Abel theorem removes the previous `b*B*Q^2` freezing loss.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodPowerWeightAbelIntervalV18331

open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodExceptionalWeightBoundaryV18128
open GoldbachCircleMethodFullFrozenPairwiseIntervalV18323
open GoldbachCircleMethodLogCutoffPresieveBindingV18120
open GoldbachCircleMethodVariableFourChannelAbelV18330
open GoldbachCircleMethodVariablePowerPairwiseIntervalV18325

/-- Total variation of the increasing-coordinate power weight. -/
theorem forward_powerWeight_total_variation_le
    (B : ℕ) (hB : 2 ≤ B) (b : ℝ) (hb : 0 ≤ b) (A T : ℕ)
    (hleft : ∀ i ∈ Finset.range T, A + i ∈ blockCarrier B) :
    ∑ i ∈ Finset.range (T - 1),
        |powerWeight b (A + (i + 1)) - powerWeight b (A + i)| ≤
      2 * b * (T : ℝ) / (B : ℝ) := by
  have hfactor : 0 ≤ 2 * b / (B : ℝ) := by positivity
  calc
    _ ≤ ∑ _i ∈ Finset.range (T - 1), 2 * b / (B : ℝ) := by
      apply Finset.sum_le_sum
      intro i hi
      have hi' := Finset.mem_range.mp hi
      have hiT : i < T := by omega
      have hisT : i + 1 < T := by omega
      have hstep := power_weight_variation B hB b hb
        (A + i) (A + (i + 1))
        (hleft i (Finset.mem_range.mpr hiT))
        (hleft (i + 1) (Finset.mem_range.mpr hisT))
      have hadd : A + (i + 1) = A + i + 1 := by omega
      have hdist :
          |((A + (i + 1) : ℕ) : ℝ) - ((A + i : ℕ) : ℝ)| = 1 := by
        rw [hadd]
        push_cast
        norm_num
      rw [hdist, mul_one] at hstep
      exact hstep
    _ = (((T - 1 : ℕ) : ℝ)) * (2 * b / (B : ℝ)) := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ ≤ (T : ℝ) * (2 * b / (B : ℝ)) := by
      apply mul_le_mul_of_nonneg_right _ hfactor
      exact_mod_cast Nat.sub_le T 1
    _ = 2 * b * (T : ℝ) / (B : ℝ) := by ring

/-- Total variation of the decreasing complementary-coordinate power weight. -/
theorem backward_powerWeight_total_variation_le
    (B : ℕ) (hB : 2 ≤ B) (b : ℝ) (hb : 0 ≤ b)
    (N A T : ℕ) (hend : A + T ≤ N + 1)
    (hright : ∀ i ∈ Finset.range T, N - (A + i) ∈ blockCarrier B) :
    ∑ i ∈ Finset.range (T - 1),
        |powerWeight b (N - (A + (i + 1))) -
          powerWeight b (N - (A + i))| ≤
      2 * b * (T : ℝ) / (B : ℝ) := by
  have hfactor : 0 ≤ 2 * b / (B : ℝ) := by positivity
  calc
    _ ≤ ∑ _i ∈ Finset.range (T - 1), 2 * b / (B : ℝ) := by
      apply Finset.sum_le_sum
      intro i hi
      have hi' := Finset.mem_range.mp hi
      have hiT : i < T := by omega
      have hisT : i + 1 < T := by omega
      have hleN : A + (i + 1) ≤ N := by omega
      have hpred :
          N - (A + i) = N - (A + (i + 1)) + 1 := by omega
      have hstep := power_weight_variation B hB b hb
        (N - (A + i)) (N - (A + (i + 1)))
        (hright i (Finset.mem_range.mpr hiT))
        (hright (i + 1) (Finset.mem_range.mpr hisT))
      have hdist :
          |((N - (A + (i + 1)) : ℕ) : ℝ) -
            ((N - (A + i) : ℕ) : ℝ)| = 1 := by
        rw [hpred]
        push_cast
        norm_num
      rw [hdist, mul_one] at hstep
      exact hstep
    _ = (((T - 1 : ℕ) : ℝ)) * (2 * b / (B : ℝ)) := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ ≤ (T : ℝ) * (2 * b / (B : ℝ)) := by
      apply mul_le_mul_of_nonneg_right _ hfactor
      exact_mod_cast Nat.sub_le T 1
    _ = 2 * b * (T : ℝ) / (B : ℝ) := by ring

/-- The V1.8.325 interval is definitionally the variable four-channel object
for the two canonical power-weight sequences. -/
theorem variablePowerPairInterval_eq_variableFourChannelPairInterval
    {Q : ℕ} (hQ : 1 ≤ Q)
    (r : PositiveLevel Q)
    (chi : {χ : DirichletCharacter ℂ r.val // χ.IsPrimitive})
    (v w : ℕ → ℂ) (b : ℝ) (N A T : ℕ) :
    variablePowerPairInterval hQ r chi v w b N A T =
      variableFourChannelPairInterval hQ r chi v w
        (fun i => powerWeight b (N - (A + i)))
        (fun i => powerWeight b (A + i)) N A T := by
  unfold variablePowerPairInterval variableFourChannelPairInterval
    naturalFrozenCoefficient
  rfl

/-- The variable arithmetic mean attached to the power-weight interval. -/
noncomputable def powerPairwiseVariableMean {Q : ℕ} (hQ : 1 ≤ Q)
    (r : PositiveLevel Q)
    (chi : {χ : DirichletCharacter ℂ r.val // χ.IsPrimitive})
    (v w : ℕ → ℂ) (b : ℝ) (N A T : ℕ) : ℂ :=
  variableFourChannelMean hQ r chi v w
    (fun i => powerWeight b (N - (A + i)))
    (fun i => powerWeight b (A + i)) N T

/-- Main interval result: pairwise periodicity plus Abel summation controls the
fully variable power-weight model by `Q^4` times a bounded variation factor. -/
theorem variablePowerPairInterval_abel_centered_norm_le
    {Q : ℕ} (hQ : 1 ≤ Q)
    (r : PositiveLevel Q)
    (chi : {χ : DirichletCharacter ℂ r.val // χ.IsPrimitive})
    (hInv : chi.val⁻¹ = chi.val)
    (v w : ℕ → ℂ) (b : ℝ) (N A T B : ℕ)
    (hB : 2 ≤ B) (hb : 0 ≤ b) (hT : 1 ≤ T)
    (hend : A + T ≤ N + 1)
    (hleft : ∀ i ∈ Finset.range T, A + i ∈ blockCarrier B)
    (hright : ∀ i ∈ Finset.range T, N - (A + i) ∈ blockCarrier B)
    (V W : ℝ) (hV : 0 ≤ V) (hW : 0 ≤ W)
    (hv : ∀ n : ℕ, ‖v n‖ ≤ V) (hw : ∀ n : ℕ, ‖w n‖ ≤ W) :
    ‖variablePowerPairInterval hQ r chi v w b N A T -
        powerPairwiseVariableMean hQ r chi v w b N A T‖ ≤
      (2 * (Q : ℝ) ^ 4 * V * W) *
        (4 + 8 * b * (T : ℝ) / (B : ℝ)) := by
  rw [variablePowerPairInterval_eq_variableFourChannelPairInterval]
  unfold powerPairwiseVariableMean
  have hu := backward_powerWeight_total_variation_le
    B hB b hb N A T hend hright
  have hz := forward_powerWeight_total_variation_le B hB b hb A T hleft
  have h := variableFourChannelPairInterval_centered_norm_le
    hQ r chi hInv v w
    (fun i => powerWeight b (N - (A + i)))
    (fun i => powerWeight b (A + i)) N A T hT hend
    V W hV hW hv hw
    (2 * b * (T : ℝ) / (B : ℝ))
    (2 * b * (T : ℝ) / (B : ℝ))
    (fun i hi => power_weight_abs_le_one B (N - (A + i)) b hb
      (hright i (Finset.mem_range.mpr hi)))
    (fun i hi => power_weight_abs_le_one B (A + i) b hb
      (hleft i (Finset.mem_range.mpr hi))) hu hz
  convert h using 1
  all_goals ring

end GoldbachCircleMethodPowerWeightAbelIntervalV18331
