import GoldbachCircleMethodPairwiseMeanDiagonalCompatibilityV18324
import GoldbachCircleMethodExceptionalWeightBoundaryV18128

/-!
# Goldbach V1.8.325: variable power transport into the pairwise-period bound

The spatial powers in the actual adjusted factors are compared with their two
endpoint-frozen values.  The resulting variation cost is combined with the
V1.8.323 quartic pairwise-period error.  No positivity or absorption claim is
made here.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodVariablePowerPairwiseIntervalV18325

open GoldbachCircleMethodActiveExceptionalCenteringV18129
open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodExceptionalWeightBoundaryV18128
open GoldbachCircleMethodFiniteCompanionBindingV18118
open GoldbachCircleMethodFullFrozenPairwiseIntervalV18323
open GoldbachCircleMethodLogCutoffPresieveBindingV18120
open GoldbachCircleMethodPairwiseMeanDiagonalCompatibilityV18324
open GoldbachCircleMethodPrincipalWindowBoundaryV18121

/-- General two-factor perturbation with a common pointwise envelope. -/
theorem adjusted_factor_pair_perturbation_norm_le
    (P₁ A₁ P₂ A₂ : ℂ) (a a₀ b b₀ : ℝ) (Z : ℝ)
    (hZ : 0 ≤ Z)
    (hP₁ : ‖P₁‖ ≤ Z) (hA₁ : ‖A₁‖ ≤ Z)
    (hP₂ : ‖P₂‖ ≤ Z) (hA₂ : ‖A₂‖ ≤ Z)
    (ha₀ : |a₀| ≤ 1) (hb : |b| ≤ 1) :
    ‖(P₁ - (a : ℂ) * A₁) * (P₂ - (b : ℂ) * A₂) -
        (P₁ - (a₀ : ℂ) * A₁) * (P₂ - (b₀ : ℂ) * A₂)‖ ≤
      2 * Z ^ 2 * (|a - a₀| + |b - b₀|) := by
  have hright : ‖P₂ - (b : ℂ) * A₂‖ ≤ 2 * Z := by
    calc
      _ ≤ ‖P₂‖ + ‖(b : ℂ) * A₂‖ := norm_sub_le _ _
      _ = ‖P₂‖ + |b| * ‖A₂‖ := by
        simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ Z + 1 * Z := by gcongr
      _ = 2 * Z := by ring
  have hleft : ‖P₁ - (a₀ : ℂ) * A₁‖ ≤ 2 * Z := by
    calc
      _ ≤ ‖P₁‖ + ‖(a₀ : ℂ) * A₁‖ := norm_sub_le _ _
      _ = ‖P₁‖ + |a₀| * ‖A₁‖ := by
        simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ Z + 1 * Z := by gcongr
      _ = 2 * Z := by ring
  have hid :
      (P₁ - (a : ℂ) * A₁) * (P₂ - (b : ℂ) * A₂) -
          (P₁ - (a₀ : ℂ) * A₁) * (P₂ - (b₀ : ℂ) * A₂) =
        ((a₀ - a : ℝ) : ℂ) * A₁ * (P₂ - (b : ℂ) * A₂) +
          ((b₀ - b : ℝ) : ℂ) * A₂ * (P₁ - (a₀ : ℂ) * A₁) := by
    push_cast
    ring
  rw [hid]
  calc
    _ ≤ ‖((a₀ - a : ℝ) : ℂ) * A₁ * (P₂ - (b : ℂ) * A₂)‖ +
        ‖((b₀ - b : ℝ) : ℂ) * A₂ * (P₁ - (a₀ : ℂ) * A₁)‖ :=
      norm_add_le _ _
    _ = |a - a₀| * ‖A₁‖ * ‖P₂ - (b : ℂ) * A₂‖ +
        |b - b₀| * ‖A₂‖ * ‖P₁ - (a₀ : ℂ) * A₁‖ := by
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]
    _ ≤ |a - a₀| * Z * (2 * Z) + |b - b₀| * Z * (2 * Z) := by
      apply add_le_add
      · exact mul_le_mul
          (mul_le_mul_of_nonneg_left hA₁ (abs_nonneg _)) hright
          (norm_nonneg _) (mul_nonneg (abs_nonneg _) hZ)
      · exact mul_le_mul
          (mul_le_mul_of_nonneg_left hA₂ (abs_nonneg _)) hleft
          (norm_nonneg _) (mul_nonneg (abs_nonneg _) hZ)
    _ = _ := by ring

/-- The actual adjusted pair sum on one half-open natural interval. -/
noncomputable def variablePowerPairInterval {Q : ℕ} (hQ : 1 ≤ Q)
    (r : PositiveLevel Q)
    (chi : {χ : DirichletCharacter ℂ r.val // χ.IsPrimitive})
    (v w : ℕ → ℂ) (b : ℝ) (N A T : ℕ) : ℂ :=
  ∑ i ∈ Finset.range T,
    naturalFrozenCoefficient hQ r chi v (powerWeight b (N - (A + i)) : ℂ)
        (N - (A + i)) *
      naturalFrozenCoefficient hQ r chi w (powerWeight b (A + i) : ℂ)
        (A + i)

/-- Endpoint-frozen pair sum used by the pairwise-period theorem. -/
noncomputable def endpointFrozenPairInterval {Q : ℕ} (hQ : 1 ≤ Q)
    (r : PositiveLevel Q)
    (chi : {χ : DirichletCharacter ℂ r.val // χ.IsPrimitive})
    (v w : ℕ → ℂ) (b : ℝ) (N A T : ℕ) : ℂ :=
  ∑ i ∈ Finset.range T,
    naturalFrozenCoefficient hQ r chi v (powerWeight b (N - A) : ℂ)
        (N - (A + i)) *
      naturalFrozenCoefficient hQ r chi w (powerWeight b A : ℂ)
        (A + i)

theorem naturalFrozenCoefficient_powerWeight_eq_adjustedModel
    {Q : ℕ} (hQ : 1 ≤ Q) (r : PositiveLevel Q)
    (chi : {χ : DirichletCharacter ℂ r.val // χ.IsPrimitive})
    (w : ℕ → ℂ) (b : ℝ) (n : ℕ) :
    naturalFrozenCoefficient hQ r chi w (powerWeight b n : ℂ) n =
      adjustedModel Q n hQ b w ⟨r, chi⟩ := by
  unfold naturalFrozenCoefficient adjustedModel windowCoefficient
  ring

/-- Spatial freezing cost for the full amplitude-aware pair, with the actual
principal and active coefficient envelopes derived from the coupled cutoff. -/
theorem variablePowerPairInterval_sub_endpointFrozen_norm_le
    {Q : ℕ} (hQ : 1 ≤ Q)
    (r : PositiveLevel Q)
    (chi : {χ : DirichletCharacter ℂ r.val // χ.IsPrimitive})
    (v w : ℕ → ℂ) (b : ℝ) (N A T B : ℕ)
    (hB : 2 ≤ B) (hb : 0 ≤ b) (hAN : A ≤ N)
    (hend : A + T ≤ N + 1)
    (hA : A ∈ blockCarrier B) (hNA : N - A ∈ blockCarrier B)
    (hleft : ∀ i ∈ Finset.range T, A + i ∈ blockCarrier B)
    (hright : ∀ i ∈ Finset.range T, N - (A + i) ∈ blockCarrier B)
    (M : ℝ) (hM : 0 ≤ M)
    (hv : ∀ n : ℕ, ‖v n‖ ≤ M)
    (hw : ∀ n : ℕ, ‖w n‖ ≤ M) :
    ‖variablePowerPairInterval hQ r chi v w b N A T -
        endpointFrozenPairInterval hQ r chi v w b N A T‖ ≤
      8 * b * (M * (Q : ℝ)) ^ 2 * (T : ℝ) ^ 2 / (B : ℝ) := by
  have hBpos : (0 : ℝ) < B := by exact_mod_cast (by omega : 0 < B)
  let Z : ℝ := M * (Q : ℝ)
  have hZ : 0 ≤ Z := mul_nonneg hM (Nat.cast_nonneg Q)
  have hterm (i : ℕ) (hi : i ∈ Finset.range T) :
      ‖naturalFrozenCoefficient hQ r chi v
            (powerWeight b (N - (A + i)) : ℂ) (N - (A + i)) *
          naturalFrozenCoefficient hQ r chi w
            (powerWeight b (A + i) : ℂ) (A + i) -
        naturalFrozenCoefficient hQ r chi v
            (powerWeight b (N - A) : ℂ) (N - (A + i)) *
          naturalFrozenCoefficient hQ r chi w
            (powerWeight b A : ℂ) (A + i)‖ ≤
        8 * b * Z ^ 2 * (T : ℝ) / (B : ℝ) := by
    have hiT : i < T := Finset.mem_range.mp hi
    have hiN : A + i ≤ N := by omega
    have hP₁ : ‖finiteCompanion (oneLevel hQ) (N - (A + i)) v‖ ≤ Z := by
      dsimp only [Z]
      simpa [oneLevel] using
        (finite_companion_norm_le_quotient Q (N - (A + i))
          (oneLevel hQ) v M hM hv)
    have hA₁ : ‖windowCoefficient r (N - (A + i)) v chi‖ ≤ Z := by
      exact window_coefficient_norm_le_linear Q (N - (A + i)) r v M hM hv chi
    have hP₂ : ‖finiteCompanion (oneLevel hQ) (A + i) w‖ ≤ Z := by
      dsimp only [Z]
      simpa [oneLevel] using
        (finite_companion_norm_le_quotient Q (A + i)
          (oneLevel hQ) w M hM hw)
    have hA₂ : ‖windowCoefficient r (A + i) w chi‖ ≤ Z := by
      exact window_coefficient_norm_le_linear Q (A + i) r w M hM hw chi
    have ha₀ := power_weight_abs_le_one B (N - A) b hb hNA
    have hbvar := power_weight_abs_le_one B (A + i) b hb (hleft i hi)
    have hvar₁ := power_weight_variation B hB b hb (N - A)
      (N - (A + i)) hNA (hright i hi)
    have hvar₂ := power_weight_variation B hB b hb A (A + i) hA (hleft i hi)
    have hdist₁ :
        |((N - (A + i) : ℕ) : ℝ) - ((N - A : ℕ) : ℝ)| = (i : ℝ) := by
      rw [Nat.cast_sub hiN, Nat.cast_sub hAN]
      push_cast
      rw [show (N : ℝ) - ((A : ℝ) + (i : ℝ)) -
          ((N : ℝ) - (A : ℝ)) = -(i : ℝ) by ring,
        abs_neg, abs_of_nonneg (Nat.cast_nonneg i)]
    have hdist₂ : |((A + i : ℕ) : ℝ) - (A : ℝ)| = (i : ℝ) := by
      push_cast
      rw [show (A : ℝ) + (i : ℝ) - (A : ℝ) = (i : ℝ) by ring,
        abs_of_nonneg (Nat.cast_nonneg i)]
    rw [hdist₁] at hvar₁
    rw [hdist₂] at hvar₂
    unfold naturalFrozenCoefficient
    have hp := adjusted_factor_pair_perturbation_norm_le
      (finiteCompanion (oneLevel hQ) (N - (A + i)) v)
      (windowCoefficient r (N - (A + i)) v chi)
      (finiteCompanion (oneLevel hQ) (A + i) w)
      (windowCoefficient r (A + i) w chi)
      (powerWeight b (N - (A + i))) (powerWeight b (N - A))
      (powerWeight b (A + i)) (powerWeight b A) Z hZ
      hP₁ hA₁ hP₂ hA₂ ha₀ hbvar
    apply hp.trans
    have hiTreal : (i : ℝ) ≤ T := by exact_mod_cast (Nat.le_of_lt hiT)
    calc
      2 * Z ^ 2 *
          (|powerWeight b (N - (A + i)) - powerWeight b (N - A)| +
            |powerWeight b (A + i) - powerWeight b A|) ≤
          2 * Z ^ 2 *
            ((2 * b / (B : ℝ)) * (i : ℝ) +
              (2 * b / (B : ℝ)) * (i : ℝ)) := by
        gcongr
      _ = 8 * b * Z ^ 2 * (i : ℝ) / (B : ℝ) := by field_simp; ring
      _ ≤ 8 * b * Z ^ 2 * (T : ℝ) / (B : ℝ) := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hiTreal (by positivity)) hBpos.le
  unfold variablePowerPairInterval endpointFrozenPairInterval
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i ∈ Finset.range T,
        ‖naturalFrozenCoefficient hQ r chi v
              (powerWeight b (N - (A + i)) : ℂ) (N - (A + i)) *
            naturalFrozenCoefficient hQ r chi w
              (powerWeight b (A + i) : ℂ) (A + i) -
          naturalFrozenCoefficient hQ r chi v
              (powerWeight b (N - A) : ℂ) (N - (A + i)) *
            naturalFrozenCoefficient hQ r chi w
              (powerWeight b A : ℂ) (A + i)‖ := norm_sum_le _ _
    _ ≤ ∑ _i ∈ Finset.range T, 8 * b * Z ^ 2 * (T : ℝ) / (B : ℝ) :=
      Finset.sum_le_sum hterm
    _ = 8 * b * (M * (Q : ℝ)) ^ 2 * (T : ℝ) ^ 2 / (B : ℝ) := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      dsimp only [Z]
      ring

/-- The variable-power interval is controlled by the same arithmetic mean as
the frozen complete diagonal, plus explicit spatial and pairwise-period costs. -/
theorem variablePowerPairInterval_centered_norm_le
    {Q : ℕ} (hQ : 1 ≤ Q)
    (r : PositiveLevel Q)
    (chi : {χ : DirichletCharacter ℂ r.val // χ.IsPrimitive})
    (hInv : chi.val⁻¹ = chi.val)
    (v w : ℕ → ℂ) (b : ℝ) (N A T B : ℕ)
    (hB : 2 ≤ B) (hb : 0 ≤ b) (hAN : A ≤ N)
    (hend : A + T ≤ N + 1)
    (hA : A ∈ blockCarrier B) (hNA : N - A ∈ blockCarrier B)
    (hleft : ∀ i ∈ Finset.range T, A + i ∈ blockCarrier B)
    (hright : ∀ i ∈ Finset.range T, N - (A + i) ∈ blockCarrier B)
    (M : ℝ) (hM : 0 ≤ M)
    (hv : ∀ n : ℕ, ‖v n‖ ≤ M)
    (hw : ∀ n : ℕ, ‖w n‖ ≤ M) :
    ‖variablePowerPairInterval hQ r chi v w b N A T -
        (T : ℂ) * fullFrozenPairwiseMean hQ r chi v w
          (powerWeight b (N - A) : ℂ) (powerWeight b A : ℂ) N‖ ≤
      8 * b * (M * (Q : ℝ)) ^ 2 * (T : ℝ) ^ 2 / (B : ℝ) +
        8 * (Q : ℝ) ^ 4 * M ^ 2 := by
  have hvar := variablePowerPairInterval_sub_endpointFrozen_norm_le
    hQ r chi v w b N A T B hB hb hAN hend hA hNA hleft hright M hM hv hw
  have hpair := fullFrozenPairwiseError_norm_le_quartic hQ r chi hInv
    v w (powerWeight b (N - A) : ℂ) (powerWeight b A : ℂ)
    N A T hend M M hM hM hv hw
  have hanchor₁ := power_weight_abs_le_one B (N - A) b hb hNA
  have hanchor₂ := power_weight_abs_le_one B A b hb hA
  have hpair' :
      ‖endpointFrozenPairInterval hQ r chi v w b N A T -
          (T : ℂ) * fullFrozenPairwiseMean hQ r chi v w
            (powerWeight b (N - A) : ℂ) (powerWeight b A : ℂ) N‖ ≤
        8 * (Q : ℝ) ^ 4 * M ^ 2 := by
    change ‖fullFrozenPairwiseError hQ r chi v w
        (powerWeight b (N - A) : ℂ) (powerWeight b A : ℂ) N A T‖ ≤ _
    apply hpair.trans
    simp only [Complex.norm_real, Real.norm_eq_abs]
    have hQ0 : 0 ≤ (Q : ℝ) := Nat.cast_nonneg Q
    calc
      (2 * (Q : ℝ) ^ 4 * M * M) * (1 + |powerWeight b (N - A)|) *
          (1 + |powerWeight b A|) ≤
          (2 * (Q : ℝ) ^ 4 * M * M) * 2 * 2 := by
        gcongr <;> linarith
      _ = 8 * (Q : ℝ) ^ 4 * M ^ 2 := by ring
  calc
    _ ≤ ‖variablePowerPairInterval hQ r chi v w b N A T -
          endpointFrozenPairInterval hQ r chi v w b N A T‖ +
        ‖endpointFrozenPairInterval hQ r chi v w b N A T -
          (T : ℂ) * fullFrozenPairwiseMean hQ r chi v w
            (powerWeight b (N - A) : ℂ) (powerWeight b A : ℂ) N‖ := by
      rw [show variablePowerPairInterval hQ r chi v w b N A T -
          (T : ℂ) * fullFrozenPairwiseMean hQ r chi v w
            (powerWeight b (N - A) : ℂ) (powerWeight b A : ℂ) N =
        (variablePowerPairInterval hQ r chi v w b N A T -
          endpointFrozenPairInterval hQ r chi v w b N A T) +
        (endpointFrozenPairInterval hQ r chi v w b N A T -
          (T : ℂ) * fullFrozenPairwiseMean hQ r chi v w
            (powerWeight b (N - A) : ℂ) (powerWeight b A : ℂ) N) by ring]
      exact norm_add_le _ _
    _ ≤ _ := add_le_add hvar hpair'

end GoldbachCircleMethodVariablePowerPairwiseIntervalV18325
