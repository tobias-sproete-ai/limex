import GoldbachCircleMethodAttestedUnitPairZeroGapReserveV18271
import GoldbachCircleMethodExceptionalWeightBoundaryV18128

/-!
# Goldbach V1.8.272: variable-weight interval discrepancy

This module isolates the missing finite-interval adapter after V1.8.271.
The spatial powers remain inside the interval sum.  They are compared with
one frozen pair of endpoint weights, and the discrepancy is retained as an
explicit norm cost.  No periodic reserve or positivity statement is imported
into this estimate.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodVariableWeightIntervalDiscrepancyV18272

open GoldbachCircleMethodLogCutoffPresieveBindingV18120
open GoldbachCircleMethodExceptionalWeightBoundaryV18128
open GoldbachCircleMethodActualUnitPairArithmeticV18194

/-- Perturbing two real weights in a quadratic character factor costs at most
twice the variation of each weight.  The asymmetric hypotheses are exactly
the two factor envelopes used by the displayed algebraic decomposition. -/
theorem factor_pair_perturbation_norm_le
    (z y : ℂ) (hz : ‖z‖ ≤ 1) (hy : ‖y‖ ≤ 1)
    (a a₀ b b₀ : ℝ) (ha₀ : |a₀| ≤ 1) (hb : |b| ≤ 1) :
    ‖(1-(a : ℂ)*z)*(1-(b : ℂ)*y) -
        (1-(a₀ : ℂ)*z)*(1-(b₀ : ℂ)*y)‖ ≤
      2*|a-a₀| + 2*|b-b₀| := by
  have hby : ‖1-(b : ℂ)*y‖ ≤ 2 := by
    calc
      _ ≤ ‖(1 : ℂ)‖ + ‖(b : ℂ)*y‖ := norm_sub_le _ _
      _ = 1 + |b| * ‖y‖ := by simp
      _ ≤ 2 := by
        have hmul : |b| * ‖y‖ ≤ 1 * 1 :=
          mul_le_mul hb hy (norm_nonneg y) (by positivity)
        nlinarith
  have ha₀z : ‖1-(a₀ : ℂ)*z‖ ≤ 2 := by
    calc
      _ ≤ ‖(1 : ℂ)‖ + ‖(a₀ : ℂ)*z‖ := norm_sub_le _ _
      _ = 1 + |a₀| * ‖z‖ := by simp
      _ ≤ 2 := by
        have hmul : |a₀| * ‖z‖ ≤ 1 * 1 :=
          mul_le_mul ha₀ hz (norm_nonneg z) (by positivity)
        nlinarith
  have hid :
      (1-(a : ℂ)*z)*(1-(b : ℂ)*y) -
          (1-(a₀ : ℂ)*z)*(1-(b₀ : ℂ)*y) =
        ((a₀-a : ℝ) : ℂ)*z*(1-(b : ℂ)*y) +
          ((b₀-b : ℝ) : ℂ)*y*(1-(a₀ : ℂ)*z) := by
    push_cast
    ring
  rw [hid]
  calc
    _ ≤ ‖((a₀-a : ℝ) : ℂ)*z*(1-(b : ℂ)*y)‖ +
        ‖((b₀-b : ℝ) : ℂ)*y*(1-(a₀ : ℂ)*z)‖ := norm_add_le _ _
    _ = |a-a₀| * ‖z‖ * ‖1-(b : ℂ)*y‖ +
        |b-b₀| * ‖y‖ * ‖1-(a₀ : ℂ)*z‖ := by
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]
    _ ≤ |a-a₀| * 1 * 2 + |b-b₀| * 1 * 2 := by
      apply add_le_add
      · exact mul_le_mul
          (mul_le_mul_of_nonneg_left hz (abs_nonneg (a-a₀))) hby
          (norm_nonneg _) (mul_nonneg (abs_nonneg _) (by positivity))
      · exact mul_le_mul
          (mul_le_mul_of_nonneg_left hy (abs_nonneg (b-b₀))) ha₀z
          (norm_nonneg _) (mul_nonneg (abs_nonneg _) (by positivity))
    _ = _ := by ring

/-- The literal unit-pair interval with both spatial power weights left at
their actual natural-number arguments. -/
noncomputable def variableUnitPairInterval
    (r N A T : ℕ) [NeZero r] (chi : DirichletCharacter ℂ r) (b : ℝ) : ℂ :=
  ∑ i ∈ Finset.range T,
    if ((A+i : ℕ) : ZMod r) ∈ unitPairResidues r (N : ℤ) then
      (1-(powerWeight b (A+i) : ℂ)*chi ((A+i : ℕ) : ZMod r)) *
        (1-(powerWeight b (N-(A+i)) : ℂ)*
          chi ((N : ZMod r)-((A+i : ℕ) : ZMod r)))
    else 0

/-- The same interval carrier with the two weights frozen at the left
endpoint `A` and its complementary point `N-A`. -/
noncomputable def frozenUnitPairInterval
    (r N A T : ℕ) [NeZero r] (chi : DirichletCharacter ℂ r) (b : ℝ) : ℂ :=
  ∑ i ∈ Finset.range T,
    if ((A+i : ℕ) : ZMod r) ∈ unitPairResidues r (N : ℤ) then
      (1-(powerWeight b A : ℂ)*chi ((A+i : ℕ) : ZMod r)) *
        (1-(powerWeight b (N-A) : ℂ)*
          chi ((N : ZMod r)-((A+i : ℕ) : ZMod r)))
    else 0

/-- On one genuine half-open interval, freezing the two spatial powers has
an explicit quadratic-in-length cost.  All actual and frozen arguments must
remain in the same dyadic block; this condition is not inferred silently.

The deliberately conservative constant `8` avoids any unrecorded endpoint
or average-distance optimization. -/
theorem variable_unit_pair_interval_discrepancy
    (r N A T B : ℕ) [NeZero r]
    (chi : DirichletCharacter ℂ r) (b : ℝ)
    (hB : 2 ≤ B) (hb : 0 ≤ b) (hAN : A ≤ N)
    (hend : A+T ≤ N+1)
    (hA : A ∈ blockCarrier B) (hNA : N-A ∈ blockCarrier B)
    (hleft : ∀ i ∈ Finset.range T, A+i ∈ blockCarrier B)
    (hright : ∀ i ∈ Finset.range T, N-(A+i) ∈ blockCarrier B) :
    ‖variableUnitPairInterval r N A T chi b -
        frozenUnitPairInterval r N A T chi b‖ ≤
      8*b*(T : ℝ)^2/(B : ℝ) := by
  have hBpos : (0 : ℝ) < B := by exact_mod_cast (by omega : 0 < B)
  have hterm (i : ℕ) (hi : i ∈ Finset.range T) :
      ‖(if ((A+i : ℕ) : ZMod r) ∈ unitPairResidues r (N : ℤ) then
          (1-(powerWeight b (A+i) : ℂ)*chi ((A+i : ℕ) : ZMod r)) *
            (1-(powerWeight b (N-(A+i)) : ℂ)*
              chi ((N : ZMod r)-((A+i : ℕ) : ZMod r)))
        else 0) -
        (if ((A+i : ℕ) : ZMod r) ∈ unitPairResidues r (N : ℤ) then
          (1-(powerWeight b A : ℂ)*chi ((A+i : ℕ) : ZMod r)) *
            (1-(powerWeight b (N-A) : ℂ)*
              chi ((N : ZMod r)-((A+i : ℕ) : ZMod r)))
        else 0)‖ ≤ 8*b*(T : ℝ)/(B : ℝ) := by
    have hiT : i < T := Finset.mem_range.mp hi
    have hiN : A+i ≤ N := by omega
    by_cases hmem : ((A+i : ℕ) : ZMod r) ∈ unitPairResidues r (N : ℤ)
    · simp only [hmem, if_true]
      have hdistA : |((A+i : ℕ) : ℝ)-(A : ℝ)| = (i : ℝ) := by
        push_cast
        rw [show (A : ℝ) + (i : ℝ) - (A : ℝ) = (i : ℝ) by ring,
          abs_of_nonneg (Nat.cast_nonneg i)]
      have hdistNA : |((N-(A+i) : ℕ) : ℝ)-((N-A : ℕ) : ℝ)| = (i : ℝ) := by
        rw [Nat.cast_sub hiN, Nat.cast_sub hAN]
        push_cast
        rw [show (N : ℝ) - ((A : ℝ) + (i : ℝ)) -
            ((N : ℝ) - (A : ℝ)) = -(i : ℝ) by ring,
          abs_neg, abs_of_nonneg (Nat.cast_nonneg i)]
      have hvarA := power_weight_variation B hB b hb A (A+i) hA (hleft i hi)
      have hvarNA := power_weight_variation B hB b hb (N-A) (N-(A+i))
        hNA (hright i hi)
      rw [hdistA] at hvarA
      rw [hdistNA] at hvarNA
      have hanchor := power_weight_abs_le_one B A b hb hA
      have hrightwt := power_weight_abs_le_one B (N-(A+i)) b hb (hright i hi)
      have hp := factor_pair_perturbation_norm_le
        (chi ((A+i : ℕ) : ZMod r))
        (chi ((N : ZMod r)-((A+i : ℕ) : ZMod r)))
        (chi.norm_le_one _) (chi.norm_le_one _)
        (powerWeight b (A+i)) (powerWeight b A)
        (powerWeight b (N-(A+i))) (powerWeight b (N-A))
        hanchor hrightwt
      apply hp.trans
      have hiTreal : (i : ℝ) ≤ T := by exact_mod_cast (Nat.le_of_lt hiT)
      calc
        2*|powerWeight b (A+i)-powerWeight b A| +
            2*|powerWeight b (N-(A+i))-powerWeight b (N-A)|
            ≤ 2*((2*b/(B : ℝ))*(i : ℝ)) +
                2*((2*b/(B : ℝ))*(i : ℝ)) :=
              add_le_add (mul_le_mul_of_nonneg_left hvarA (by positivity))
                (mul_le_mul_of_nonneg_left hvarNA (by positivity))
        _ = 8*b*(i : ℝ)/(B : ℝ) := by field_simp; ring
        _ ≤ 8*b*(T : ℝ)/(B : ℝ) := by
          exact div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left hiTreal (by positivity)) hBpos.le
    · push_cast at hmem ⊢
      simp only [hmem, if_false, sub_self, norm_zero]
      positivity
  unfold variableUnitPairInterval frozenUnitPairInterval
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i ∈ Finset.range T,
        ‖(if ((A+i : ℕ) : ZMod r) ∈ unitPairResidues r (N : ℤ) then
            (1-(powerWeight b (A+i) : ℂ)*chi ((A+i : ℕ) : ZMod r)) *
              (1-(powerWeight b (N-(A+i)) : ℂ)*
                chi ((N : ZMod r)-((A+i : ℕ) : ZMod r)))
          else 0) -
          (if ((A+i : ℕ) : ZMod r) ∈ unitPairResidues r (N : ℤ) then
            (1-(powerWeight b A : ℂ)*chi ((A+i : ℕ) : ZMod r)) *
              (1-(powerWeight b (N-A) : ℂ)*
                chi ((N : ZMod r)-((A+i : ℕ) : ZMod r)))
          else 0)‖ := norm_sum_le _ _
    _ ≤ ∑ _i ∈ Finset.range T, 8*b*(T : ℝ)/(B : ℝ) :=
      Finset.sum_le_sum (fun i hi => hterm i hi)
    _ = 8*b*(T : ℝ)^2/(B : ℝ) := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      ring

end GoldbachCircleMethodVariableWeightIntervalDiscrepancyV18272
