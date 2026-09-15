import GoldbachCircleMethodNonsquarefreeMaskRegressionV1888
import Mathlib.NumberTheory.Chebyshev

/-! Reuse Mathlib's proved Chebyshev bound, not an external axiom. -/
set_option autoImplicit false
open scoped BigOperators Classical
open MeasureTheory AddCircle
open GoldbachCircleMethodFourierIdentityV171
open GoldbachPrimePowerDefectBoundV161
open GoldbachCircleMethodTwoScaleIntegralPartitionV1831
open GoldbachCircleMethodTwoScaleEvenBlockDefectReserveV1833
open GoldbachCircleMethodTwoScaleBesselBridgeV1834
open GoldbachCircleMethodFiniteFourierL2MinorMomentV1872
open GoldbachCircleMethodRealApproximationMinorAdapterV1873
open GoldbachCircleMethodQuantitativeMinorEvenBlockV1874
open GoldbachPurePrimeAdequacyV15

namespace GoldbachCircleMethodChebyshevEnergyBudgetV1889

noncomputable def chebyshevConstant : ℝ := Real.log 4 + 4

theorem chebyshevConstant_pos : 0 < chebyshevConstant := by
  unfold chebyshevConstant
  have h := Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num)
  linarith

theorem actual_lambda_sum_eq_psi (M : ℕ) :
    (∑ n ∈ Finset.range M, ArithmeticFunction.vonMangoldt (n+1)) =
      Chebyshev.psi (M : ℝ) := by
  rw [Chebyshev.psi_eq_sum_Icc, Nat.floor_natCast]
  have hset : Finset.Icc 0 M = Finset.range M.succ := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_range]
    omega
  rw [hset]
  simp [Finset.sum_range_succ']

theorem actual_lambda_square_sum_le (M : ℕ) :
    (∑ n ∈ Finset.range M, (ArithmeticFunction.vonMangoldt (n+1))^2) ≤
      chebyshevConstant*(M : ℝ)*Real.log (M : ℝ) := by
  calc
    _ ≤ ∑ n ∈ Finset.range M,
        ArithmeticFunction.vonMangoldt (n+1)*Real.log (M : ℝ) := by
      apply Finset.sum_le_sum
      intro n hn
      have hnM : n+1 ≤ M := by have := Finset.mem_range.mp hn; omega
      have hu := vonMangoldt_le_log_nat_of_le hnM
      have hn0 : 0 ≤ ArithmeticFunction.vonMangoldt (n+1) :=
        ArithmeticFunction.vonMangoldt_nonneg
      nlinarith
    _ = Chebyshev.psi (M : ℝ)*Real.log (M : ℝ) := by
      rw [← Finset.sum_mul, actual_lambda_sum_eq_psi]
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (Chebyshev.psi_le_const_mul_self (Nat.cast_nonneg M)) (Real.log_natCast_nonneg M)

theorem actual_L2_le_chebyshev (M : ℕ) :
    (∫ x : UnitAddCircle, ‖exponentialSum M.succ x‖^2 ∂haarAddCircle) ≤
      chebyshevConstant*(M : ℝ)*Real.log (M : ℝ) := by
  rw [exponentialSum_integral_norm_sq]
  exact actual_lambda_square_sum_le M

theorem minorFourthMoment_le_chebyshev_L2 (M P R : ℕ) (A : ℝ) (hA : 0 ≤ A)
    (hMinor : ∀ x ∈ twoScaleMinorMask M P R, ‖exponentialSum M.succ x‖^2 ≤ A) :
    minorFourthMoment M P R ≤ A*(chebyshevConstant*(M : ℝ)*Real.log (M : ℝ)) :=
  (minorFourthMoment_le_bound_mul_L2 M P R A hA hMinor).trans
    (mul_le_mul_of_nonneg_left (actual_L2_le_chebyshev M) hA)

noncomputable def chebyshevFourthBudget (M P R : ℕ) (C : ℝ) : ℝ :=
  3*chebyshevConstant*C^2*(M : ℝ)*(Real.log (M : ℝ))^9 *
    ((M : ℝ)^2/(R : ℝ)+(M : ℝ)^((8 : ℝ)/5)+2*(M : ℝ)^2/(P : ℝ))

theorem minorFourthMoment_le_chebyshev_budget (C : ℝ) (hC : 0 ≤ C)
    (hV : RealVaughanEstimate C) (M P R : ℕ) (hM : 3 ≤ M)
    (hP : 0 < P) (hPM : P ≤ M) (hR : 0 < R) :
    minorFourthMoment M P R ≤ chebyshevFourthBudget M P R C := by
  let Q : ℕ := ⌈(M : ℝ)/(P : ℝ)⌉₊
  have h := minorFourthMoment_le_chebyshev_L2 M P R
    ((minorEnvelope M R Q C)^2) (sq_nonneg _) (by
      intro x hx
      have hb := uniform_minor_bound_of_real_estimate C hC hV M P Q R hM hP hR rfl x hx
      nlinarith [norm_nonneg (exponentialSum M.succ x)])
  have hs := mul_le_mul_of_nonneg_right (minorEnvelope_sq_le M P Q R C hP hPM rfl)
    (show 0 ≤ chebyshevConstant*(M : ℝ)*Real.log (M : ℝ) by
      exact mul_nonneg (mul_nonneg chebyshevConstant_pos.le (Nat.cast_nonneg M))
        (Real.log_natCast_nonneg M))
  apply h.trans
  convert hs using 1
  unfold chebyshevFourthBudget
  ring

theorem evenBlock_exceptions_le_chebyshev_budget (C : ℝ) (hC : 0 ≤ C)
    (hV : RealVaughanEstimate C) (M P R : ℕ) (hM : 3 ≤ M)
    (hP : 0 < P) (hPM : P ≤ M) (hR : 0 < R)
    (hLarge : defectScaleThreshold ≤ M)
    (hMajor : ∀ N ∈ evenTargetBlock M,
      (M : ℝ)/14 ≤ twoScaleMajorIntegralReal M P R N) :
    (((evenTargetBlock M).filter (fun N => ¬ GoldbachAt N)).card : ℝ) ≤
      784*chebyshevFourthBudget M P R C/(M : ℝ)^2 := by
  have hm : (M : ℝ) ≠ 0 := by exact_mod_cast (show M ≠ 0 by omega)
  have hFourth : minorFourthMoment M P R ≤
      4*(M : ℝ)^2*(chebyshevFourthBudget M P R C/(4*(M : ℝ)^2)) := by
    rw [mul_div_cancel₀ _ (by positivity : (4*(M : ℝ)^2) ≠ 0)]
    exact minorFourthMoment_le_chebyshev_budget C hC hV M P R hM hP hPM hR
  have h := evenBlock_exceptions_card_le_3136_of_fourthMoment M P R
    (chebyshevFourthBudget M P R C/(4*(M : ℝ)^2)) hLarge hMajor hFourth
  calc
    _ ≤ 3136*(chebyshevFourthBudget M P R C/(4*(M : ℝ)^2)) := h
    _ = _ := by field_simp; ring

theorem budget_exact_log_relation (M P R : ℕ) (C : ℝ) :
    chebyshevFourthBudget M P R C * Real.log (M : ℝ) =
      chebyshevConstant * fourthMomentBudget M P R C := by
  unfold chebyshevFourthBudget fourthMomentBudget
  ring

theorem chebyshev_budget_le_old_budget (M P R : ℕ) (C : ℝ)
    (hlog : chebyshevConstant ≤ Real.log (M : ℝ)) :
    chebyshevFourthBudget M P R C ≤ fourthMomentBudget M P R C := by
  have hl : 0 ≤ Real.log (M : ℝ) := Real.log_natCast_nonneg M
  have hb : 0 ≤ 3*C^2*(M : ℝ)*(Real.log (M : ℝ))^9 *
      ((M : ℝ)^2/(R : ℝ)+(M : ℝ)^((8 : ℝ)/5)+2*(M : ℝ)^2/(P : ℝ)) := by
    positivity
  have h := mul_le_mul_of_nonneg_left hlog hb
  calc
    _ = (3*C^2*(M : ℝ)*(Real.log (M : ℝ))^9 *
      ((M : ℝ)^2/(R : ℝ)+(M : ℝ)^((8 : ℝ)/5)+2*(M : ℝ)^2/(P : ℝ))) *
        chebyshevConstant := by unfold chebyshevFourthBudget; ring
    _ ≤ (3*C^2*(M : ℝ)*(Real.log (M : ℝ))^9 *
      ((M : ℝ)^2/(R : ℝ)+(M : ℝ)^((8 : ℝ)/5)+2*(M : ℝ)^2/(P : ℝ))) *
        Real.log (M : ℝ) := h
    _ = _ := by unfold fourthMomentBudget; ring

end GoldbachCircleMethodChebyshevEnergyBudgetV1889
