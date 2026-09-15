import GoldbachCircleMethodActualOperatorErrorTransferV1861

/-! # V1.8.62: finite mask mass and conditional actual major reserve.
The actual rational approximation remains an explicit analytic premise.
-/
open MeasureTheory
open GoldbachCircleMethodOriginalMaskModelBindingV1859
open GoldbachCircleMethodMajorMinorPartitionV172
open GoldbachCircleMethodTwoScaleMaskAdapterV1829
open GoldbachCircleMethodTwoScaleIntegralPartitionV1831
open GoldbachCircleMethodDiscreteMainKernelV1852
open GoldbachCircleMethodFourierIdentityV171
open GoldbachCircleMethodDiscreteArcModelReserveV1855
open GoldbachCircleMethodActualOperatorErrorTransferV1861

namespace GoldbachCircleMethodActualMajorReserveV1862

theorem sum_original_indices_real (R : ℕ) (f : ℕ → ℕ → ℝ) :
    (∑ i : ReducedRationalIndex R, f i.val.1 i.val.2) =
      ∑ q : Denominator R, ∑ a : ZMod q.val, if IsUnit a then f q.val a.val else 0 := by
  classical
  have h := congrArg Complex.re (sum_original_indices R (fun q a => (f q a : ℂ)))
  simpa only [Complex.re_sum, apply_ite, Complex.ofReal_re, Complex.zero_re] using h

theorem original_radii_mass_bound (M P R : ℕ) (hM : 0 < M) :
    (∑ i : ReducedRationalIndex R, 2*twoScaleArcRadius M P i) ≤
      2*(P : ℝ)*(R : ℝ)/(M : ℝ) := by
  classical
  unfold twoScaleArcRadius
  rw [sum_original_indices_real R (fun q _ => 2*((P : ℝ)/((q : ℝ)*(M : ℝ))))]
  have hden (q : Denominator R) :
      (∑ a : ZMod q.val, if IsUnit a then 2*((P : ℝ)/((q.val : ℝ)*(M : ℝ))) else 0)
        ≤ 2*(P : ℝ)/(M : ℝ) := by
    have hq : (0 : ℝ) < q.val := by exact_mod_cast (Finset.mem_Icc.mp q.property).1
    have hM' : (0 : ℝ) < M := by exact_mod_cast hM
    calc
      _ ≤ ∑ _a : ZMod q.val, 2*((P : ℝ)/((q.val : ℝ)*(M : ℝ))) := by
        apply Finset.sum_le_sum
        intro a _
        split_ifs
        · rfl
        · positivity
      _ = 2*(P : ℝ)/(M : ℝ) := by
        simp only [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
        field_simp
  calc
    _ ≤ ∑ _q : Denominator R, 2*(P : ℝ)/(M : ℝ) :=
      Finset.sum_le_sum (fun q _ => hden q)
    _ = 2*(P : ℝ)*(R : ℝ)/(M : ℝ) := by
      calc
        _ = ∑ _q ∈ Finset.Icc 1 R, 2*(P : ℝ)/(M : ℝ) :=
          Finset.sum_coe_sort (Finset.Icc 1 R) (fun _ => 2*(P : ℝ)/(M : ℝ))
        _ = _ := by simp; ring

theorem original_major_real_error_finite_bound (M P R N : ℕ)
    (hR : 1 ≤ R) (hscale : 2*P*R < M) (ε : ℝ) (hε : 0 ≤ ε)
    (happrox : ∀ i : ReducedRationalIndex R,
      ∀ x ∈ Metric.closedBall (majorArcCenter i) (twoScaleArcRadius M P i),
        ‖exponentialSum M.succ x -
          (((ArithmeticFunction.moebius i.val.1 : ℤ) : ℂ)/(Nat.totient i.val.1 : ℂ)) *
            discreteMainPolynomial M (x-majorArcCenter i)‖ ≤ ε) :
    |twoScaleMajorIntegralReal M P R N - discreteArcMainModel M N R P| ≤
      (2*(M : ℝ)*ε+ε^2)*(2*(P : ℝ)*(R : ℝ)/(M : ℝ)) := by
  exact (original_major_real_error_bound M P R N hR hscale ε happrox).trans
    (mul_le_mul_of_nonneg_left (original_radii_mass_bound M P R (by omega))
      (by positivity))

theorem actual_major_lower_bound (M P R N : ℕ)
    (hN : 2 ≤ N) (hNM : N ≤ M) (hEven : Even N)
    (hR : 1 ≤ R) (hP : 0 < P) (hscale : 2*P*R < M) (ε : ℝ) (hε : 0 ≤ ε)
    (happrox : ∀ i : ReducedRationalIndex R,
      ∀ x ∈ Metric.closedBall (majorArcCenter i) (twoScaleArcRadius M P i),
        ‖exponentialSum M.succ x -
          (((ArithmeticFunction.moebius i.val.1 : ℤ) : ℂ)/(Nat.totient i.val.1 : ℂ)) *
            discreteMainPolynomial M (x-majorArcCenter i)‖ ≤ ε) :
    ((N : ℝ)-1)*(2/7 : ℝ) - ((M : ℝ)/(2*(P : ℝ)))*(R : ℝ)^2 -
      (2*(M : ℝ)*ε+ε^2)*(2*(P : ℝ)*(R : ℝ)/(M : ℝ)) ≤
        twoScaleMajorIntegralReal M P R N := by
  have hcap : 2*(P : ℝ) ≤ M := by
    exact_mod_cast (show 2*P ≤ M by nlinarith)
  have hmodel := discreteArcMainModel_lower_bound M N R hN hNM hEven hR
    (P : ℝ) (by exact_mod_cast hP) hcap
  have herr := (abs_le.mp
    (original_major_real_error_finite_bound M P R N hR hscale ε hε happrox)).1
  linarith

theorem actual_major_ge_one_fourteenth (M P R N : ℕ)
    (hN : 2 ≤ N) (hNM : N ≤ M) (hEven : Even N)
    (hR : 1 ≤ R) (hP : 0 < P) (hscale : 2*P*R < M)
    (hblock : (M : ℝ)/2 ≤ N) (ε : ℝ) (hε : 0 ≤ ε)
    (happrox : ∀ i : ReducedRationalIndex R,
      ∀ x ∈ Metric.closedBall (majorArcCenter i) (twoScaleArcRadius M P i),
        ‖exponentialSum M.succ x -
          (((ArithmeticFunction.moebius i.val.1 : ℤ) : ℂ)/(Nat.totient i.val.1 : ℂ)) *
            discreteMainPolynomial M (x-majorArcCenter i)‖ ≤ ε)
    (hbudget : (2/7 : ℝ) + ((M : ℝ)/(2*(P : ℝ)))*(R : ℝ)^2 +
      (2*(M : ℝ)*ε+ε^2)*(2*(P : ℝ)*(R : ℝ)/(M : ℝ)) ≤ (M : ℝ)/14) :
    (M : ℝ)/14 ≤ twoScaleMajorIntegralReal M P R N := by
  have h := actual_major_lower_bound M P R N hN hNM hEven hR hP hscale ε hε happrox
  linarith

end GoldbachCircleMethodActualMajorReserveV1862
