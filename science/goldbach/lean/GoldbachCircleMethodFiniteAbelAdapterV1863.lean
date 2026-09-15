import GoldbachCircleMethodActualMajorReserveV1862
import Mathlib.Algebra.BigOperators.Module

/-! # V1.8.63: finite Abel adapter, with the prefix estimate left explicit.
No Siegel-Walfisz theorem or new analytic bound is asserted.
-/
open GoldbachCircleMethodDiscreteMainKernelV1852
open GoldbachCircleMethodFourierIdentityV171
open GoldbachCircleMethodShiftedClosedArcModelV1858
open GoldbachCircleMethodMajorMinorPartitionV172
open GoldbachCircleMethodTwoScaleMaskAdapterV1829

namespace GoldbachCircleMethodFiniteAbelAdapterV1863

theorem character_gap_le_two_pi_abs (β : ℝ) :
    ‖fourier 1 (β : UnitAddCircle) - 1‖ ≤ 2*Real.pi*|β| := by
  have hexp : fourier 1 (β : UnitAddCircle) =
      Complex.exp (Complex.I * ((2 * Real.pi * β : ℝ) : ℂ)) := by
    rw [fourier_coe_apply]
    norm_num
    congr 1
    ring
  rw [hexp]
  have h := Real.norm_exp_I_mul_ofReal_sub_one_le (x := 2*Real.pi*β)
  simpa only [Real.norm_eq_abs, abs_mul, abs_of_pos Real.pi_pos,
    abs_of_pos (by norm_num : (0 : ℝ) < 2)] using h

theorem successive_phase_gap (k : ℕ) (β : ℝ) :
    ‖fourier ((k+2 : ℕ) : ℤ) (β : UnitAddCircle) -
      fourier ((k+1 : ℕ) : ℤ) (β : UnitAddCircle)‖ ≤ 2*Real.pi*|β| := by
  have hi : ((k+2 : ℕ) : ℤ) = ((k+1 : ℕ) : ℤ)+1 := by omega
  rw [hi, fourier_add]
  rw [show fourier ((k+1 : ℕ) : ℤ) (β : UnitAddCircle)*fourier 1 (β : UnitAddCircle) -
      fourier ((k+1 : ℕ) : ℤ) (β : UnitAddCircle) =
        fourier ((k+1 : ℕ) : ℤ) (β : UnitAddCircle)*(fourier 1 (β : UnitAddCircle)-1)
          by ring, norm_mul]
  simpa only [fourier_apply, Circle.norm_coe, one_mul] using character_gap_le_two_pi_abs β

theorem finite_abel_norm_bound (M : ℕ) (g : ℕ → ℂ) (β D : ℝ) (hD : 0 ≤ D)
    (hprefix : ∀ k ≤ M, ‖∑ n ∈ Finset.range k, g n‖ ≤ D) :
    ‖∑ n ∈ Finset.range M, fourier ((n+1 : ℕ) : ℤ) (β : UnitAddCircle)*g n‖ ≤
      (1+2*Real.pi*(M : ℝ)*|β|)*D := by
  have hab := Finset.sum_range_by_parts
    (fun n => fourier ((n+1 : ℕ) : ℤ) (β : UnitAddCircle)) g M
  simp only [smul_eq_mul] at hab
  rw [hab]
  have ht : ‖fourier (((M-1)+1 : ℕ) : ℤ) (β : UnitAddCircle)*
      (∑ n ∈ Finset.range M, g n)‖ ≤ D := by
    simpa only [norm_mul, fourier_apply, Circle.norm_coe, one_mul] using hprefix M le_rfl
  have hr : ‖∑ n ∈ Finset.range (M-1),
      (fourier (((n+1)+1 : ℕ) : ℤ) (β : UnitAddCircle)-
        fourier ((n+1 : ℕ) : ℤ) (β : UnitAddCircle)) *
          (∑ j ∈ Finset.range (n+1), g j)‖ ≤ (M : ℝ)*(2*Real.pi*|β| * D) := by
    calc
      _ ≤ ∑ n ∈ Finset.range (M-1),
          ‖(fourier (((n+1)+1 : ℕ) : ℤ) (β : UnitAddCircle)-
            fourier ((n+1 : ℕ) : ℤ) (β : UnitAddCircle)) *
              (∑ j ∈ Finset.range (n+1), g j)‖ := norm_sum_le _ _
      _ ≤ ∑ _n ∈ Finset.range (M-1), 2*Real.pi*|β| * D := by
        apply Finset.sum_le_sum
        intro n hn
        have hnM : n+1 ≤ M := by have := Finset.mem_range.mp hn; omega
        rw [norm_mul]
        exact mul_le_mul (successive_phase_gap n β) (hprefix (n+1) hnM)
          (norm_nonneg _) (by positivity)
      _ ≤ (M : ℝ)*(2*Real.pi*|β| * D) := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.sub_le M 1) (by positivity)
  calc
    _ ≤ D+(M : ℝ)*(2*Real.pi*|β| * D) := (norm_sub_le _ _).trans (add_le_add ht hr)
    _ = _ := by ring

theorem sum_range_succ_index (M : ℕ) (f : ℕ → ℂ) :
    (∑ n ∈ Finset.range M, f (n+1)) = ∑ n ∈ Finset.Icc 1 M, f n := by
  apply Finset.sum_bij (fun n _ => n+1)
  · intro n hn
    have := Finset.mem_range.mp hn
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  · intro a _ b _ h
    omega
  · intro b hb
    have hb' := Finset.mem_Icc.mp hb
    exact ⟨b-1, Finset.mem_range.mpr (by omega), by omega⟩
  · intro n _
    rfl

theorem exponentialSum_eq_shifted_sum (M : ℕ) (c : UnitAddCircle) :
    exponentialSum M.succ c = ∑ n ∈ Finset.range M,
      (ArithmeticFunction.vonMangoldt (n+1) : ℂ)*fourier ((n+1 : ℕ) : ℤ) c := by
  simp only [exponentialSum, ContinuousMap.sum_apply, ContinuousMap.smul_apply, smul_eq_mul]
  rw [Finset.sum_range_succ']
  simp

theorem prefix_discrepancy_identity (M : ℕ) (c : UnitAddCircle) (z : ℂ) :
    (∑ n ∈ Finset.range M,
      ((ArithmeticFunction.vonMangoldt (n+1) : ℂ)*fourier ((n+1 : ℕ) : ℤ) c-z)) =
        exponentialSum M.succ c-z*(M : ℂ) := by
  rw [Finset.sum_sub_distrib, ← exponentialSum_eq_shifted_sum]
  simp [mul_comm]

theorem shifted_discrepancy_identity (M : ℕ) (c : UnitAddCircle) (β : ℝ) (z : ℂ) :
    (∑ n ∈ Finset.range M, fourier ((n+1 : ℕ) : ℤ) (β : UnitAddCircle)*
      ((ArithmeticFunction.vonMangoldt (n+1) : ℂ)*fourier ((n+1 : ℕ) : ℤ) c-z)) =
        exponentialSum M.succ (c+(β : UnitAddCircle))-z*discreteMainPolynomial M
          (β : UnitAddCircle) := by
  rw [exponentialSum_eq_shifted_sum]
  unfold discreteMainPolynomial
  rw [← sum_range_succ_index, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n _
  rw [fourier_argument_add]
  ring

theorem actual_shifted_error_from_prefix (M : ℕ) (c : UnitAddCircle) (β D : ℝ)
    (z : ℂ) (hD : 0 ≤ D)
    (hprefix : ∀ k ≤ M, ‖exponentialSum k.succ c-z*(k : ℂ)‖ ≤ D) :
    ‖exponentialSum M.succ (c+(β : UnitAddCircle))-z*discreteMainPolynomial M
      (β : UnitAddCircle)‖ ≤ (1+2*Real.pi*(M : ℝ)*|β|)*D := by
  rw [← shifted_discrepancy_identity]
  apply finite_abel_norm_bound M _ β D hD
  intro k hk
  rw [prefix_discrepancy_identity]
  exact hprefix k hk

theorem closedBall_real_lift (c x : UnitAddCircle) (t : ℝ)
    (hx : x ∈ Metric.closedBall c t) :
    ∃ β : ℝ, |β| ≤ t ∧ x = c+(β : UnitAddCircle) := by
  let b := AddCircle.equivIco (1 : ℝ) (-(1/2 : ℝ)) (x-c)
  have hb : |(b : ℝ)| ≤ (1 : ℝ)/2 := by
    rcases b.property with ⟨hl, hr⟩
    exact abs_le.mpr ⟨hl, by linarith⟩
  have he : ((b : ℝ) : UnitAddCircle) = x-c := AddCircle.coe_equivIco
  have hn : ‖((b : ℝ) : UnitAddCircle)‖ = |(b : ℝ)| :=
    (AddCircle.norm_coe_eq_abs_iff (1 : ℝ) (by norm_num)).mpr (by simpa using hb)
  have ht : |(b : ℝ)| ≤ t := by
    rw [← hn, he]
    simpa only [dist_eq_norm] using Metric.mem_closedBall.mp hx
  exact ⟨b, ht, by rw [he]; abel⟩

theorem actual_closed_ball_error_from_prefix (M : ℕ) (c x : UnitAddCircle)
    (t D : ℝ) (z : ℂ) (hD : 0 ≤ D) (hx : x ∈ Metric.closedBall c t)
    (hprefix : ∀ k ≤ M, ‖exponentialSum k.succ c-z*(k : ℂ)‖ ≤ D) :
    ‖exponentialSum M.succ x-z*discreteMainPolynomial M (x-c)‖ ≤
      (1+2*Real.pi*(M : ℝ)*t)*D := by
  obtain ⟨β, hβ, he⟩ := closedBall_real_lift c x t hx
  have h := actual_shifted_error_from_prefix M c β D z hD hprefix
  have he' : x-c = (β : UnitAddCircle) := by rw [he]; abel
  rw [← he, ← he'] at h
  apply h.trans
  apply mul_le_mul_of_nonneg_right _ hD
  linarith [mul_le_mul_of_nonneg_left hβ (by positivity : 0 ≤ 2*Real.pi*(M : ℝ))]

theorem original_arc_error_from_prefix (M P R : ℕ) (hM : 0 < M)
    (i : ReducedRationalIndex R) (x : UnitAddCircle) (D : ℝ) (hD : 0 ≤ D)
    (hx : x ∈ Metric.closedBall (majorArcCenter i) (twoScaleArcRadius M P i))
    (hprefix : ∀ k ≤ M, ‖exponentialSum k.succ (majorArcCenter i)-
      (((ArithmeticFunction.moebius i.val.1 : ℤ) : ℂ)/(Nat.totient i.val.1 : ℂ)) *
        (k : ℂ)‖ ≤ D) :
    ‖exponentialSum M.succ x-
      (((ArithmeticFunction.moebius i.val.1 : ℤ) : ℂ)/(Nat.totient i.val.1 : ℂ)) *
        discreteMainPolynomial M (x-majorArcCenter i)‖ ≤
      (1+2*Real.pi*(P : ℝ))*D := by
  have h := actual_closed_ball_error_from_prefix M (majorArcCenter i) x
    (twoScaleArcRadius M P i) D _ hD hx hprefix
  have hq : (1 : ℝ) ≤ i.val.1 := by exact_mod_cast index_denominator_pos i
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  have hrad : (M : ℝ)*twoScaleArcRadius M P i ≤ P := by
    unfold twoScaleArcRadius
    rw [← mul_div_assoc, div_le_iff₀ (mul_pos (by linarith : (0 : ℝ) < i.val.1) hM')]
    nlinarith [mul_le_mul_of_nonneg_right hq (show 0 ≤ (M : ℝ)*(P : ℝ) by positivity)]
  apply h.trans
  apply mul_le_mul_of_nonneg_right _ hD
  nlinarith [Real.pi_pos]

end GoldbachCircleMethodFiniteAbelAdapterV1863
