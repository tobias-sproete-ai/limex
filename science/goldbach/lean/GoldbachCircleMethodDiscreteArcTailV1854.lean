import GoldbachCircleMethodDiscreteGeometricBoundV1853
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! # V1.8.54: local arc of the actual discrete main integrand.
Both complementary half-intervals are integrated. No pointwise error hypothesis
is assumed: the tail is derived from V53 and the exact N-1 coefficient in V52.+-/
open scoped BigOperators
open MeasureTheory
open GoldbachCircleMethodDiscreteMainKernelV1852
open GoldbachCircleMethodDiscreteGeometricBoundV1853

namespace GoldbachCircleMethodDiscreteArcTailV1854

noncomputable def realMainIntegrand (M N : ℕ) (β : ℝ) : ℂ :=
  discreteMainIntegrand M N (β : UnitAddCircle)

theorem realMainIntegrand_continuous (M N : ℕ) :
    Continuous (realMainIntegrand M N) := by
  have hc : Continuous (discreteMainIntegrand M N) :=
    (fourier (-(N : ℤ))).continuous.mul
      ((discreteMainPolynomial_continuous M).mul (discreteMainPolynomial_continuous M))
  exact hc.comp (AddCircle.continuous_mk' (1 : ℝ))

theorem full_interval_integral (M N : ℕ) (hN : 2 ≤ N) (hNM : N ≤ M) :
    (∫ β in (-1/2 : ℝ)..(1/2 : ℝ), realMainIntegrand M N β) = (N : ℂ)-1 := by
  have h := fourierCoeff_eq_intervalIntegral
    (fun x : UnitAddCircle => discreteMainPolynomial M x * discreteMainPolynomial M x)
    (N : ℤ) (-1/2)
  rw [discreteMainPolynomial_square_fourierCoeff M N hN hNM] at h
  norm_num [realMainIntegrand, discreteMainIntegrand] at h ⊢
  exact h.symm

noncomputable def localDiscreteMainIntegral (M N : ℕ) (t : ℝ) : ℂ :=
  ∫ β in -t..t, realMainIntegrand M N β

private theorem positive_tail_norm_bound (f : ℝ → ℂ) (t : ℝ)
    (ht : 0 < t) (htop : t ≤ 1/2)
    (hf : ∀ x ∈ Set.Ioc t (1/2), ‖f x‖ ≤ 1/(4*x^2)) :
    ‖∫ x in t..(1/2 : ℝ), f x‖ ≤ 1/(4*t) := by
  have hz : (0 : ℝ) ∉ Set.uIcc t (1/2) := by
    rw [Set.uIcc_of_le htop]
    intro h
    have := (Set.mem_Icc.mp h).1
    linarith
  have heq : (fun x : ℝ => 1/(4*x^2)) = fun x => (1/4 : ℝ)*x^(-2 : ℤ) := by
    funext x
    simp only [zpow_neg, zpow_ofNat]
    ring
  have hb : IntervalIntegrable (fun x : ℝ => 1/(4*x^2)) volume t (1/2) := by
    rw [heq]
    exact (intervalIntegral.intervalIntegrable_zpow (Or.inr hz)).const_mul (1/4)
  have hi : (∫ x in t..(1/2 : ℝ), (1 : ℝ)/(4*x^2)) = 1/(4*t)-1/2 := by
    rw [heq, intervalIntegral.integral_const_mul,
      integral_zpow (Or.inr ⟨by norm_num, hz⟩)]
    norm_num
    ring
  have hbound := intervalIntegral.norm_integral_le_of_norm_le htop
    (Filter.Eventually.of_forall hf) hb
  rw [hi] at hbound
  linarith

theorem localDiscreteMainIntegral_tail_bound (M N : ℕ) (hN : 2 ≤ N) (hNM : N ≤ M)
    (t : ℝ) (ht : 0 < t) (htop : t ≤ 1/2) :
    ‖localDiscreteMainIntegral M N t - ((N : ℂ)-1)‖ ≤ 1/(2*t) := by
  let f := realMainIntegrand M N
  have hc : Continuous f := realMainIntegrand_continuous M N
  have hright : ‖∫ x in t..(1/2 : ℝ), f x‖ ≤ 1/(4*t) := by
    apply positive_tail_norm_bound f t ht htop
    intro x hx
    have hx0 : 0 < x := lt_trans ht hx.1
    simpa [f, realMainIntegrand, abs_of_pos hx0] using
      discreteMainIntegrand_norm_le M N x
        (by simpa [abs_of_pos hx0]) (by simpa [abs_of_pos hx0] using hx.2)
  have hleft : ‖∫ x in (-1/2 : ℝ)..(-t), f x‖ ≤ 1/(4*t) := by
    have hb : ‖∫ x in t..(1/2 : ℝ), f (-x)‖ ≤ 1/(4*t) := by
      apply positive_tail_norm_bound (fun x => f (-x)) t ht htop
      intro x hx
      have hx0 : 0 < x := lt_trans ht hx.1
      simpa [f, realMainIntegrand, abs_neg, abs_of_pos hx0] using
        discreteMainIntegrand_norm_le M N (-x)
          (by simpa [abs_neg, abs_of_pos hx0])
          (by simpa [abs_neg, abs_of_pos hx0] using hx.2)
    simpa only [intervalIntegral.integral_comp_neg, neg_div] using hb
  have hsplit :
      (∫ x in (-1/2 : ℝ)..(-t), f x) + localDiscreteMainIntegral M N t +
        (∫ x in t..(1/2 : ℝ), f x) = (N : ℂ)-1 := by
    rw [localDiscreteMainIntegral,
      intervalIntegral.integral_add_adjacent_intervals
        (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _),
      intervalIntegral.integral_add_adjacent_intervals
        (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)]
    exact full_interval_integral M N hN hNM
  have hdiff : localDiscreteMainIntegral M N t - ((N : ℂ)-1) =
      -((∫ x in (-1/2 : ℝ)..(-t), f x) + (∫ x in t..(1/2 : ℝ), f x)) := by
    linear_combination hsplit
  rw [hdiff, norm_neg]
  calc
    ‖(∫ x in (-1/2 : ℝ)..(-t), f x) + (∫ x in t..(1/2 : ℝ), f x)‖ ≤
      ‖∫ x in (-1/2 : ℝ)..(-t), f x‖ + ‖∫ x in t..(1/2 : ℝ), f x‖ := norm_add_le _ _
    _ ≤ 1/(4*t)+1/(4*t) := add_le_add hleft hright
    _ = 1/(2*t) := by ring

theorem localDiscreteMainIntegral_real_tail_bound (M N : ℕ)
    (hN : 2 ≤ N) (hNM : N ≤ M) (t : ℝ) (ht : 0 < t) (htop : t ≤ 1/2) :
    |(localDiscreteMainIntegral M N t).re - ((N : ℝ)-1)| ≤ 1/(2*t) := by
  calc
    |(localDiscreteMainIntegral M N t).re - ((N : ℝ)-1)| =
        |(localDiscreteMainIntegral M N t - ((N : ℂ)-1)).re| := by simp
    _ ≤ ‖localDiscreteMainIntegral M N t - ((N : ℂ)-1)‖ := Complex.abs_re_le_norm _
    _ ≤ 1/(2*t) := localDiscreteMainIntegral_tail_bound M N hN hNM t ht htop

end GoldbachCircleMethodDiscreteArcTailV1854
