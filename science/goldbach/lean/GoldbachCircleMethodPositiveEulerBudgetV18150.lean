import GoldbachCircleMethodLocalEulerRadicalBoundsV18149
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries

set_option autoImplicit false
open scoped BigOperators Classical
open MeasureTheory
open GoldbachCircleMethodLocalEulerRadicalBoundsV18149
namespace GoldbachCircleMethodPositiveEulerBudgetV18150

/-- Explicit integral-test constant, not O-notation. -/
theorem pseries_explicit_bound {σ : ℝ} (hσ : 0 < σ) :
    (∑' n : ℕ, (n : ℝ)^(-(1+σ))) ≤ 1+1/σ := by
  have ha : -(1+σ) < -1 := by linarith
  have hi := integrableOn_Ioi_rpow_of_lt ha (show (0 : ℝ) < 1 by norm_num)
  have hanti : AntitoneOn (fun x : ℝ => x^(-(1+σ))) (Set.Ici 1) := by
    intro x hx y hy hxy
    have hx1 : 1 ≤ x := hx
    exact Real.rpow_le_rpow_of_nonpos (by linarith) hxy (by linarith)
  have ht := AntitoneOn.tsum_comp_add_le_integral
    (f := fun x : ℝ => x^(-(1+σ))) 1
    (by simpa only [Nat.cast_one] using hanti)
    (by simpa only [Nat.cast_one] using hi) (fun x hx =>
    Real.rpow_nonneg (by
      have hx1 : (1 : ℝ) < x := by simpa using hx
      linarith) _)
  have hint : (∫ x : ℝ in Set.Ioi 1, x^(-(1+σ))) = 1/σ := by
    rw [integral_Ioi_rpow_of_lt ha (show (0 : ℝ) < 1 by norm_num),Real.one_rpow]
    have he : -(1+σ)+1 = -σ := by ring
    rw [he]
    ring
  simp only [Nat.cast_one] at ht
  rw [hint] at ht
  have hs : Summable (fun n : ℕ => (n : ℝ)^(-(1+σ))) :=
    Real.summable_nat_rpow.mpr ha
  have hbase : (∑ n ∈ Finset.range 2, (n : ℝ)^(-(1+σ))) = 1 := by
    rw [show Finset.range 2 = ({0,1} : Finset ℕ) by decide]
    rw [Finset.sum_pair (by decide : (0 : ℕ) ≠ 1)]
    simp only [Nat.cast_zero,Nat.cast_one,Real.one_rpow,
      Real.zero_rpow (by linarith : -(1+σ) ≠ 0),zero_add]
  rw [← hs.sum_add_tsum_nat_add 2,hbase]
  simpa only [Nat.add_assoc,Nat.one_add] using add_le_add_right ht 1

theorem reciprocal_telescope_range (K : ℕ) :
    (∑ k ∈ Finset.range K, 1/(((k : ℝ)+1)*((k : ℝ)+2))) = 1-1/((K : ℝ)+1) := by
  induction K with
  | zero => norm_num
  | succ K ih =>
    rw [Finset.sum_range_succ,ih]
    push_cast
    have h1 : (K : ℝ)+1 ≠ 0 := by positivity
    have h2 : (K : ℝ)+2 ≠ 0 := by positivity
    field_simp [h1,h2]
    ring

theorem finite_prime_reciprocal_budget (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    (∑ p ∈ S, 1/((p : ℝ)*((p : ℝ)-1))) ≤ 1 := by
  let T := S.image (fun p => p-2)
  have he : (∑ p ∈ S, 1/((p : ℝ)*((p : ℝ)-1))) =
      ∑ k ∈ T, 1/(((k : ℝ)+1)*((k : ℝ)+2)) := by
    dsimp [T]
    rw [Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro p hp
      rw [Nat.cast_sub (hS p hp).two_le]
      push_cast
      congr 1
      ring
    · intro p hp q hq heq
      change p-2 = q-2 at heq
      have hp2 := (hS p hp).two_le
      have hq2 := (hS q hq).two_le
      omega
  have hsub : T ⊆ Finset.range (T.sup id+1) := by
    intro k hk
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_sup (f := id) hk))
  rw [he]
  calc
    _ ≤ ∑ k ∈ Finset.range (T.sup id+1), 1/(((k : ℝ)+1)*((k : ℝ)+2)) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun k _ _ => by positivity)
    _ = _ := reciprocal_telescope_range _
    _ ≤ 1 := sub_le_self _ (by positivity)

theorem positiveLocal_nonneg {p : ℝ} (hp : 1 < p) (σ : ℝ) :
    0 ≤ positiveLocal p σ := by
  unfold positiveLocal
  exact add_nonneg zero_le_one (div_nonneg zero_le_one
    (mul_nonneg (by linarith) (Real.rpow_pos_of_pos (by linarith) _).le))

theorem zeta_correction_factor_pos {p σ : ℝ} (hp : 1 < p) (hσ : 0 ≤ σ) :
    0 < 1-1/p^(1+σ) := by
  have hpow := Real.one_lt_rpow hp (show 0 < 1+σ by linarith)
  have hpos : 0 < p^(1+σ) := by linarith
  have hi : 1/p^(1+σ) < 1 := (div_lt_one hpos).mpr hpow
  linarith

/-- Uniform finite product budget underlying the sharp Euler bound. -/
theorem finite_positive_euler_correction_budget (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime) {σ : ℝ} (hσ : 0 ≤ σ) :
    (∏ p ∈ S, positiveLocal (p : ℝ) σ * (1-1/(p : ℝ)^(1+σ))) ≤ Real.exp 1 := by
  calc
    _ ≤ ∏ p ∈ S, Real.exp (1/((p : ℝ)*((p : ℝ)-1))) :=
      Finset.prod_le_prod
        (fun p hp => mul_nonneg (positiveLocal_nonneg (by exact_mod_cast (hS p hp).one_lt) σ)
          (zeta_correction_factor_pos (by exact_mod_cast (hS p hp).one_lt) hσ).le)
        (fun p hp => positiveLocal_correction_le_exp (by exact_mod_cast (hS p hp).one_lt) σ)
    _ = Real.exp (∑ p ∈ S, 1/((p : ℝ)*((p : ℝ)-1))) := (Real.exp_sum _ _).symm
    _ ≤ _ := Real.exp_le_exp.mpr (finite_prime_reciprocal_budget S hS)

end GoldbachCircleMethodPositiveEulerBudgetV18150
