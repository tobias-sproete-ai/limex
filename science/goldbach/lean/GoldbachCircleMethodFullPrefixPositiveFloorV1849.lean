import GoldbachCircleMethodFullSquarefreePrefixFloorV1848
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds

/-! # V1.8.49: numerical positivity and the full finite Fourier prefix.
No Major-Arc integral estimate or Goldbach existence assertion is made.
-/
open scoped BigOperators
namespace GoldbachCircleMethodFullPrefixPositiveFloorV1849
open GoldbachCircleMethodFullSquarefreeCarrierV1846
open GoldbachCircleMethodFullSquarefreePrefixFloorV1848

theorem kappa_gt_two_sevenths :
    (2 : ℝ) / 7 < 2 - Real.exp (Real.pi ^ 2 / 24) := by
  have hpi := Real.pi_lt_d2
  have hpi0 := Real.pi_pos
  have hangle : Real.pi ^ 2 / 24 < (1 : ℝ) / 2 := by nlinarith
  have hexp : Real.exp ((1 : ℝ) / 2) ^ 2 = Real.exp 1 := by
    rw [pow_two, ← Real.exp_add]
    norm_num
  have hpos := Real.exp_pos ((1 : ℝ) / 2)
  have hbound := Real.exp_one_lt_d9
  have hhalf : Real.exp ((1 : ℝ) / 2) < (12 : ℝ) / 7 := by nlinarith
  have hmono := Real.exp_lt_exp.mpr hangle
  linarith

theorem kappa_pos : 0 < 2 - Real.exp (Real.pi ^ 2 / 24) := by
  linarith [kappa_gt_two_sevenths]

theorem one_mem_dividingSquarefreePrefix (N : ℕ) {H : ℕ} (hH : 1 ≤ H) :
    1 ∈ dividingSquarefreePrefix N H := by
  apply Finset.mem_filter.mpr
  exact ⟨mem_fullSquarefreePrefix.mpr ⟨hH, squarefree_one⟩, one_dvd N⟩

theorem divisor_mass_ge_one (N : ℕ) {H : ℕ} (hH : 1 ≤ H) :
    (1 : ℝ) ≤ ∑ a ∈ dividingSquarefreePrefix N H, 1 / (Nat.totient a : ℝ) := by
  have h := Finset.single_le_sum
    (f := fun a : ℕ => (1 : ℝ) / (Nat.totient a : ℝ))
    (fun a _ => by positivity) (one_mem_dividingSquarefreePrefix N hH)
  simpa using h

theorem fullSquarefreeFourierPrefix_ge_kappa {N H : ℕ}
    (hEven : Even N) (hH : 1 ≤ H) :
    2 - Real.exp (Real.pi ^ 2 / 24) ≤ fullSquarefreeFourierPrefix N H := by
  have hmass := divisor_mass_ge_one N hH
  have hfloor := fullSquarefreeFourierPrefix_ge_kappa_times_divisor_mass
    (R := H) hEven le_rfl
  have hmul := mul_le_mul_of_nonneg_left hmass (le_of_lt kappa_pos)
  simpa only [mul_one] using hmul.trans hfloor

theorem fullSquarefreeFourierPrefix_gt_two_sevenths {N H : ℕ}
    (hEven : Even N) (hH : 1 ≤ H) :
    (2 : ℝ) / 7 < fullSquarefreeFourierPrefix N H :=
  kappa_gt_two_sevenths.trans_le (fullSquarefreeFourierPrefix_ge_kappa hEven hH)

end GoldbachCircleMethodFullPrefixPositiveFloorV1849
