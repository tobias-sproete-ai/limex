import GoldbachCircleMethodUncorrectedSupportedErrorConvolutionV18184
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic

set_option autoImplicit false
open scoped BigOperators Classical
open GoldbachCircleMethodFiniteWindowConvolutionV18119

namespace GoldbachCircleMethodActualWindowSourceNormalizationV18185

theorem nat_abs_sub_le_width_iff (N U : ℕ) {H : ℝ} (hH : 0 ≤ H) :
    |(N : ℝ) - (U : ℝ)| ≤ H ↔ N - ⌊H⌋₊ ≤ U ∧ U ≤ N + ⌊H⌋₊ := by
  by_cases hUN : U ≤ N
  · have heq : |(N : ℝ) - (U : ℝ)| = ((N - U : ℕ) : ℝ) := by
      rw [Nat.cast_sub hUN, abs_of_nonneg]
      exact sub_nonneg.mpr (by exact_mod_cast hUN)
    rw [heq, ← Nat.le_floor_iff hH]
    omega
  · have hNU : N ≤ U := by omega
    have heq : |(N : ℝ) - (U : ℝ)| = ((U - N : ℕ) : ℝ) := by
      rw [Nat.cast_sub hNU, abs_of_nonpos]
      · ring
      · exact sub_nonpos.mpr (by exact_mod_cast hNU)
    rw [heq, ← Nat.le_floor_iff hH]
    omega

theorem centeredWindow_eq_nat_inter (J : Finset ℕ) (N : ℕ) {H : ℝ}
    (hH : 0 ≤ H) :
    centeredWindow J N H = J ∩ Finset.Icc (N - ⌊H⌋₊) (N + ⌊H⌋₊) := by
  ext U
  simp only [mem_centeredWindow, Finset.mem_inter, Finset.mem_Icc,
    nat_abs_sub_le_width_iff N U hH]

theorem block_centeredWindow_eq_Icc (M N : ℕ) {H : ℝ} (hH : 0 ≤ H) :
    centeredWindow (Finset.Ioc (M / 2) M) N H =
      Finset.Icc (max (M / 2 + 1) (N - ⌊H⌋₊)) (min M (N + ⌊H⌋₊)) := by
  ext U
  simp only [mem_centeredWindow, Finset.mem_Ioc, Finset.mem_Icc,
    max_le_iff, le_min_iff, nat_abs_sub_le_width_iff N U hH]
  omega

theorem centeredWindow_card_le (J : Finset ℕ) (N : ℕ) {H : ℝ}
    (hH : 0 ≤ H) :
    ((centeredWindow J N H).card : ℝ) ≤ 2 * H + 1 := by
  have hsub : centeredWindow J N H ⊆ Finset.Icc (N - ⌊H⌋₊) (N + ⌊H⌋₊) := by
    rw [centeredWindow_eq_nat_inter J N hH]
    exact Finset.inter_subset_right
  have hcard := Finset.card_le_card hsub
  rw [Nat.card_Icc] at hcard
  have hnat : (centeredWindow J N H).card ≤ 2 * ⌊H⌋₊ + 1 := by omega
  have hreal : ((centeredWindow J N H).card : ℝ) ≤ 2 * (⌊H⌋₊ : ℝ) + 1 := by
    exact_mod_cast hnat
  have hfloor := Nat.floor_le hH
  linarith

theorem centeredWindow_nonempty (J : Finset ℕ) (N : ℕ) {H : ℝ}
    (hH : 0 ≤ H) (hN : N ∈ J) : (centeredWindow J N H).Nonempty := by
  refine ⟨N, (mem_centeredWindow J N N H).mpr ⟨hN, ?_⟩⟩
  simpa using hH

theorem centeredWindow_normalization_le_two (J : Finset ℕ) (N : ℕ) {H : ℝ}
    (hH : 1 ≤ H) :
    (((centeredWindow J N H).card : ℝ) + H) / (2 * H) ≤ 2 := by
  have hH0 : 0 ≤ H := by linarith
  have hc := centeredWindow_card_le J N hH0
  apply (div_le_iff₀ (by positivity : 0 < 2 * H)).mpr
  linarith

theorem block_left_endpoint_admits_explicit_formula (M N : ℕ) {H : ℝ}
    (hM : 6 ≤ M) :
    (M : ℝ) / 3 ≤ ((max (M / 2 + 1) (N - ⌊H⌋₊) - 1 : ℕ) : ℝ) := by
  have hnat : M ≤ 3 * (max (M / 2 + 1) (N - ⌊H⌋₊) - 1) := by omega
  have hreal : (M : ℝ) ≤
      3 * ((max (M / 2 + 1) (N - ⌊H⌋₊) - 1 : ℕ) : ℝ) := by
    exact_mod_cast hnat
  linarith

/-- Exact algebraic comparison between the actual `2H` normalization and the
source normalization `#I+H`; no equality between cardinality and width is used. -/
theorem complex_window_normalization_identity (J : Finset ℕ) (N : ℕ)
    {H : ℝ} (hH : 1 ≤ H) (z : ℂ) :
    ‖(2 * (H : ℂ))⁻¹ * z‖ =
      ((((centeredWindow J N H).card : ℝ) + H) / (2 * H)) *
        (‖z‖ / (((centeredWindow J N H).card : ℝ) + H)) := by
  have hHpos : 0 < H := lt_of_lt_of_le (by norm_num) hH
  have hden : 0 < ((centeredWindow J N H).card : ℝ) + H := by positivity
  rw [norm_mul, norm_inv, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (le_of_lt hHpos)]
  norm_num
  field_simp

/-- A literal source-to-operator transfer for one actual complex window sum.
The normalized source estimate remains an explicit premise. -/
theorem complex_window_normalization_transfer (J : Finset ℕ) (N : ℕ)
    {H A : ℝ} (hH : 1 ≤ H) (z : ℂ)
    (hsource : ‖z‖ / (((centeredWindow J N H).card : ℝ) + H) ≤ A) :
    ‖(2 * (H : ℂ))⁻¹ * z‖ ≤ 2 * A := by
  rw [complex_window_normalization_identity J N hH z]
  have hden : 0 ≤ ‖z‖ / (((centeredWindow J N H).card : ℝ) + H) := by positivity
  calc
    _ ≤ 2 * (‖z‖ / (((centeredWindow J N H).card : ℝ) + H)) :=
      mul_le_mul_of_nonneg_right (centeredWindow_normalization_le_two J N hH) hden
    _ ≤ 2 * A := mul_le_mul_of_nonneg_left hsource (by norm_num)

end GoldbachCircleMethodActualWindowSourceNormalizationV18185
