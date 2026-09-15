import GoldbachCircleMethodDiscreteMainKernelV1852
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Complex.Trigonometric

/-! # V1.8.53: geometric bound for the actual discrete polynomial.
No continuous replacement. The singular bound is only asserted for 0<|β|≤1/2.
Local integration and the major-arc approximation remain separate.
-/
open scoped BigOperators
open GoldbachCircleMethodDiscreteMainKernelV1852

namespace GoldbachCircleMethodDiscreteGeometricBoundV1853

private theorem nat_character_pow (n : ℕ) (x : UnitAddCircle) :
    fourier (n : ℤ) x = (fourier 1 x) ^ n := by
  induction n with
  | zero => simp
  | succ n ih => simp only [Nat.cast_add, Nat.cast_one, fourier_add, pow_succ, ih]

theorem discreteMainPolynomial_geometric_identity (M : ℕ) (x : UnitAddCircle) :
    discreteMainPolynomial M x * (fourier 1 x - 1) =
      fourier ((M+1 : ℕ) : ℤ) x - fourier 1 x := by
  have hset : Finset.Icc 1 M = Finset.Ico 1 (M+1) := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  simp only [discreteMainPolynomial, nat_character_pow]
  rw [hset]
  simpa only [pow_one] using geom_sum_Ico_mul (fourier 1 x) (show 1 ≤ M+1 by omega)

theorem discreteMainPolynomial_norm_product_le_two (M : ℕ) (x : UnitAddCircle) :
    ‖discreteMainPolynomial M x‖ * ‖fourier 1 x - 1‖ ≤ 2 := by
  rw [← norm_mul, discreteMainPolynomial_geometric_identity]
  calc
    ‖fourier ((M+1 : ℕ) : ℤ) x - fourier 1 x‖ ≤
        ‖fourier ((M+1 : ℕ) : ℤ) x‖ + ‖fourier 1 x‖ := norm_sub_le _ _
    _ = 2 := by simp only [fourier_apply, Circle.norm_coe]; norm_num

theorem character_gap_ge_four_abs (β : ℝ) (hβ : |β| ≤ 1/2) :
    4 * |β| ≤ ‖fourier 1 (β : UnitAddCircle) - 1‖ := by
  have hexp : fourier 1 (β : UnitAddCircle) =
      Complex.exp (Complex.I * ((2 * Real.pi * β : ℝ) : ℂ)) := by
    rw [fourier_coe_apply]
    norm_num
    congr 1
    ring
  have hnorm : ‖fourier 1 (β : UnitAddCircle) - 1‖ =
      2 * |Real.sin (Real.pi * β)| := by
    rw [hexp, Complex.norm_exp_I_mul_ofReal_sub_one]
    rw [show (2 * Real.pi * β) / 2 = Real.pi * β by ring]
    simp [Real.norm_eq_abs]
  have harg : |Real.pi * β| ≤ Real.pi / 2 := by
    rw [abs_mul, abs_of_pos Real.pi_pos]
    nlinarith [Real.pi_pos]
  have hj := Real.mul_abs_le_abs_sin harg
  rw [abs_mul, abs_of_pos Real.pi_pos] at hj
  have hcancel : 2 / Real.pi * (Real.pi * |β|) = 2 * |β| := by
    field_simp
  rw [hcancel] at hj
  rw [hnorm]
  linarith

theorem discreteMainPolynomial_norm_le (M : ℕ) (β : ℝ)
    (hβ0 : 0 < |β|) (hβ : |β| ≤ 1/2) :
    ‖discreteMainPolynomial M (β : UnitAddCircle)‖ ≤ 1 / (2 * |β|) := by
  have hgap := character_gap_ge_four_abs β hβ
  have hprod := discreteMainPolynomial_norm_product_le_two M (β : UnitAddCircle)
  have hmul := mul_le_mul_of_nonneg_left hgap
    (norm_nonneg (discreteMainPolynomial M (β : UnitAddCircle)))
  apply (le_div_iff₀ (by positivity : 0 < 2 * |β|)).mpr
  nlinarith

theorem discreteMainIntegrand_norm_le (M N : ℕ) (β : ℝ)
    (hβ0 : 0 < |β|) (hβ : |β| ≤ 1/2) :
    ‖discreteMainIntegrand M N (β : UnitAddCircle)‖ ≤ 1 / (4 * |β| ^ 2) := by
  have hV := discreteMainPolynomial_norm_le M β hβ0 hβ
  calc
    ‖discreteMainIntegrand M N (β : UnitAddCircle)‖ =
        ‖discreteMainPolynomial M (β : UnitAddCircle)‖ ^ 2 := by
      simp only [discreteMainIntegrand, norm_mul, fourier_apply, Circle.norm_coe, one_mul,
        pow_two]
    _ ≤ (1 / (2 * |β|)) ^ 2 := by nlinarith [norm_nonneg (discreteMainPolynomial M (β : UnitAddCircle))]
    _ = 1 / (4 * |β| ^ 2) := by ring

end GoldbachCircleMethodDiscreteGeometricBoundV1853
