import GoldbachCircleMethodArithmeticSupportedPowersetV18438
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Topology.Algebra.InfiniteSum.Order

/-!
# Goldbach V1.8.439: uniform Euler-kernel bound

The odd-prime square weights are dominated by the convergent p-series over all
natural indices.  Their `1 + weight` family is therefore multipliable, and its
infinite product supplies one uniform finite constant for every supported
kernel prefix.  A numerical sharpening such as `C < 2` is deliberately not
needed for this closure theorem.

This closes the Euler-kernel mean-value subproblem only.  It does not prove the
analytic source estimates required by the binary Goldbach conjecture.
-/

set_option autoImplicit false

open scoped BigOperators Classical Topology

namespace GoldbachCircleMethodArithmeticEulerKernelBoundV18439

open GoldbachCircleMethodArithmeticSupportedKernelV18436
open GoldbachCircleMethodArithmeticSupportedPowersetV18438

noncomputable def oddPrimeSquareWeight (n : ℕ) : ℝ :=
  if n.Prime ∧ 2 < n then (3 : ℝ) / (n : ℝ) ^ 2 else 0

theorem oddPrimeSquareWeight_nonneg (n : ℕ) :
    0 ≤ oddPrimeSquareWeight n := by
  unfold oddPrimeSquareWeight
  split_ifs
  · positivity
  · exact le_rfl

theorem oddPrimeSquareWeight_le_pSeriesMajorant (n : ℕ) :
    oddPrimeSquareWeight n ≤ (3 : ℝ) * (1 / (n : ℝ) ^ 2) := by
  unfold oddPrimeSquareWeight
  split_ifs
  · simpa only [div_eq_mul_inv, one_div, one_mul] using
      (le_refl ((3 : ℝ) * ((n : ℝ) ^ 2)⁻¹))
  · positivity

theorem summable_oddPrimeSquareWeight : Summable oddPrimeSquareWeight := by
  have hbase : Summable (fun n : ℕ => (3 : ℝ) * (1 / (n : ℝ) ^ 2)) :=
    (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < (2 : ℕ))).mul_left 3
  exact hbase.of_nonneg_of_le oddPrimeSquareWeight_nonneg
    oddPrimeSquareWeight_le_pSeriesMajorant

noncomputable def eulerKernelConstant : ℝ :=
  Real.exp (∑' n : ℕ, oddPrimeSquareWeight n)

theorem one_le_eulerKernelConstant : 1 ≤ eulerKernelConstant := by
  unfold eulerKernelConstant
  exact Real.one_le_exp (tsum_nonneg oddPrimeSquareWeight_nonneg)

theorem finiteEulerProduct_eq_weightProduct (X : ℕ) :
    (∏ p ∈ oddPrimesBelow X, (1 + (3 : ℝ) / (p : ℝ) ^ 2)) =
      ∏ p ∈ oddPrimesBelow X, (1 + oddPrimeSquareWeight p) := by
  apply Finset.prod_congr rfl
  intro p hp
  have hprops : p.Prime ∧ 2 < p := (Finset.mem_filter.mp hp).2
  rw [oddPrimeSquareWeight, if_pos hprops]

theorem finiteEulerProduct_le_eulerKernelConstant (X : ℕ) :
    (∏ p ∈ oddPrimesBelow X, (1 + (3 : ℝ) / (p : ℝ) ^ 2)) ≤
      eulerKernelConstant := by
  rw [finiteEulerProduct_eq_weightProduct]
  unfold eulerKernelConstant
  calc
    (∏ p ∈ oddPrimesBelow X, (1 + oddPrimeSquareWeight p)) ≤
        Real.exp (∑ p ∈ oddPrimesBelow X, oddPrimeSquareWeight p) :=
      Real.prod_one_add_le_exp_sum (oddPrimesBelow X) oddPrimeSquareWeight_nonneg
    _ ≤ Real.exp (∑' n : ℕ, oddPrimeSquareWeight n) :=
      Real.exp_le_exp.mpr
        (summable_oddPrimeSquareWeight.sum_le_tsum (oddPrimesBelow X)
          (fun n _ => oddPrimeSquareWeight_nonneg n))

theorem supportedKernelSum_le_eulerKernelConstant (X : ℕ) :
    (∑ d ∈ Finset.range X, supportedReciprocalKernel d) ≤
      eulerKernelConstant := by
  exact (supportedKernelSum_le_finiteEulerProduct X).trans
    (finiteEulerProduct_le_eulerKernelConstant X)

end GoldbachCircleMethodArithmeticEulerKernelBoundV18439
