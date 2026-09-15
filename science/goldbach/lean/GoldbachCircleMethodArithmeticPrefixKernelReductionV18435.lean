import GoldbachCircleMethodArithmeticDivisorWeightNormalFormV18434

/-!
# Goldbach V1.8.435: prefix kernel reduction

The floor multiplicity in V1.8.433 is bounded by the real reciprocal factor
and the common prefix scale is factored out.  The linear mean problem is thus
reduced to one explicit finite positive kernel sum.

No uniform kernel-sum constant is claimed. `proof_status = NO_PROOF`.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodArithmeticPrefixKernelReductionV18435

open GoldbachCircleMethodArithmeticDivisorReindexV18430
open GoldbachCircleMethodArithmeticPrefixDivisorBudgetV18433
open GoldbachCircleMethodArithmeticDivisorWeightNormalFormV18434

theorem floorMultiplicity_mul_le_kernel {X d : ℕ} :
    ((((X - 1) / d : ℕ) : ℝ) * divisorMajorant d) ≤
      (X : ℝ) * reciprocalDivisorKernel d := by
  by_cases hd : d = 0
  · subst d
    simp [reciprocalDivisorKernel]
  · have hdR : (0 : ℝ) < d := by positivity
    have hcast : ((((X - 1) / d : ℕ) : ℝ)) ≤
        ((X - 1 : ℕ) : ℝ) / (d : ℝ) := Nat.cast_div_le
    have hsub : (((X - 1 : ℕ) : ℝ)) ≤ (X : ℝ) := by
      exact_mod_cast Nat.sub_le X 1
    have hquot : ((((X - 1) / d : ℕ) : ℝ)) ≤ (X : ℝ) / (d : ℝ) :=
      hcast.trans (div_le_div_of_nonneg_right hsub hdR.le)
    rw [reciprocalDivisorKernel, if_neg hd]
    calc
      ((((X - 1) / d : ℕ) : ℝ) * divisorMajorant d) ≤
          ((X : ℝ) / (d : ℝ)) * divisorMajorant d :=
        mul_le_mul_of_nonneg_right hquot (le_of_lt (divisorMajorant_pos d))
      _ = (X : ℝ) * (divisorMajorant d / (d : ℝ)) := by ring

/-- The exact remaining finite gate for a linear arithmetic-factor prefix mean. -/
theorem arithmeticFactor_prefix_le_scale_mul_kernelSum {X : ℕ} (hX : 1 ≤ X) :
    (∑ n ∈ Finset.Ico 1 X,
      GoldbachCircleMethodGlobalSieveFiniteFactorV18173.arithmeticFactor n) ≤
      (X : ℝ) * ∑ d ∈ Finset.range X, reciprocalDivisorKernel d := by
  calc
    (∑ n ∈ Finset.Ico 1 X,
        GoldbachCircleMethodGlobalSieveFiniteFactorV18173.arithmeticFactor n) ≤
        ∑ d ∈ Finset.range X,
          (((X - 1) / d : ℕ) : ℝ) * divisorMajorant d :=
      arithmeticFactor_prefix_le_reciprocalDivisorBudget hX
    _ ≤ ∑ d ∈ Finset.range X,
        (X : ℝ) * reciprocalDivisorKernel d := by
      apply Finset.sum_le_sum
      intro d hd
      exact floorMultiplicity_mul_le_kernel
    _ = (X : ℝ) * ∑ d ∈ Finset.range X, reciprocalDivisorKernel d := by
      rw [Finset.mul_sum]

end GoldbachCircleMethodArithmeticPrefixKernelReductionV18435
