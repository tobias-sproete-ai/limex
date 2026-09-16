import GoldbachCircleMethodActualQ3ZeroClassExactLogMassV18787
import GoldbachCircleMethodActualQ3LocalDensityThreeClassSplitV18785
import GoldbachCircleMethodActualLambdaPairSourceMeanChebyshevBoundV18719

/-!
# V1.8.788: logarithmic q=3 zero-class convolution bound

The exact logarithmic zero-class mass from V1.8.787 is transported through
the unchanged outer von-Mangoldt convolution and the literal q=3 selector.
The result is an explicit `M log M`-scale ceiling after the already proved
Chebyshev estimate.  The full-prefix channel is deliberately not bounded by
absolute values here, because that would destroy its cancellation against the
project mean.

No full profile absorption or Goldbach conclusion is proved.
`proof_status = NO_PROOF`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

open scoped BigOperators Classical ArithmeticFunction.vonMangoldt

namespace GoldbachCircleMethodActualQ3ZeroClassConvolutionBoundV18788

open GoldbachCircleMethodOddOddFourierBesselBridgeV18668
open GoldbachCircleMethodActualLambdaPairSourceMeanChebyshevBoundV18719
open GoldbachCircleMethodActualQ3ResidueSelectorMainProfileAbsorptionV18774
open GoldbachCircleMethodActualQ3LocalDensityThreeClassSplitV18785
open GoldbachCircleMethodActualQ3ZeroClassExactLogMassV18787
open GoldbachCircleMethodChebyshevEnergyBudgetV1889

/-- The literal residue selector has norm at most two. -/
theorem norm_actualQ3ResidueSelector_le_two (n a : Nat) :
    ‖actualQ3ResidueSelector n a‖ ≤ 2 := by
  unfold actualQ3ResidueSelector
  split <;> norm_num

/-- Exact zero-class mass bounded uniformly in the inner prefix by the
base-three logarithm of the ambient carrier. -/
theorem norm_oddLambdaQ3ResidueMass_zero_le_ambient_log
    (M B : Nat) :
    ‖GoldbachCircleMethodActualOddLambdaQ3ResidueDiscrepancyV18752.oddLambdaQ3ResidueMass
        M B (0 : ZMod 3)‖ ≤
      Nat.log 3 M * Real.log 3 := by
  rw [norm_oddLambdaQ3ResidueMass_zero_eq]
  have hcountNat :
      Nat.log 3 (min M (B - 1)) ≤ Nat.log 3 M :=
    Nat.log_mono_right (min_le_left _ _)
  have hcount :
      (Nat.log 3 (min M (B - 1)) : Real) ≤ Nat.log 3 M := by
    exact_mod_cast hcountNat
  have hlog : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  exact mul_le_mul_of_nonneg_right hcount hlog

/-- Before invoking any asymptotic theorem, the exceptional zero-class
selector convolution is bounded by the literal odd-Lambda mass times one
logarithmic factor. -/
theorem norm_actualQ3ZeroClassSelectorConvolution_le_oddLambdaSum_log
    (M n k : Nat) :
    ‖actualQ3ZeroClassSelectorConvolution M n k‖ ≤
      2 * oddLambdaSum M * (Nat.log 3 M * Real.log 3) := by
  unfold actualQ3ZeroClassSelectorConvolution
  calc
    ‖∑ a ∈ oddCarrier M,
        ((ArithmeticFunction.vonMangoldt a : Complex) *
          GoldbachCircleMethodActualOddLambdaQ3ResidueDiscrepancyV18752.oddLambdaQ3ResidueMass
            M (2 * k - a) (0 : ZMod 3)) *
          actualQ3ResidueSelector n a‖ ≤
      ∑ a ∈ oddCarrier M,
        ‖((ArithmeticFunction.vonMangoldt a : Complex) *
          GoldbachCircleMethodActualOddLambdaQ3ResidueDiscrepancyV18752.oddLambdaQ3ResidueMass
            M (2 * k - a) (0 : ZMod 3)) *
          actualQ3ResidueSelector n a‖ := norm_sum_le _ _
    _ ≤ ∑ a ∈ oddCarrier M,
        ArithmeticFunction.vonMangoldt a *
          (Nat.log 3 M * Real.log 3) * 2 := by
      apply Finset.sum_le_sum
      intro a _ha
      rw [norm_mul, norm_mul]
      have hLam : ‖(ArithmeticFunction.vonMangoldt a : Complex)‖ =
          ArithmeticFunction.vonMangoldt a := by
        rw [Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
      rw [hLam]
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left
          (norm_oddLambdaQ3ResidueMass_zero_le_ambient_log
            M (2 * k - a))
          ArithmeticFunction.vonMangoldt_nonneg)
        (norm_actualQ3ResidueSelector_le_two n a)
        (norm_nonneg _)
        (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
          (mul_nonneg (Nat.cast_nonneg _)
            (Real.log_nonneg (by norm_num))))
    _ = 2 * oddLambdaSum M * (Nat.log 3 M * Real.log 3) := by
      unfold oddLambdaSum
      rw [← Finset.sum_mul, ← Finset.sum_mul]
      ring

/-- Fully explicit Chebyshev-linear ceiling for the zero-class channel. -/
theorem norm_actualQ3ZeroClassSelectorConvolution_le_chebyshev
    (M n k : Nat) :
    ‖actualQ3ZeroClassSelectorConvolution M n k‖ ≤
      2 * chebyshevConstant * M * (Nat.log 3 M * Real.log 3) := by
  have hsum := oddLambdaSum_le_chebyshev_linear M
  have hfactor : 0 ≤ Nat.log 3 M * Real.log 3 :=
    mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by norm_num))
  calc
    ‖actualQ3ZeroClassSelectorConvolution M n k‖ ≤
        2 * oddLambdaSum M * (Nat.log 3 M * Real.log 3) :=
      norm_actualQ3ZeroClassSelectorConvolution_le_oddLambdaSum_log M n k
    _ ≤ 2 * (chebyshevConstant * M) *
        (Nat.log 3 M * Real.log 3) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hsum (by norm_num)) hfactor
    _ = 2 * chebyshevConstant * M *
        (Nat.log 3 M * Real.log 3) := by ring

end GoldbachCircleMethodActualQ3ZeroClassConvolutionBoundV18788
