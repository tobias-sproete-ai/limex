import GoldbachCircleMethodExplicitOffDiagonalKernelLeakageV18649

/-!
# V1.8.650: exact kernel Jordan balance

The V1.8.648 leakage bound moves `negativePart` inside a finite sum and
therefore discards cancellation between positive and negative off-diagonal
modes.  This module keeps both one-sided masses and proves the exact Jordan
balance of the actual Minor coefficient.

The diagonal contributes zero to the negative mass and its exact
nonnegative Haar-mass contribution to the positive mass.  No positive lower
bound for the diagonal von-Mangoldt convolution is asserted.

No analytic estimate is supplied.  `proof_status = NO_PROOF`.
-/
set_option autoImplicit false

open scoped BigOperators Classical
open MeasureTheory AddCircle
open GoldbachCircleMethodSignedMaskKernelConvolutionV1884
open GoldbachCircleMethodActualMajorOvershootIdentityV18630
open GoldbachCircleMethodActualOneSidedKernelLeakageV18648
open GoldbachCircleMethodExplicitOffDiagonalKernelLeakageV18649

namespace GoldbachCircleMethodExactKernelJordanBalanceV18650

/-- Exact scalar Jordan decomposition on the reals. -/
theorem real_eq_positivePart_sub_negativePart (x : ℝ) :
    x = positivePart x -
      GoldbachCircleMethodExceptionalTransferV1823.negativePart x := by
  rcases le_total 0 x with hx | hx
  · unfold positivePart
      GoldbachCircleMethodExceptionalTransferV1823.negativePart
    rw [max_eq_left hx, max_eq_right]
    · ring
    · exact neg_nonpos.mpr hx
  · unfold positivePart
      GoldbachCircleMethodExceptionalTransferV1823.negativePart
    rw [max_eq_right hx, max_eq_left]
    · ring
    · exact neg_nonneg.mpr hx

/-- Weighted positive mass of the real Minor-mask kernel on the unchanged
finite von-Mangoldt pair carrier. -/
noncomputable def positiveKernelMass (M P R N : ℕ) : ℝ :=
  ∑ ab ∈ (Finset.range M.succ).product (Finset.range M.succ),
    lambdaPairWeight ab *
      positivePart
        (minorMaskKernel M P R
          ((N : ℤ) - (ab.1 : ℤ) - (ab.2 : ℤ))).re

theorem positiveKernelMass_nonneg (M P R N : ℕ) :
    0 ≤ positiveKernelMass M P R N := by
  unfold positiveKernelMass
  exact Finset.sum_nonneg fun ab _ =>
    mul_nonneg (lambdaPairWeight_nonneg ab) (positivePart_nonneg _)

/-- The actual Minor coefficient is exactly positive kernel mass minus
negative kernel mass.  No subadditivity is used. -/
theorem actual_minor_real_eq_positiveKernelMass_sub_negativeKernelLeakage
    (M P R N : ℕ) :
    GoldbachCircleMethodTwoScaleIntegralPartitionV1831.twoScaleMinorIntegralReal
        M P R N =
      positiveKernelMass M P R N - negativeKernelLeakage M P R N := by
  rw [actual_minor_real_exact_finite_convolution]
  unfold positiveKernelMass negativeKernelLeakage lambdaPairWeight
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro ab _
  rw [← mul_sub, ← real_eq_positivePart_sub_negativePart]

/-- Exact signed imbalance formula for the actual Major overshoot. -/
theorem actualMajorOvershoot_eq_positivePart_kernelImbalance
    (M P R N : ℕ) (hNM : N ≤ M) :
    actualMajorOvershoot M P R N =
      positivePart
        (negativeKernelLeakage M P R N - positiveKernelMass M P R N) := by
  rw [← negativePart_minor_eq_actualMajorOvershoot M P R N hNM]
  rw [actual_minor_real_eq_positiveKernelMass_sub_negativeKernelLeakage]
  unfold GoldbachCircleMethodExceptionalTransferV1823.negativePart positivePart
  congr 1
  ring

/-- The exact von-Mangoldt weight carried by the convolution diagonal. -/
noncomputable def diagonalLambdaPairMass (M N : ℕ) : ℝ :=
  ∑ ab ∈
      ((Finset.range M.succ).product (Finset.range M.succ)).filter
        (fun ab => ab.1 + ab.2 = N),
    lambdaPairWeight ab

/-- The positive-kernel contribution restricted to the convolution
diagonal. -/
noncomputable def diagonalPositiveKernelMass (M P R N : ℕ) : ℝ :=
  ∑ ab ∈
      ((Finset.range M.succ).product (Finset.range M.succ)).filter
        (fun ab => ab.1 + ab.2 = N),
    lambdaPairWeight ab *
      positivePart
        (minorMaskKernel M P R
          ((N : ℤ) - (ab.1 : ℤ) - (ab.2 : ℤ))).re

/-- On a diagonal pair the positive kernel part is exactly the nonnegative
Haar mass of the Minor mask. -/
theorem diagonal_positiveKernelContribution_eq_haar
    (M P R N a b : ℕ) (hab : a + b = N) :
    lambdaPairWeight (a, b) *
        positivePart
          (minorMaskKernel M P R
            ((N : ℤ) - (a : ℤ) - (b : ℤ))).re =
      lambdaPairWeight (a, b) *
        haarAddCircle.real
          (GoldbachCircleMethodTwoScaleIntegralPartitionV1831.twoScaleMinorMask
            M P R) := by
  have hshift : (N : ℤ) - (a : ℤ) - (b : ℤ) = 0 := by
    have habz : (a : ℤ) + (b : ℤ) = (N : ℤ) := by
      exact_mod_cast hab
    omega
  rw [hshift, minorMaskKernel_zero]
  simp only [Complex.ofReal_re]
  have hmeasure :
      0 ≤ haarAddCircle.real
        (GoldbachCircleMethodTwoScaleIntegralPartitionV1831.twoScaleMinorMask
          M P R) := measureReal_nonneg
  unfold positivePart
  rw [max_eq_left hmeasure]

/-- The whole positive diagonal is exactly the Haar mass times the finite
diagonal von-Mangoldt pair mass. -/
theorem diagonalPositiveKernelMass_eq_haar_mul_diagonalLambdaPairMass
    (M P R N : ℕ) :
    diagonalPositiveKernelMass M P R N =
      haarAddCircle.real
          (GoldbachCircleMethodTwoScaleIntegralPartitionV1831.twoScaleMinorMask
            M P R) *
        diagonalLambdaPairMass M N := by
  unfold diagonalPositiveKernelMass diagonalLambdaPairMass
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ab hab
  rw [diagonal_positiveKernelContribution_eq_haar
    M P R N ab.1 ab.2 (Finset.mem_filter.mp hab).2]
  ring

/-- The exact positive diagonal contribution is nonnegative. -/
theorem diagonalPositiveKernelMass_nonneg (M P R N : ℕ) :
    0 ≤ diagonalPositiveKernelMass M P R N := by
  unfold diagonalPositiveKernelMass
  exact Finset.sum_nonneg fun ab _ =>
    mul_nonneg (lambdaPairWeight_nonneg ab) (positivePart_nonneg _)

end GoldbachCircleMethodExactKernelJordanBalanceV18650
