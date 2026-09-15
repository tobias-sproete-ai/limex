import GoldbachCircleMethodSignedMaskKernelConvolutionV1884
import GoldbachCircleMethodActualMajorOvershootIdentityV18630

/-!
# V1.8.648: actual one-sided kernel leakage

The exact finite convolution from V1.8.84 is passed through the one-sided
negative-part functional.  Since the von-Mangoldt pair weights are
nonnegative, finite subadditivity and positive homogeneity bound the actual
Major overshoot by a finite weighted sum of the negative part of the real
Minor-mask kernel.

The diagonal `a + b = N` contributes exactly zero to this one-sided leakage:
the zero-frequency kernel is the nonnegative Haar mass of the Minor mask.  The
kernel itself is not asserted to vanish.

No estimate for the remaining off-diagonal leakage is supplied.  This is a
diagonal-free one-sided kernel reduction, not a leakage estimate and not a
Goldbach proof.

`proof_status = NO_PROOF`.
-/
set_option autoImplicit false

open scoped BigOperators Classical
open MeasureTheory AddCircle
open GoldbachCircleMethodExceptionalTransferV1823
open GoldbachCircleMethodTwoScaleIntegralPartitionV1831
open GoldbachCircleMethodSignedMaskKernelConvolutionV1884
open GoldbachCircleMethodActualMajorOvershootIdentityV18630

namespace GoldbachCircleMethodActualOneSidedKernelLeakageV18648

/-- The negative part is nonnegative. -/
theorem negativePart_nonneg (x : ℝ) :
    0 ≤ negativePart x := by
  unfold negativePart
  exact le_max_right _ _

/-- Subadditivity of the negative part on the reals. -/
theorem negativePart_add_le (x y : ℝ) :
    negativePart (x + y) ≤ negativePart x + negativePart y := by
  unfold negativePart
  apply max_le
  · have hx : -x ≤ max (-x) 0 := le_max_left _ _
    have hy : -y ≤ max (-y) 0 := le_max_left _ _
    linarith
  · exact add_nonneg (le_max_right _ _) (le_max_right _ _)

/-- A nonnegative scalar can be pulled outside the one-sided upper bound. -/
theorem negativePart_mul_le (c x : ℝ) (hc : 0 ≤ c) :
    negativePart (c * x) ≤ c * negativePart x := by
  unfold negativePart
  apply max_le
  · have hx : -x ≤ max (-x) 0 := le_max_left _ _
    have h := mul_le_mul_of_nonneg_left hx hc
    nlinarith
  · exact mul_nonneg hc (le_max_right _ _)

/-- Finite subadditivity of the negative part. -/
theorem negativePart_sum_le_sum {ι : Type*}
    (s : Finset ι) (f : ι → ℝ) :
    negativePart (∑ i ∈ s, f i) ≤ ∑ i ∈ s, negativePart (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [negativePart]
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      exact (negativePart_add_le (f a) (∑ i ∈ s, f i)).trans
        (add_le_add le_rfl ih)

/-- The nonnegative real weight of a von-Mangoldt pair. -/
noncomputable def lambdaPairWeight (ab : ℕ × ℕ) : ℝ :=
  ArithmeticFunction.vonMangoldt ab.1 * ArithmeticFunction.vonMangoldt ab.2

theorem lambdaPairWeight_nonneg (ab : ℕ × ℕ) :
    0 ≤ lambdaPairWeight ab := by
  exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
    ArithmeticFunction.vonMangoldt_nonneg

/-- Finite one-sided kernel leakage.  The definition preserves the sign of
the real kernel coefficient and applies `negativePart` before summation. -/
noncomputable def negativeKernelLeakage (M P R N : ℕ) : ℝ :=
  ∑ ab ∈ (Finset.range M.succ).product (Finset.range M.succ),
    lambdaPairWeight ab *
      negativePart
        (minorMaskKernel M P R
          ((N : ℤ) - (ab.1 : ℤ) - (ab.2 : ℤ))).re

theorem negativeKernelLeakage_nonneg (M P R N : ℕ) :
    0 ≤ negativeKernelLeakage M P R N := by
  unfold negativeKernelLeakage
  exact Finset.sum_nonneg fun ab _ =>
    mul_nonneg (lambdaPairWeight_nonneg ab)
      (negativePart_nonneg _)

/-- Pointwise diagonal-free one-sided reduction: on the exact coefficient
range, the actual Major overshoot is bounded by the weighted negative kernel
leakage. -/
theorem actualMajorOvershoot_le_negativeKernelLeakage
    (M P R N : ℕ) (hNM : N ≤ M) :
    actualMajorOvershoot M P R N ≤ negativeKernelLeakage M P R N := by
  rw [← negativePart_minor_eq_actualMajorOvershoot M P R N hNM]
  rw [actual_minor_real_exact_finite_convolution]
  unfold negativeKernelLeakage
  calc
    negativePart
        (∑ ab ∈ (Finset.range M.succ).product (Finset.range M.succ),
          lambdaPairWeight ab *
            (minorMaskKernel M P R
              ((N : ℤ) - (ab.1 : ℤ) - (ab.2 : ℤ))).re) ≤
        ∑ ab ∈ (Finset.range M.succ).product (Finset.range M.succ),
          negativePart
            (lambdaPairWeight ab *
              (minorMaskKernel M P R
                ((N : ℤ) - (ab.1 : ℤ) - (ab.2 : ℤ))).re) :=
      negativePart_sum_le_sum _ _
    _ ≤ ∑ ab ∈ (Finset.range M.succ).product (Finset.range M.succ),
          lambdaPairWeight ab *
            negativePart
              (minorMaskKernel M P R
                ((N : ℤ) - (ab.1 : ℤ) - (ab.2 : ℤ))).re := by
      exact Finset.sum_le_sum fun ab _ =>
        negativePart_mul_le _ _ (lambdaPairWeight_nonneg ab)

/-- Squared pointwise form of the one-sided kernel reduction. -/
theorem actualMajorOvershoot_sq_le_negativeKernelLeakage_sq
    (M P R N : ℕ) (hNM : N ≤ M) :
    (actualMajorOvershoot M P R N) ^ 2 ≤
      (negativeKernelLeakage M P R N) ^ 2 := by
  have hle := actualMajorOvershoot_le_negativeKernelLeakage M P R N hNM
  have hov : 0 ≤ actualMajorOvershoot M P R N := by
    unfold actualMajorOvershoot
    exact le_max_right _ _
  have hleak := negativeKernelLeakage_nonneg M P R N
  nlinarith

/-- Finite squared leakage on an arbitrary target carrier. -/
noncomputable def negativeKernelLeakageSquaredMoment
    (M P R : ℕ) (s : Finset ℕ) : ℝ :=
  ∑ N ∈ s, (negativeKernelLeakage M P R N) ^ 2

/-- Corresponding finite squared-moment upper bound. -/
theorem actualMajorOvershootSquaredMoment_le_negativeKernelLeakageSquaredMoment
    (M P R : ℕ) (s : Finset ℕ)
    (hRange : ∀ N ∈ s, N ≤ M) :
    actualMajorOvershootSquaredMoment M P R s ≤
      negativeKernelLeakageSquaredMoment M P R s := by
  unfold actualMajorOvershootSquaredMoment negativeKernelLeakageSquaredMoment
  exact Finset.sum_le_sum fun N hN =>
    actualMajorOvershoot_sq_le_negativeKernelLeakage_sq
      M P R N (hRange N hN)

/-- On the convolution diagonal, only the one-sided contribution vanishes.
The zero-frequency kernel itself equals the nonnegative Haar mass of the
Minor mask. -/
theorem diagonal_negativeKernelContribution_eq_zero
    (M P R N a b : ℕ) (hab : a + b = N) :
    lambdaPairWeight (a, b) *
        negativePart
          (minorMaskKernel M P R
            ((N : ℤ) - (a : ℤ) - (b : ℤ))).re = 0 := by
  have hshift : (N : ℤ) - (a : ℤ) - (b : ℤ) = 0 := by
    have habz : (a : ℤ) + (b : ℤ) = (N : ℤ) := by
      exact_mod_cast hab
    omega
  rw [hshift, minorMaskKernel_zero]
  have hmeasure :
      0 ≤ haarAddCircle.real (twoScaleMinorMask M P R) := measureReal_nonneg
  unfold negativePart
  rw [max_eq_right]
  · ring
  · simp [hmeasure]

end GoldbachCircleMethodActualOneSidedKernelLeakageV18648
