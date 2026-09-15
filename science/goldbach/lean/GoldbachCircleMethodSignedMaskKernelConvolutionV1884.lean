import GoldbachCircleMethodArithmeticHalfShiftV1883

/-! Exact signed finite convolution of the unchanged masked Lambda square.
Frequency differences live in Int; there is no truncated Nat subtraction. -/
set_option autoImplicit false
open scoped BigOperators Classical
open MeasureTheory AddCircle
open GoldbachCircleMethodFourierIdentityV171
open GoldbachCircleMethodTwoScaleIntegralPartitionV1831
open GoldbachCircleMethodTwoScaleBesselBridgeV1834
open GoldbachCircleMethodArithmeticHalfShiftV1883

namespace GoldbachCircleMethodSignedMaskKernelConvolutionV1884

noncomputable def minorMaskKernel (M P R : ℕ) (k : ℤ) : ℂ :=
  fourierCoeff (minorWeight M P R) k

theorem minorWeight_integrable (M P R : ℕ) :
    Integrable (minorWeight M P R) haarAddCircle :=
  (integrable_const (1 : ℂ)).indicator (twoScaleMinorMask_measurable M P R)

theorem minorMaskKernel_zero (M P R : ℕ) :
    minorMaskKernel M P R 0 =
      (haarAddCircle.real (twoScaleMinorMask M P R) : ℂ) := by
  simp [minorMaskKernel, fourierCoeff, minorWeight, integral_indicator
    (twoScaleMinorMask_measurable M P R), integral_const, Complex.real_smul]

theorem minorWeight_mode_coefficient (M P R : ℕ) (k j : ℤ) :
    fourierCoeff (fun x => minorWeight M P R x*fourier j x) k =
      minorMaskKernel M P R (k-j) := by
  unfold minorMaskKernel
  rw [fourierCoeff, fourierCoeff]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [show -(k-j) = -k+j by omega, fourier_add]
  simp only [smul_eq_mul]
  ring

theorem weighted_mode_integrable (M P R : ℕ) (a : ℂ) (j : ℤ) :
    Integrable (fun x => a*(minorWeight M P R x*fourier j x)) haarAddCircle := by
  have h := (minorWeight_integrable M P R).fourier_smul j
  have h' : Integrable (fun x => minorWeight M P R x*fourier j x) haarAddCircle := by
    simpa [smul_eq_mul, mul_comm] using h
  exact h'.const_mul a

theorem finite_weighted_modes_coefficient {ι : Type*} (M P R : ℕ)
    (s : Finset ι) (a : ι → ℂ) (j : ι → ℤ) (k : ℤ) :
    fourierCoeff (fun x => minorWeight M P R x*∑ i ∈ s, a i*fourier (j i) x) k =
      ∑ i ∈ s, a i*minorMaskKernel M P R (k-j i) := by
  have hf : (fun x => minorWeight M P R x*∑ i ∈ s, a i*fourier (j i) x) =
      ∑ i ∈ s, (fun x => a i*(minorWeight M P R x*fourier (j i) x)) := by
    funext x
    simp [Finset.mul_sum, mul_left_comm]
  rw [hf, fourierCoeff.sum s _ (fun i _ => weighted_mode_integrable M P R (a i) (j i))]
  simp only [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [fourierCoeff.const_mul, minorWeight_mode_coefficient]

theorem lambda_square_as_finite_modes (M : ℕ) (x : UnitAddCircle) :
    exponentialSum M.succ x*exponentialSum M.succ x =
      ∑ ab ∈ (Finset.range M.succ).product (Finset.range M.succ),
        ((ArithmeticFunction.vonMangoldt ab.1 : ℂ)*
          (ArithmeticFunction.vonMangoldt ab.2 : ℂ)) *
        fourier ((ab.1 : ℤ)+(ab.2 : ℤ)) x := by
  rw [Finset.product_eq_sprod,
    Finset.sum_product (Finset.range M.succ) (Finset.range M.succ)
    (fun ab : ℕ × ℕ =>
      ((ArithmeticFunction.vonMangoldt ab.1 : ℂ)*
        (ArithmeticFunction.vonMangoldt ab.2 : ℂ)) *
      fourier ((ab.1 : ℤ)+(ab.2 : ℤ)) x)]
  calc
    _ = ∑ a ∈ Finset.range M.succ, ∑ b ∈ Finset.range M.succ,
        ((ArithmeticFunction.vonMangoldt a : ℂ)*fourier (a : ℤ) x) *
        ((ArithmeticFunction.vonMangoldt b : ℂ)*fourier (b : ℤ) x) := by
      simp [exponentialSum, Finset.mul_sum, mul_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      rw [fourier_add]
      ring

theorem maskedSquare_coefficient_exact_finite_convolution (M P R N : ℕ) :
    fourierCoeff (maskedSquare M P R) (N : ℤ) =
      ∑ ab ∈ (Finset.range M.succ).product (Finset.range M.succ),
        ((ArithmeticFunction.vonMangoldt ab.1 : ℂ)*
          (ArithmeticFunction.vonMangoldt ab.2 : ℂ)) *
        minorMaskKernel M P R ((N : ℤ)-(ab.1 : ℤ)-(ab.2 : ℤ)) := by
  have hf : maskedSquare M P R =
      fun x => minorWeight M P R x *
        ∑ ab ∈ (Finset.range M.succ).product (Finset.range M.succ),
          ((ArithmeticFunction.vonMangoldt ab.1 : ℂ)*
            (ArithmeticFunction.vonMangoldt ab.2 : ℂ)) *
          fourier ((ab.1 : ℤ)+(ab.2 : ℤ)) x := by
    funext x
    rw [← lambda_square_as_finite_modes]
    by_cases hx : x ∈ twoScaleMinorMask M P R
    · simp [maskedSquare, minorWeight, Set.indicator_of_mem hx]
    · simp [maskedSquare, minorWeight, Set.indicator_of_notMem hx]
  rw [hf, finite_weighted_modes_coefficient]
  simp only [sub_add_eq_sub_sub]

theorem actual_minor_real_exact_finite_convolution (M P R N : ℕ) :
    twoScaleMinorIntegralReal M P R N =
      ∑ ab ∈ (Finset.range M.succ).product (Finset.range M.succ),
        ArithmeticFunction.vonMangoldt ab.1 * ArithmeticFunction.vonMangoldt ab.2 *
        (minorMaskKernel M P R ((N : ℤ)-(ab.1 : ℤ)-(ab.2 : ℤ))).re := by
  rw [minorReal_eq_re_fourierCoeff, maskedSquare_coefficient_exact_finite_convolution]
  simp [Complex.mul_re]

end GoldbachCircleMethodSignedMaskKernelConvolutionV1884
