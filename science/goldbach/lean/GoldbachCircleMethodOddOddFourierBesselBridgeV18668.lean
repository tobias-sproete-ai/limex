import GoldbachCircleMethodDiagonalCompensatedEvenSubchannelsV18667

/-!
# V1.8.668: exact Odd-Odd Fourier/Bessel bridge

The V1.8.667 compensated Odd-Odd deficit is identified with the real Fourier
coefficient of the unchanged Minor mask multiplied by the square of the exact
odd-coordinate von Mangoldt polynomial.  This is semantic closure only.

A finite Bessel argument then bounds the harmful one-sided target moment by
the corresponding Odd-Odd Minor fourth moment.  That ceiling is sufficient
but strictly stronger than the sign-sensitive target: it discards coefficient
signs and includes the full integer Fourier spectrum.  No bound for the fourth
moment is supplied or claimed.

`proof_status = NO_PROOF`.
-/

set_option autoImplicit false

open scoped BigOperators Classical
open MeasureTheory AddCircle
open GoldbachCircleMethodFourierIdentityV171
open GoldbachCircleMethodTwoScaleIntegralPartitionV1831
open GoldbachCircleMethodTwoScaleBesselBridgeV1834
open GoldbachCircleMethodArithmeticHalfShiftV1883
open GoldbachCircleMethodSignedMaskKernelConvolutionV1884
open GoldbachCircleMethodActualMaskReflectionV1886
open GoldbachCircleMethodExceptionalTransferV1823
open GoldbachCircleMethodOddChannelEventualAbsorptionV18658
open GoldbachCircleMethodDiagonalCompensatedEvenSubchannelsV18667

namespace GoldbachCircleMethodOddOddFourierBesselBridgeV18668

/-- Exact one-coordinate odd carrier used by V1.8.667 after taking its
Cartesian square. -/
def oddCarrier (M : Nat) : Finset Nat :=
  (Finset.range M.succ).filter Odd

/-- Odd-coordinate part of the actual finite von Mangoldt exponential sum. -/
noncomputable def oddExponentialSum (M : Nat) : C(UnitAddCircle, Complex) :=
  ∑ n ∈ oddCarrier M,
    (ArithmeticFunction.vonMangoldt n : Complex) • fourier (n : Int)

/-- The unchanged Minor indicator times the literal Odd-Odd square. -/
noncomputable def oddOddMaskedSquare
    (M P R : Nat) : UnitAddCircle → Complex :=
  (twoScaleMinorMask M P R).indicator
    (fun x => oddExponentialSum M x * oddExponentialSum M x)

/-- Full Odd-Odd fourth moment on the unchanged Minor mask.  This is only a
named analytic object; no quantitative estimate is asserted. -/
noncomputable def oddOddMinorFourthMoment (M P R : Nat) : Real :=
  ∫ x in twoScaleMinorMask M P R,
    ‖oddExponentialSum M x‖ ^ 4 ∂haarAddCircle

/-- Exact finite-mode expansion of the Odd-Odd square. -/
theorem oddExponentialSum_square_as_finite_modes
    (M : Nat) (x : UnitAddCircle) :
    oddExponentialSum M x * oddExponentialSum M x =
      ∑ ab ∈ (oddCarrier M).product (oddCarrier M),
        ((ArithmeticFunction.vonMangoldt ab.1 : Complex) *
          (ArithmeticFunction.vonMangoldt ab.2 : Complex)) *
        fourier ((ab.1 : Int) + (ab.2 : Int)) x := by
  rw [Finset.product_eq_sprod,
    Finset.sum_product (oddCarrier M) (oddCarrier M)
      (fun ab : Nat × Nat =>
        ((ArithmeticFunction.vonMangoldt ab.1 : Complex) *
          (ArithmeticFunction.vonMangoldt ab.2 : Complex)) *
        fourier ((ab.1 : Int) + (ab.2 : Int)) x)]
  calc
    _ = ∑ a ∈ oddCarrier M, ∑ b ∈ oddCarrier M,
        ((ArithmeticFunction.vonMangoldt a : Complex) * fourier (a : Int) x) *
        ((ArithmeticFunction.vonMangoldt b : Complex) * fourier (b : Int) x) := by
      simp [oddExponentialSum, Finset.mul_sum, mul_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a _ha
      apply Finset.sum_congr rfl
      intro b _hb
      rw [fourier_add]
      ring

/-- Exact complex coefficient of the literal Odd-Odd masked square. -/
theorem fourierCoeff_oddOddMaskedSquare
    (M P R N : Nat) :
    fourierCoeff (oddOddMaskedSquare M P R) (N : Int) =
      ∑ ab ∈ (oddCarrier M).product (oddCarrier M),
        ((ArithmeticFunction.vonMangoldt ab.1 : Complex) *
          (ArithmeticFunction.vonMangoldt ab.2 : Complex)) *
        minorMaskKernel M P R
          ((N : Int) - (ab.1 : Int) - (ab.2 : Int)) := by
  have hf : oddOddMaskedSquare M P R =
      fun x => minorWeight M P R x *
        ∑ ab ∈ (oddCarrier M).product (oddCarrier M),
          ((ArithmeticFunction.vonMangoldt ab.1 : Complex) *
            (ArithmeticFunction.vonMangoldt ab.2 : Complex)) *
          fourier ((ab.1 : Int) + (ab.2 : Int)) x := by
    funext x
    rw [← oddExponentialSum_square_as_finite_modes M x]
    by_cases hx : x ∈ twoScaleMinorMask M P R
    · simp [oddOddMaskedSquare, minorWeight, Set.indicator_of_mem hx]
    · simp [oddOddMaskedSquare, minorWeight, Set.indicator_of_notMem hx]
  rw [hf, finite_weighted_modes_coefficient]
  simp only [sub_add_eq_sub_sub]

/-- The new Odd-Odd coefficient is real because every Minor-mask kernel
coefficient is real.  This does not imply either sign. -/
theorem oddOddMaskedSquare_coefficient_im_zero
    (M P R N : Nat) :
    (fourierCoeff (oddOddMaskedSquare M P R) (N : Int)).im = 0 := by
  rw [fourierCoeff_oddOddMaskedSquare]
  simp [Complex.mul_im, minorMaskKernel_im_zero]

/-- The V1.8.667 finite kernel convolution is literally the real part of the
Odd-Odd masked-square coefficient. -/
theorem oddOddMinorKernelConvolution_eq_re_fourierCoeff
    (M P R N : Nat) :
    oddOddMinorKernelConvolution M P R N =
      (fourierCoeff (oddOddMaskedSquare M P R) (N : Int)).re := by
  rw [fourierCoeff_oddOddMaskedSquare]
  rw [Complex.re_sum]
  unfold oddOddMinorKernelConvolution
  apply Finset.sum_congr
  · ext ab
    change ab ∈ (((Finset.range M.succ).product (Finset.range M.succ)).filter
        (fun ab => Odd ab.1 ∧ Odd ab.2)) ↔
      ab ∈ (oddCarrier M).product (oddCarrier M)
    simp [oddCarrier, and_left_comm, and_assoc, and_comm]
  · intro ab _hab
    simp [GoldbachCircleMethodActualOneSidedKernelLeakageV18648.lambdaPairWeight,
      Complex.mul_re, minorMaskKernel_im_zero]

/-- Exact semantic closure: the compensated Odd-Odd deficit is the negative
real coefficient of the literal Odd-Odd masked square.  No estimate occurs. -/
theorem compensatedOddOddDeficit_eq_neg_re_fourierCoeff_oddOddMaskedSquare
    (M P R N : Nat) (hscale : 2 * P * R < M) :
    compensatedOddOddDeficit M P R N =
      -(fourierCoeff (oddOddMaskedSquare M P R) (N : Int)).re := by
  rw [compensatedOddOddDeficit_eq_neg_minorConvolution M P R N hscale]
  rw [oddOddMinorKernelConvolution_eq_re_fourierCoeff]

theorem oddOddMaskedSquare_memLp_two (M P R : Nat) :
    MemLp (oddOddMaskedSquare M P R) 2 haarAddCircle := by
  exact MemLp.indicator (twoScaleMinorMask_measurable M P R)
    (ContinuousMap.memLp (p := 2) haarAddCircle Complex
      (oddExponentialSum M * oddExponentialSum M))

theorem integral_oddOddMaskedSquare_norm_sq (M P R : Nat) :
    (∫ x : UnitAddCircle,
      ‖oddOddMaskedSquare M P R x‖ ^ 2 ∂haarAddCircle) =
        oddOddMinorFourthMoment M P R := by
  unfold oddOddMinorFourthMoment
  rw [← integral_indicator (twoScaleMinorMask_measurable M P R)]
  apply integral_congr_ae
  filter_upwards [] with x
  by_cases hx : x ∈ twoScaleMinorMask M P R
  · simp only [oddOddMaskedSquare, Set.indicator_of_mem hx, norm_mul]
    ring
  · simp [oddOddMaskedSquare, Set.indicator_of_notMem hx]

theorem hasSum_sq_oddOddMaskedSquare_fourierCoeff (M P R : Nat) :
    HasSum
      (fun k : Int => ‖fourierCoeff (oddOddMaskedSquare M P R) k‖ ^ 2)
      (oddOddMinorFourthMoment M P R) := by
  let h := oddOddMaskedSquare_memLp_two M P R
  have hc := fourierCoeff_congr_ae h.coeFn_toLp
  have hi :
      (∫ x : UnitAddCircle,
        ‖h.toLp (oddOddMaskedSquare M P R) x‖ ^ 2 ∂haarAddCircle) =
      ∫ x : UnitAddCircle,
        ‖oddOddMaskedSquare M P R x‖ ^ 2 ∂haarAddCircle := by
    apply integral_congr_ae
    filter_upwards [h.coeFn_toLp] with x hx
    rw [hx]
  have hp := hasSum_sq_fourierCoeff
    (h.toLp (oddOddMaskedSquare M P R))
  rw [hc, hi, integral_oddOddMaskedSquare_norm_sq] at hp
  exact hp

/-- Target-local coefficient energy is bounded by the full Odd-Odd fourth
moment.  The second inequality is Bessel and includes all integer modes. -/
theorem finite_sq_oddOdd_coeff_le_fourthMoment
    (M P R : Nat) (s : Finset Nat) :
    (∑ N ∈ s,
      ‖fourierCoeff (oddOddMaskedSquare M P R) (N : Int)‖ ^ 2) ≤
        oddOddMinorFourthMoment M P R := by
  have hs := sum_le_hasSum (s.image (fun N : Nat => (N : Int)))
    (fun k _hk => sq_nonneg ‖fourierCoeff (oddOddMaskedSquare M P R) k‖)
    (hasSum_sq_oddOddMaskedSquare_fourierCoeff M P R)
  rw [Finset.sum_image] at hs
  · exact hs
  · intro a _ha b _hb hab
    exact Int.ofNat_inj.mp hab

/-- Direct finite Bessel ceiling for the compensated harmful moment.

This is unconditional once the exact geometric scale condition is supplied,
but it is deliberately only a sufficient upper bound: the pointwise step
replaces a one-sided real coefficient by its full squared norm, destroying the
signed cancellation retained in V1.8.667. -/
theorem compensatedOddOdd_negativePartMoment_le_fourthMoment
    (M P R : Nat) (s : Finset Nat) (hscale : 2 * P * R < M) :
    negativePartSquaredMoment s
        (fun N => -compensatedOddOddDeficit M P R N) ≤
      oddOddMinorFourthMoment M P R := by
  unfold negativePartSquaredMoment
  calc
    _ ≤ ∑ N ∈ s,
        ‖fourierCoeff (oddOddMaskedSquare M P R) (N : Int)‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro N _hN
      simp only
      rw [compensatedOddOddDeficit_eq_neg_re_fourierCoeff_oddOddMaskedSquare
        M P R N hscale]
      simp only [neg_neg]
      exact negativePart_re_sq_le_norm_sq _
    _ ≤ _ := finite_sq_oddOdd_coeff_le_fourthMoment M P R s

/-- Literal project-target specialization of the finite Bessel ceiling.

The only hypothesis is the already explicit geometric scale condition.  This
does not estimate the fourth moment on the right. -/
theorem compensatedOddOdd_project_negativePartMoment_le_fourthMoment
    (M : Nat)
    (hscale : 2 * oddProjectWidth M * oddProjectRadius M < M) :
    negativePartSquaredMoment
        (GoldbachCircleMethodTwoScaleEvenBlockDefectReserveV1833.evenTargetBlock M)
        (fun N => -compensatedOddOddDeficit M
          (oddProjectWidth M) (oddProjectRadius M) N) ≤
      oddOddMinorFourthMoment M (oddProjectWidth M) (oddProjectRadius M) := by
  exact compensatedOddOdd_negativePartMoment_le_fourthMoment M
    (oddProjectWidth M) (oddProjectRadius M)
    (GoldbachCircleMethodTwoScaleEvenBlockDefectReserveV1833.evenTargetBlock M)
    hscale

end GoldbachCircleMethodOddOddFourierBesselBridgeV18668
