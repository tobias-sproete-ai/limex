import GoldbachCircleMethodDiscreteModelExceptionDetectorV18632

/-!
# V1.8.633: Bessel transfer for the actual Major-operator error

The actual Major square and the fixed discrete arc model are assembled as two
literal functions on the circle.  Their difference is independent of the
target frequency.  Bessel therefore bounds the squared operator-error
coefficients on every finite target carrier by one `L²` energy integral.

This removes the artificial carrier-cardinality loss of a pointwise envelope.
No estimate for the new energy integral is supplied here.

`proof_status = NO_PROOF`.
-/
set_option autoImplicit false

open scoped BigOperators Classical
open MeasureTheory AddCircle
open GoldbachCircleMethodFourierIdentityV171
open GoldbachCircleMethodMajorMinorPartitionV172
open GoldbachCircleMethodFixedScaleTransferV1824
open GoldbachCircleMethodTwoScaleMaskAdapterV1829
open GoldbachCircleMethodTwoScaleIntegralPartitionV1831
open GoldbachCircleMethodDiscreteMainKernelV1852
open GoldbachCircleMethodDiscreteArcModelReserveV1855
open GoldbachCircleMethodClosedArcCoordinatesV1857
open GoldbachCircleMethodComplexArcModelBindingV1856
open GoldbachCircleMethodShiftedClosedArcModelV1858
open GoldbachCircleMethodOriginalMaskModelBindingV1859
open GoldbachCircleMethodActualOperatorErrorTransferV1861
open GoldbachCircleMethodActualOvershootTwoChannelV18631

namespace GoldbachCircleMethodMajorOperatorErrorBesselV18633

/-- The literal square of the fixed-scale von-Mangoldt polynomial, restricted
to the unchanged two-scale Major mask. -/
noncomputable def actualMajorSquare (M P R : ℕ) : UnitAddCircle → ℂ :=
  (twoScaleMajorMask M P R).indicator
    (fun x => exponentialSum M.succ x * exponentialSum M.succ x)

/-- One fixed local model square on its original closed rational arc. -/
noncomputable def localArcModelSquare (M P R : ℕ)
    (i : ReducedRationalIndex R) : UnitAddCircle → ℂ :=
  (Metric.closedBall (majorArcCenter i) (twoScaleArcRadius M P i)).indicator
    (fun x =>
      ((((ArithmeticFunction.moebius i.val.1 : ℤ) : ℂ) /
          (Nat.totient i.val.1 : ℂ)) *
        discreteMainPolynomial M (x - majorArcCenter i)) ^ 2)

/-- Finite assembly of all fixed local model squares. -/
noncomputable def assembledArcModelSquare (M P R : ℕ) : UnitAddCircle → ℂ :=
  ∑ i : ReducedRationalIndex R, localArcModelSquare M P R i

/-- Frequency-independent error function whose coefficients are exactly the
complex Major-operator errors. -/
noncomputable def majorOperatorErrorFunction (M P R : ℕ) : UnitAddCircle → ℂ :=
  actualMajorSquare M P R - assembledArcModelSquare M P R

/-- The exact `L²` energy target for the first V1.8.631 channel. -/
noncomputable def majorOperatorErrorEnergy (M P R : ℕ) : ℝ :=
  ∫ x : UnitAddCircle, ‖majorOperatorErrorFunction M P R x‖ ^ 2 ∂haarAddCircle

theorem actualMajorSquare_integrable (M P R : ℕ) :
    Integrable (actualMajorSquare M P R) haarAddCircle := by
  have hBase : Integrable
      (fun x : UnitAddCircle =>
        exponentialSum M.succ x * exponentialSum M.succ x) haarAddCircle := by
    have hContinuous : Continuous
        (fun x : UnitAddCircle =>
          exponentialSum M.succ x * exponentialSum M.succ x) :=
      (exponentialSum M.succ).continuous.mul (exponentialSum M.succ).continuous
    simpa only [IntegrableOn, Measure.restrict_univ] using
      (ContinuousOn.integrableOn_compact
        (K := Set.univ) isCompact_univ hContinuous.continuousOn)
  exact hBase.indicator (twoScaleMajorMask_measurable M P R)

theorem localArcModelSquare_integrable (M P R : ℕ)
    (i : ReducedRationalIndex R) :
    Integrable (localArcModelSquare M P R i) haarAddCircle := by
  have hBase : Integrable
      (fun x : UnitAddCircle =>
        ((((ArithmeticFunction.moebius i.val.1 : ℤ) : ℂ) /
            (Nat.totient i.val.1 : ℂ)) *
          discreteMainPolynomial M (x - majorArcCenter i)) ^ 2) haarAddCircle := by
    have hContinuous : Continuous
        (fun x : UnitAddCircle =>
          ((((ArithmeticFunction.moebius i.val.1 : ℤ) : ℂ) /
              (Nat.totient i.val.1 : ℂ)) *
            discreteMainPolynomial M (x - majorArcCenter i)) ^ 2) :=
      (continuous_const.mul ((discreteMainPolynomial_continuous M).comp
        (continuous_id.sub continuous_const))).pow 2
    simpa only [IntegrableOn, Measure.restrict_univ] using
      (ContinuousOn.integrableOn_compact
        (K := Set.univ) isCompact_univ hContinuous.continuousOn)
  exact hBase.indicator measurableSet_closedBall

theorem assembledArcModelSquare_integrable (M P R : ℕ) :
    Integrable (assembledArcModelSquare M P R) haarAddCircle := by
  unfold assembledArcModelSquare
  exact integrable_finsetSum' Finset.univ fun i _ =>
    localArcModelSquare_integrable M P R i

theorem majorOperatorErrorFunction_integrable (M P R : ℕ) :
    Integrable (majorOperatorErrorFunction M P R) haarAddCircle := by
  unfold majorOperatorErrorFunction
  exact (actualMajorSquare_integrable M P R).sub
    (assembledArcModelSquare_integrable M P R)

theorem actualMajorSquare_memLp_two (M P R : ℕ) :
    MemLp (actualMajorSquare M P R) 2 haarAddCircle := by
  exact MemLp.indicator (twoScaleMajorMask_measurable M P R)
    (ContinuousMap.memLp (p := 2) haarAddCircle ℂ
      (exponentialSum M.succ * exponentialSum M.succ))

theorem localArcModelSquare_memLp_two (M P R : ℕ)
    (i : ReducedRationalIndex R) :
    MemLp (localArcModelSquare M P R i) 2 haarAddCircle := by
  let F : C(UnitAddCircle, ℂ) :=
    ⟨fun x =>
      ((((ArithmeticFunction.moebius i.val.1 : ℤ) : ℂ) /
          (Nat.totient i.val.1 : ℂ)) *
        discreteMainPolynomial M (x - majorArcCenter i)) ^ 2, by
      exact (continuous_const.mul ((discreteMainPolynomial_continuous M).comp
        (continuous_id.sub continuous_const))).pow 2⟩
  exact MemLp.indicator measurableSet_closedBall
    (ContinuousMap.memLp (p := 2) haarAddCircle ℂ F)

theorem assembledArcModelSquare_memLp_two (M P R : ℕ) :
    MemLp (assembledArcModelSquare M P R) 2 haarAddCircle := by
  unfold assembledArcModelSquare
  exact memLp_finsetSum' Finset.univ fun i _ =>
    localArcModelSquare_memLp_two M P R i

theorem majorOperatorErrorFunction_memLp_two (M P R : ℕ) :
    MemLp (majorOperatorErrorFunction M P R) 2 haarAddCircle := by
  unfold majorOperatorErrorFunction
  exact (actualMajorSquare_memLp_two M P R).sub
    (assembledArcModelSquare_memLp_two M P R)

/-- The actual Major integral is a Fourier coefficient of one fixed function. -/
theorem fourierCoeff_actualMajorSquare (M P R N : ℕ) :
    fourierCoeff (actualMajorSquare M P R) (N : ℤ) =
      ∫ x in twoScaleMajorMask M P R,
        fixedScalePairFourierIntegrand M N x ∂haarAddCircle := by
  rw [fourierCoeff, ← integral_indicator (twoScaleMajorMask_measurable M P R)]
  apply integral_congr_ae
  filter_upwards [] with x
  by_cases hx : x ∈ twoScaleMajorMask M P R
  · simp [actualMajorSquare, Set.indicator_of_mem hx,
      fixedScalePairFourierIntegrand, smul_eq_mul]
  · simp [actualMajorSquare, Set.indicator_of_notMem hx]

/-- One local model integral is a Fourier coefficient of its fixed local
square. -/
theorem fourierCoeff_localArcModelSquare (M P R N : ℕ)
    (i : ReducedRationalIndex R) :
    fourierCoeff (localArcModelSquare M P R i) (N : ℤ) =
      ∫ x in Metric.closedBall (majorArcCenter i) (twoScaleArcRadius M P i),
        shiftedArcModelIntegrand M N (majorArcCenter i)
          (((ArithmeticFunction.moebius i.val.1 : ℤ) : ℂ) /
            (Nat.totient i.val.1 : ℂ)) x ∂haarAddCircle := by
  rw [fourierCoeff, ← integral_indicator measurableSet_closedBall]
  apply integral_congr_ae
  filter_upwards [] with x
  by_cases hx : x ∈
      Metric.closedBall (majorArcCenter i) (twoScaleArcRadius M P i)
  · simp [localArcModelSquare, Set.indicator_of_mem hx,
      shiftedArcModelIntegrand, smul_eq_mul]
  · simp [localArcModelSquare, Set.indicator_of_notMem hx]

/-- The assembled model has exactly the previously fixed complex discrete
arc coefficient. -/
theorem fourierCoeff_assembledArcModelSquare (M P R N : ℕ)
    (hR : 1 ≤ R) (hscale : 2 * P * R < M) :
    fourierCoeff (assembledArcModelSquare M P R) (N : ℤ) =
      complexDiscreteArcMainModel M N R P := by
  unfold assembledArcModelSquare
  rw [fourierCoeff.sum Finset.univ _
    (fun i _ => localArcModelSquare_integrable M P R i)]
  simp only [Finset.sum_apply]
  rw [show (∑ i : ReducedRationalIndex R,
      fourierCoeff (localArcModelSquare M P R i) (N : ℤ)) =
      originalIndexArcModelSum M P R N by
        unfold originalIndexArcModelSum
        apply Finset.sum_congr rfl
        intro i _
        exact fourierCoeff_localArcModelSquare M P R N i]
  apply originalIndexArcModelSum_eq_complex_model M P R N
  exact lt_of_le_of_lt (by nlinarith [Nat.mul_le_mul_left (2 * P) hR]) hscale

/-- Exact complex coefficient identity for the first V1.8.631 channel. -/
theorem fourierCoeff_majorOperatorErrorFunction (M P R N : ℕ)
    (hR : 1 ≤ R) (hscale : 2 * P * R < M) :
    fourierCoeff (majorOperatorErrorFunction M P R) (N : ℤ) =
      (∫ x in twoScaleMajorMask M P R,
        fixedScalePairFourierIntegrand M N x ∂haarAddCircle) -
          complexDiscreteArcMainModel M N R P := by
  unfold majorOperatorErrorFunction fourierCoeff
  rw [show (fun t : UnitAddCircle =>
      fourier (-(N : ℤ)) t •
        (actualMajorSquare M P R - assembledArcModelSquare M P R) t) =
      (fun t => fourier (-(N : ℤ)) t • actualMajorSquare M P R t) -
        (fun t => fourier (-(N : ℤ)) t • assembledArcModelSquare M P R t) by
          funext t
          exact smul_sub _ _ _]
  change (∫ t : UnitAddCircle,
      fourier (-(N : ℤ)) t • actualMajorSquare M P R t -
        fourier (-(N : ℤ)) t • assembledArcModelSquare M P R t
        ∂haarAddCircle) = _
  rw [integral_sub
    ((actualMajorSquare_integrable M P R).fourier_smul _)
    ((assembledArcModelSquare_integrable M P R).fourier_smul _)]
  change fourierCoeff (actualMajorSquare M P R) (N : ℤ) -
      fourierCoeff (assembledArcModelSquare M P R) (N : ℤ) = _
  rw [fourierCoeff_actualMajorSquare,
    fourierCoeff_assembledArcModelSquare M P R N hR hscale]

/-- The real absolute value of the complex coefficient is the literal
operator-approximation error from V1.8.631. -/
theorem operatorApproximationError_eq_abs_re_fourierCoeff
    (M P R N : ℕ) (hR : 1 ≤ R) (hscale : 2 * P * R < M) :
    operatorApproximationError M P R N =
      |(fourierCoeff (majorOperatorErrorFunction M P R) (N : ℤ)).re| := by
  rw [fourierCoeff_majorOperatorErrorFunction M P R N hR hscale]
  simp only [Complex.sub_re, complexDiscreteArcMainModel_re]
  rfl

/-- Parseval identity for the frequency-independent Major error function. -/
theorem hasSum_sq_majorOperatorErrorFourierCoeff (M P R : ℕ) :
    HasSum
      (fun k : ℤ => ‖fourierCoeff (majorOperatorErrorFunction M P R) k‖ ^ 2)
      (majorOperatorErrorEnergy M P R) := by
  let h := majorOperatorErrorFunction_memLp_two M P R
  have hc := fourierCoeff_congr_ae h.coeFn_toLp
  have hi :
      (∫ x : UnitAddCircle,
        ‖h.toLp (majorOperatorErrorFunction M P R) x‖ ^ 2 ∂haarAddCircle) =
      ∫ x : UnitAddCircle,
        ‖majorOperatorErrorFunction M P R x‖ ^ 2 ∂haarAddCircle := by
    apply integral_congr_ae
    filter_upwards [h.coeFn_toLp] with x hx
    rw [hx]
  have hp := hasSum_sq_fourierCoeff
    (h.toLp (majorOperatorErrorFunction M P R))
  unfold majorOperatorErrorEnergy
  rw [hc, hi] at hp
  exact hp

/-- Bessel removes the factor `s.card` from the first-channel reduction. -/
theorem operatorApproximationSquaredMoment_le_errorEnergy
    (M P R : ℕ) (s : Finset ℕ) (hR : 1 ≤ R)
    (hscale : 2 * P * R < M) :
    operatorApproximationSquaredMoment M P R s ≤
      majorOperatorErrorEnergy M P R := by
  have hBessel := sum_le_hasSum (s.image fun N : ℕ => (N : ℤ))
    (fun k _ => sq_nonneg ‖fourierCoeff (majorOperatorErrorFunction M P R) k‖)
    (hasSum_sq_majorOperatorErrorFourierCoeff M P R)
  rw [Finset.sum_image] at hBessel
  · unfold operatorApproximationSquaredMoment
    calc
      _ ≤ ∑ N ∈ s,
          ‖fourierCoeff (majorOperatorErrorFunction M P R) (N : ℤ)‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro N _hN
        rw [operatorApproximationError_eq_abs_re_fourierCoeff M P R N hR hscale]
        have hRe := Complex.abs_re_le_norm
          (fourierCoeff (majorOperatorErrorFunction M P R) (N : ℤ))
        nlinarith [abs_nonneg
          (fourierCoeff (majorOperatorErrorFunction M P R) (N : ℤ)).re]
      _ ≤ _ := hBessel
  · intro a _ha b _hb hab
    exact Int.ofNat_inj.mp hab

end GoldbachCircleMethodMajorOperatorErrorBesselV18633
