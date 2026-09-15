import GoldbachCircleMethodMinorLocalizationSharpV177

/-!
# Exact central-band signed correlation, V1.7.8 probe

The central-band set integral is expanded into the exact finite V1.7.1
von-Mangoldt double sum. The remaining factor is the Fourier coefficient of
the central-band indicator, with its sign fixed by Mathlib's convention
`fourierCoeff f k = ∫ fourier (-k) • f`.
-/

set_option autoImplicit false

open scoped BigOperators ArithmeticFunction.vonMangoldt

namespace GoldbachCircleMethodCentralBandCorrelationV178

open GoldbachCircleMethodFourierIdentityV171
open GoldbachCircleMethodMajorMinorPartitionV172
open GoldbachCircleMethodMinorLocalizationV176
open GoldbachCircleMethodMinorLocalizationSharpV177

noncomputable def centralBandIndicator (p : ArcParameters) (Q : Nat)
    (hQ : 0 < Q) (hCoupling : p.N ≤ p.R * (Q + 1)) :
    UnitAddCircle → Complex :=
  (centralMinorBand p Q hQ hCoupling).indicator (fun _ => 1)

/-- Fourier coefficient of the concrete central-band indicator. -/
noncomputable def centralBandIndicatorCoeff (p : ArcParameters) (Q : Nat)
    (hQ : 0 < Q) (hCoupling : p.N ≤ p.R * (Q + 1))
    (k : Int) : Complex :=
  fourierCoeff (centralBandIndicator p Q hQ hCoupling) k

/-- The concrete central-band contribution to the V1.7.2 Fourier integral. -/
noncomputable def centralBandIntegral (p : ArcParameters) (Q : Nat)
    (hQ : 0 < Q) (hCoupling : p.N ≤ p.R * (Q + 1)) : Complex :=
  ∫ x in centralMinorBand p Q hQ hCoupling,
    pairFourierIntegrand p.N x ∂AddCircle.haarAddCircle

/--
Exact finite signed-correlation expression. Both indices use `range N.succ`,
matching V1.7.1. The coefficient index `N-n-m` is forced by Mathlib's
negative-frequency convention in `fourierCoeff`.
-/
noncomputable def centralBandSignedCorrelation (p : ArcParameters) (Q : Nat)
    (hQ : 0 < Q) (hCoupling : p.N ≤ p.R * (Q + 1)) : Complex :=
  ∑ n ∈ Finset.range p.N.succ,
    ∑ m ∈ Finset.range p.N.succ,
      ((ArithmeticFunction.vonMangoldt n : Complex) *
          ArithmeticFunction.vonMangoldt m) *
        centralBandIndicatorCoeff p Q hQ hCoupling
          ((p.N : Int) - (n : Int) - (m : Int))

private lemma centralBandIndicatorCoeff_eq_setIntegral_fourier
    (p : ArcParameters) (Q : Nat)
    (hQ : 0 < Q) (hCoupling : p.N ≤ p.R * (Q + 1)) (k : Int) :
    centralBandIndicatorCoeff p Q hQ hCoupling k =
      ∫ x in centralMinorBand p Q hQ hCoupling,
        fourier (-k) x ∂AddCircle.haarAddCircle := by
  let s := centralMinorBand p Q hQ hCoupling
  have hs : MeasurableSet s := centralMinorBand_measurable p Q hQ hCoupling
  have hFunction :
      (fun x : UnitAddCircle =>
        fourier (-k) x • centralBandIndicator p Q hQ hCoupling x) =
      s.indicator (fun x : UnitAddCircle => fourier (-k) x) := by
    funext x
    by_cases hx : x ∈ s
    · simp [centralBandIndicator, s, hx]
    · simp [centralBandIndicator, s, hx]
  unfold centralBandIndicatorCoeff fourierCoeff
  rw [hFunction, MeasureTheory.integral_indicator hs]

private lemma pairFourierIntegrand_eq_doubleSum (N : Nat)
    (x : UnitAddCircle) :
    pairFourierIntegrand N x =
      ∑ n ∈ Finset.range N.succ,
        ∑ m ∈ Finset.range N.succ,
          ((ArithmeticFunction.vonMangoldt n : Complex) *
              ArithmeticFunction.vonMangoldt m) *
            fourier ((n : Int) + (m : Int) - (N : Int)) x := by
  have hExponential : exponentialSum N.succ x =
      ∑ n ∈ Finset.range N.succ,
        (ArithmeticFunction.vonMangoldt n : Complex) * fourier (n : Int) x := by
    simp [exponentialSum]
  unfold pairFourierIntegrand
  rw [hExponential]
  rw [Finset.sum_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [Finset.mul_sum]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  calc
    (fourier (-(N : Int))) x *
        ((ArithmeticFunction.vonMangoldt n : Complex) * fourier (n : Int) x *
          ((ArithmeticFunction.vonMangoldt m : Complex) * fourier (m : Int) x)) =
      ((ArithmeticFunction.vonMangoldt n : Complex) *
          ArithmeticFunction.vonMangoldt m) *
        (((fourier (-(N : Int))) x * fourier (n : Int) x) *
          fourier (m : Int) x) := by ring_nf
    _ = ((ArithmeticFunction.vonMangoldt n : Complex) *
          ArithmeticFunction.vonMangoldt m) *
        fourier ((n : Int) + (m : Int) - (N : Int)) x := by
      rw [← fourier_add, ← fourier_add]
      congr 2
      ring_nf

private lemma const_mul_fourier_integrableOn
    (s : Set UnitAddCircle) (c : Complex) (k : Int) :
    MeasureTheory.IntegrableOn
      (fun x : UnitAddCircle => c * fourier k x) s
      AddCircle.haarAddCircle := by
  have hContinuous : Continuous (fun x : UnitAddCircle => c * fourier k x) :=
    continuous_const.mul (fourier k).continuous
  have hIntegrable : MeasureTheory.Integrable
      (fun x : UnitAddCircle => c * fourier k x)
      AddCircle.haarAddCircle := by
    simpa only [MeasureTheory.IntegrableOn,
      MeasureTheory.Measure.restrict_univ] using
      (ContinuousOn.integrableOn_compact
        (μ := AddCircle.haarAddCircle)
        (K := Set.univ) isCompact_univ hContinuous.continuousOn)
  exact hIntegrable.integrableOn

/-- The central-band integral is exactly the finite signed correlation. -/
theorem centralBandIntegral_eq_signedCorrelation (p : ArcParameters) (Q : Nat)
    (hQ : 0 < Q) (hCoupling : p.N ≤ p.R * (Q + 1)) :
    centralBandIntegral p Q hQ hCoupling =
      centralBandSignedCorrelation p Q hQ hCoupling := by
  let s := centralMinorBand p Q hQ hCoupling
  unfold centralBandIntegral centralBandSignedCorrelation
  rw [MeasureTheory.setIntegral_congr_fun
    (centralMinorBand_measurable p Q hQ hCoupling)
    (fun x hx => pairFourierIntegrand_eq_doubleSum p.N x)]
  rw [MeasureTheory.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro n hn
    rw [MeasureTheory.integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro m hm
      rw [MeasureTheory.integral_const_mul]
      have hFrequency :
          (n : Int) + (m : Int) - (p.N : Int) =
            -((p.N : Int) - (n : Int) - (m : Int)) := by
        ring_nf
      rw [hFrequency]
      rw [← centralBandIndicatorCoeff_eq_setIntegral_fourier]
    · intro m hm
      exact const_mul_fourier_integrableOn s _ _
  · intro n hn
    have hFunction :
        (fun x : UnitAddCircle =>
          ∑ m ∈ Finset.range p.N.succ,
            ((ArithmeticFunction.vonMangoldt n : Complex) *
                ArithmeticFunction.vonMangoldt m) *
              fourier ((n : Int) + (m : Int) - (p.N : Int)) x) =
          ∑ m ∈ Finset.range p.N.succ,
            (fun x : UnitAddCircle =>
              ((ArithmeticFunction.vonMangoldt n : Complex) *
                  ArithmeticFunction.vonMangoldt m) *
                fourier ((n : Int) + (m : Int) - (p.N : Int)) x) := by
      funext x
      simp only [Finset.sum_apply]
    rw [hFunction]
    exact MeasureTheory.integrable_finsetSum'
      (Finset.range p.N.succ) fun m hm =>
        const_mul_fourier_integrableOn s _ _

private lemma setIntegral_conj_eq_self_of_neg_symmetry
    (s : Set UnitAddCircle)
    (hs : MeasurableSet s)
    (hSet : ∀ x : UnitAddCircle, -x ∈ s ↔ x ∈ s)
    (f : UnitAddCircle → Complex)
    (hFun : ∀ x : UnitAddCircle, f (-x) = star (f x)) :
    star (∫ x in s, f x ∂AddCircle.haarAddCircle) =
      ∫ x in s, f x ∂AddCircle.haarAddCircle := by
  have hIndicator : ∀ x : UnitAddCircle,
      s.indicator f (-x) = star (s.indicator f x) := by
    intro x
    by_cases hx : x ∈ s
    · have hnx : -x ∈ s := (hSet x).mpr hx
      rw [Set.indicator_of_mem hx, Set.indicator_of_mem hnx, hFun]
    · have hnx : -x ∉ s := by
        simpa [hSet x] using hx
      simp [Set.indicator, hx, hnx]
  have hNegIntegral :
      (∫ x : UnitAddCircle, s.indicator f (-x) ∂AddCircle.haarAddCircle) =
        ∫ x : UnitAddCircle, s.indicator f x ∂AddCircle.haarAddCircle := by
    exact (MeasureTheory.Measure.measurePreserving_neg
      AddCircle.haarAddCircle).integral_comp'
        (f := MeasurableEquiv.neg UnitAddCircle) (s.indicator f)
  calc
    star (∫ x in s, f x ∂AddCircle.haarAddCircle) =
        star (∫ x : UnitAddCircle,
          s.indicator f x ∂AddCircle.haarAddCircle) := by
      rw [MeasureTheory.integral_indicator hs]
    _ = ∫ x : UnitAddCircle,
          star (s.indicator f x) ∂AddCircle.haarAddCircle := by
      exact integral_conj.symm
    _ = ∫ x : UnitAddCircle,
          s.indicator f (-x) ∂AddCircle.haarAddCircle := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards [] with x
      exact (hIndicator x).symm
    _ = ∫ x : UnitAddCircle,
          s.indicator f x ∂AddCircle.haarAddCircle := hNegIntegral
    _ = ∫ x in s, f x ∂AddCircle.haarAddCircle := by
      exact MeasureTheory.integral_indicator hs

/-- The concrete central-band contribution equals its complex conjugate. -/
theorem centralBandIntegral_conj_eq_self (p : ArcParameters) (Q : Nat)
    (hQ : 0 < Q) (hCoupling : p.N ≤ p.R * (Q + 1)) :
    star (centralBandIntegral p Q hQ hCoupling) =
      centralBandIntegral p Q hQ hCoupling := by
  exact setIntegral_conj_eq_self_of_neg_symmetry
    (centralMinorBand p Q hQ hCoupling)
    (centralMinorBand_measurable p Q hQ hCoupling)
    (neg_mem_centralMinorBand_iff p Q hQ hCoupling)
    (pairFourierIntegrand p.N)
    (GoldbachCircleMethodSymmetryV175.pairFourierIntegrand_arg_neg p.N)

/-- The concrete central-band contribution has zero imaginary part. -/
theorem centralBandIntegral_im_eq_zero (p : ArcParameters) (Q : Nat)
    (hQ : 0 < Q) (hCoupling : p.N ≤ p.R * (Q + 1)) :
    (centralBandIntegral p Q hQ hCoupling).im = 0 := by
  exact Complex.conj_eq_iff_im.mp
    (centralBandIntegral_conj_eq_self p Q hQ hCoupling)

/-- The equal finite signed-correlation expression is real as well. -/
theorem centralBandSignedCorrelation_im_eq_zero (p : ArcParameters) (Q : Nat)
    (hQ : 0 < Q) (hCoupling : p.N ≤ p.R * (Q + 1)) :
    (centralBandSignedCorrelation p Q hQ hCoupling).im = 0 := by
  rw [← centralBandIntegral_eq_signedCorrelation p Q hQ hCoupling]
  exact centralBandIntegral_im_eq_zero p Q hQ hCoupling

end GoldbachCircleMethodCentralBandCorrelationV178
