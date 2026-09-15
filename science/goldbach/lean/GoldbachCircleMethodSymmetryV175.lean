import GoldbachCircleMethodMajorMinorRealPartV174

/-!
# Circle-method symmetry and non-improvement result, V1.7.5 candidate

For the concrete V1.7.2 arcs, this module proves that negation permutes the
reduced rational centres and preserves every radius. It then proves that the
major and minor arcs are negation-invariant and that the V1.7.2 Fourier
integrand satisfies `g(-x) = conj (g x)`.

Haar-measure invariance under negation makes both set integrals real. Hence
the norm of the concrete minor integral equals the absolute value of its real
part, so the V1.7.3 norm condition and the V1.7.4 real-part condition are
equivalent for these arcs. No instance of either analytic bound is produced.
-/

set_option autoImplicit false

namespace GoldbachCircleMethodSymmetryV175

open GoldbachCircleMethodFourierIdentityV171
open GoldbachCircleMethodMajorMinorPartitionV172

/-- Every Fourier character is conjugated by negation of its argument. -/
lemma fourier_arg_neg (n : Int) (x : UnitAddCircle) :
    fourier n (-x) = star (fourier n x) := by
  rw [fourier_apply, smul_neg]
  exact fourier_neg'

/-- The finite von Mangoldt exponential sum has conjugation symmetry. -/
lemma exponentialSum_arg_neg (N : Nat) (x : UnitAddCircle) :
    exponentialSum N (-x) = star (exponentialSum N x) := by
  simp only [exponentialSum, ContinuousMap.sum_apply]
  change (∑ n ∈ Finset.range N,
    (ArithmeticFunction.vonMangoldt n : Complex) • fourier (n : Int) (-x)) =
    (starRingEnd Complex) (∑ n ∈ Finset.range N,
      (ArithmeticFunction.vonMangoldt n : Complex) • fourier (n : Int) x)
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro n hn
  simp only [smul_eq_mul, map_mul, Complex.conj_ofReal]
  congr 1
  exact fourier_arg_neg (n : Int) x

/-- The exact V1.7.2 pair integrand is conjugated by argument negation. -/
theorem pairFourierIntegrand_arg_neg (N : Nat) (x : UnitAddCircle) :
    pairFourierIntegrand N (-x) = star (pairFourierIntegrand N x) := by
  unfold pairFourierIntegrand
  change
    fourier (-(N : Int)) (-x) *
        (exponentialSum N.succ (-x) * exponentialSum N.succ (-x)) =
      (starRingEnd Complex)
        (fourier (-(N : Int)) x *
          (exponentialSum N.succ x * exponentialSum N.succ x))
  rw [map_mul, map_mul]
  rw [fourier_arg_neg, exponentialSum_arg_neg]
  rfl

/--
Each reduced centre `a/q` has a reduced reflected centre: `0` reflects to
itself and positive `a` reflects to `(q-a)/q`. The radius is unchanged.
-/
theorem reflected_majorArc_exists (p : ArcParameters)
    (i : ReducedRationalIndex p.R) :
    ∃ j : ReducedRationalIndex p.R,
      majorArcCenter j = -majorArcCenter i ∧
      majorArcRadius p j = majorArcRadius p i := by
  have hiFilter := Finset.mem_filter.mp i.2
  have hiProduct := Finset.mem_product.mp hiFilter.1
  have hqIcc := Finset.mem_Icc.mp hiProduct.1
  have haRange := Finset.mem_range.mp hiProduct.2
  have ha_lt_q := hiFilter.2.1
  have ha_coprime_q := hiFilter.2.2
  by_cases ha0 : i.1.2 = 0
  · refine ⟨i, ?_, rfl⟩
    unfold majorArcCenter
    simp [ha0]
  · let j : ReducedRationalIndex p.R :=
      ⟨(i.1.1, i.1.1 - i.1.2), by
        unfold reducedRationalPairs
        rw [Finset.mem_filter]
        constructor
        · exact Finset.mem_product.mpr
            ⟨hiProduct.1, Finset.mem_range.mpr (by omega)⟩
        · constructor
          · omega
          · exact (Nat.coprime_self_sub_left
              (Nat.le_of_lt ha_lt_q)).mpr ha_coprime_q⟩
    refine ⟨j, ?_, ?_⟩
    · unfold majorArcCenter
      change
        ((((i.1.1 - i.1.2 : Nat) : Real) / (i.1.1 : Real) : Real) :
            UnitAddCircle) =
          -((((i.1.2 : Nat) : Real) / (i.1.1 : Real) : Real) :
            UnitAddCircle)
      have hq_ne : ((i.1.1 : Nat) : Real) ≠ 0 := by
        exact Nat.cast_ne_zero.mpr (Nat.ne_of_gt (index_denominator_pos i))
      rw [Nat.cast_sub (Nat.le_of_lt ha_lt_q)]
      have hReal :
          ((i.1.1 : Real) - (i.1.2 : Real)) / (i.1.1 : Real) =
            1 - (i.1.2 : Real) / (i.1.1 : Real) := by
        field_simp
      rw [hReal, AddCircle.coe_sub]
      simp
    · rfl

private lemma neg_mem_majorArcs_of_mem (p : ArcParameters)
    {x : UnitAddCircle} (hx : x ∈ majorArcs p) : -x ∈ majorArcs p := by
  simp only [majorArcs, Set.mem_iUnion] at hx ⊢
  rcases hx with ⟨i, hi⟩
  rcases reflected_majorArc_exists p i with ⟨j, hCenter, hRadius⟩
  refine ⟨j, ?_⟩
  rw [Metric.mem_closedBall] at hi ⊢
  rw [hCenter, hRadius, dist_neg_neg]
  exact hi

/-- Membership in the concrete major arcs is invariant under negation. -/
theorem neg_mem_majorArcs_iff (p : ArcParameters) (x : UnitAddCircle) :
    -x ∈ majorArcs p ↔ x ∈ majorArcs p := by
  constructor
  · intro hx
    have h := neg_mem_majorArcs_of_mem p hx
    simpa using h
  · exact neg_mem_majorArcs_of_mem p

/-- Membership in the concrete complementary minor arcs is negation-invariant. -/
theorem neg_mem_minorArcs_iff (p : ArcParameters) (x : UnitAddCircle) :
    -x ∈ minorArcs p ↔ x ∈ minorArcs p := by
  simp only [minorArcs, Set.mem_compl_iff, neg_mem_majorArcs_iff]

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

/-- The concrete major-arc integral equals its conjugate. -/
theorem majorIntegral_conj_eq_self (p : ArcParameters) :
    star (∫ x in majorArcs p,
      pairFourierIntegrand p.N x ∂AddCircle.haarAddCircle) =
      ∫ x in majorArcs p,
        pairFourierIntegrand p.N x ∂AddCircle.haarAddCircle := by
  exact setIntegral_conj_eq_self_of_neg_symmetry
    (majorArcs p) (majorArcs_measurable p) (neg_mem_majorArcs_iff p)
    (pairFourierIntegrand p.N) (pairFourierIntegrand_arg_neg p.N)

/-- The concrete minor-arc integral equals its conjugate. -/
theorem minorIntegral_conj_eq_self (p : ArcParameters) :
    star (∫ x in minorArcs p,
      pairFourierIntegrand p.N x ∂AddCircle.haarAddCircle) =
      ∫ x in minorArcs p,
        pairFourierIntegrand p.N x ∂AddCircle.haarAddCircle := by
  exact setIntegral_conj_eq_self_of_neg_symmetry
    (minorArcs p) (minorArcs_measurable p) (neg_mem_minorArcs_iff p)
    (pairFourierIntegrand p.N) (pairFourierIntegrand_arg_neg p.N)

/-- The concrete major-arc integral has zero imaginary part. -/
theorem majorIntegral_im_eq_zero (p : ArcParameters) :
    (∫ x in majorArcs p,
      pairFourierIntegrand p.N x ∂AddCircle.haarAddCircle).im = 0 := by
  exact Complex.conj_eq_iff_im.mp (majorIntegral_conj_eq_self p)

/-- The concrete minor-arc integral has zero imaginary part. -/
theorem minorIntegral_im_eq_zero (p : ArcParameters) :
    (∫ x in minorArcs p,
      pairFourierIntegrand p.N x ∂AddCircle.haarAddCircle).im = 0 := by
  exact Complex.conj_eq_iff_im.mp (minorIntegral_conj_eq_self p)

/-- The concrete minor integral's norm is the absolute value of its real part. -/
theorem minorIntegral_norm_eq_abs_re (p : ArcParameters) :
    ‖∫ x in minorArcs p,
      pairFourierIntegrand p.N x ∂AddCircle.haarAddCircle‖ =
      |(∫ x in minorArcs p,
        pairFourierIntegrand p.N x ∂AddCircle.haarAddCircle).re| := by
  let z : Complex :=
    ∫ x in minorArcs p,
      pairFourierIntegrand p.N x ∂AddCircle.haarAddCircle
  have hz : (z.re : Complex) = z :=
    Complex.conj_eq_iff_re.mp (minorIntegral_conj_eq_self p)
  change ‖z‖ = |z.re|
  calc
    ‖z‖ = ‖(z.re : Complex)‖ := by rw [hz]
    _ = ‖z.re‖ := Complex.norm_real z.re
    _ = |z.re| := Real.norm_eq_abs z.re

/--
For the concrete V1.7.2 arcs, the V1.7.3 norm condition and V1.7.4
real-part condition are the same proposition.
-/
theorem norm_bound_iff_realpart_bound (p : ArcParameters) :
    (4 * Real.sqrt (p.N : Real) * (Real.log (p.N : Real)) ^ 2 <
      (∫ x in majorArcs p,
        pairFourierIntegrand p.N x ∂AddCircle.haarAddCircle).re -
      ‖∫ x in minorArcs p,
        pairFourierIntegrand p.N x ∂AddCircle.haarAddCircle‖) ↔
    (4 * Real.sqrt (p.N : Real) * (Real.log (p.N : Real)) ^ 2 <
      (∫ x in majorArcs p,
        pairFourierIntegrand p.N x ∂AddCircle.haarAddCircle).re -
      |(∫ x in minorArcs p,
        pairFourierIntegrand p.N x ∂AddCircle.haarAddCircle).re|) := by
  rw [minorIntegral_norm_eq_abs_re p]

end GoldbachCircleMethodSymmetryV175
