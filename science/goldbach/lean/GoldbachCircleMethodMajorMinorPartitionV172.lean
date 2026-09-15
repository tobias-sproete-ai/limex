import GoldbachCircleMethodFourierIdentityV171

/-!
# Concrete finite major/minor-arc partition, V1.7.2 candidate

This module defines the major arcs as a finite union of closed metric balls on
`UnitAddCircle`, centred at reduced rationals `a/q` with `1 ≤ q ≤ R` and
`0 ≤ a < q`. The radius is exactly `R / (q * N)`, with the same natural-number
cutoff `R` cast to `Real`. The parameter record makes `N` and `R` positive
before the sets exist.

The module proves measurability and the exact set-integral partition for the
V1.7.1 Fourier integrand. It contains no major-arc estimate, minor-arc
estimate, asymptotic formula, or Goldbach proof.
-/

set_option autoImplicit false

open scoped BigOperators ArithmeticFunction.vonMangoldt

namespace GoldbachCircleMethodMajorMinorPartitionV172

open GoldbachCircleMethodFourierIdentityV171
open GoldbachVonMangoldtDecompositionV16

/-- Parameters for one pointwise finite arc partition. -/
structure ArcParameters where
  N : Nat
  R : Nat
  N_pos : 0 < N
  R_pos : 0 < R

/-- Reduced pairs `(q,a)` with `1 ≤ q ≤ Q`, `a < q`, and `gcd(a,q)=1`. -/
def reducedRationalPairs (Q : Nat) : Finset (Nat × Nat) :=
  ((Finset.Icc 1 Q).product (Finset.range Q)).filter
    (fun qa => qa.2 < qa.1 ∧ Nat.Coprime qa.2 qa.1)

/-- A finite index carrying its proof of membership in the reduced-pair set. -/
abbrev ReducedRationalIndex (Q : Nat) :=
  {qa : Nat × Nat // qa ∈ reducedRationalPairs Q}

/-- Every indexed denominator is strictly positive. -/
lemma index_denominator_pos {Q : Nat} (i : ReducedRationalIndex Q) :
    0 < i.1.1 := by
  have hp := (Finset.mem_filter.mp i.2).1
  have hq := (Finset.mem_product.mp hp).1
  exact Nat.zero_lt_of_lt (Finset.mem_Icc.mp hq).1

/-- The point `a/q` in `ℝ/ℤ`, with `q > 0` supplied by the index. -/
noncomputable def majorArcCenter {Q : Nat} (i : ReducedRationalIndex Q) :
    UnitAddCircle :=
  (((i.1.2 : Nat) : Real) / ((i.1.1 : Nat) : Real) : Real)

/-- The exact circle-method radius `R/(q*N)`. -/
noncomputable def majorArcRadius (p : ArcParameters)
    (i : ReducedRationalIndex p.R) : Real :=
  (p.R : Real) / (((i.1.1 : Nat) : Real) * (p.N : Real))

/-- The radius denominator is nonzero for every admitted parameter/index. -/
lemma majorArcRadius_denominator_ne_zero (p : ArcParameters)
    (i : ReducedRationalIndex p.R) :
    (((i.1.1 : Nat) : Real) * (p.N : Real)) ≠ 0 := by
  exact mul_ne_zero
    (Nat.cast_ne_zero.mpr (Nat.ne_of_gt (index_denominator_pos i)))
    (Nat.cast_ne_zero.mpr (Nat.ne_of_gt p.N_pos))

/-- Finite union of closed torus balls around the admitted reduced rationals. -/
def majorArcs (p : ArcParameters) : Set UnitAddCircle :=
  ⋃ i : ReducedRationalIndex p.R,
    Metric.closedBall (majorArcCenter i) (majorArcRadius p i)

/-- The minor arcs are exactly the set-theoretic complement of the major arcs. -/
def minorArcs (p : ArcParameters) : Set UnitAddCircle :=
  (majorArcs p)ᶜ

/-- The finite union of closed major arcs is measurable. -/
lemma majorArcs_measurable (p : ArcParameters) : MeasurableSet (majorArcs p) := by
  unfold majorArcs
  exact MeasurableSet.iUnion (fun i => measurableSet_closedBall)

/-- The complementary minor arcs are measurable. -/
lemma minorArcs_measurable (p : ArcParameters) : MeasurableSet (minorArcs p) := by
  exact (majorArcs_measurable p).compl

/-- The exact integrand defining the `N`-th coefficient of the V1.7.1 square. -/
noncomputable def pairFourierIntegrand (N : Nat) (x : UnitAddCircle) : Complex :=
  fourier (-(N : Int)) x *
    (exponentialSum N.succ x * exponentialSum N.succ x)

/-- The finite Fourier integrand is Haar-integrable. -/
lemma pairFourierIntegrand_integrable (N : Nat) :
    MeasureTheory.Integrable (pairFourierIntegrand N) AddCircle.haarAddCircle := by
  have hContinuous : Continuous (pairFourierIntegrand N) :=
    (fourier (-(N : Int))).continuous.mul
      ((exponentialSum N.succ).continuous.mul (exponentialSum N.succ).continuous)
  simpa only [MeasureTheory.IntegrableOn,
    MeasureTheory.Measure.restrict_univ] using
    (ContinuousOn.integrableOn_compact
      (μ := AddCircle.haarAddCircle)
      (K := Set.univ) isCompact_univ hContinuous.continuousOn)

/-- V1.7.1 identifies the full integral with the bound von Mangoldt pair sum. -/
lemma integral_pairFourierIntegrand_eq_vonMangoldtPairSum (N : Nat) :
    (∫ x : UnitAddCircle, pairFourierIntegrand N x ∂AddCircle.haarAddCircle) =
      (vonMangoldtPairSum N : Complex) := by
  rw [← fourierCoeff_exponentialSum_sq_eq_vonMangoldtPairSum N]
  rfl

/--
Exact measurable partition of the V1.7.1 integral into the concrete major and
minor arcs. Neither summand is estimated here.
-/
theorem major_minor_integral_partition (p : ArcParameters) :
    (∫ x in majorArcs p, pairFourierIntegrand p.N x ∂AddCircle.haarAddCircle) +
      (∫ x in minorArcs p, pairFourierIntegrand p.N x ∂AddCircle.haarAddCircle) =
        (vonMangoldtPairSum p.N : Complex) := by
  rw [minorArcs]
  rw [MeasureTheory.integral_add_compl (majorArcs_measurable p)
    (pairFourierIntegrand_integrable p.N)]
  exact integral_pairFourierIntegrand_eq_vonMangoldtPairSum p.N

end GoldbachCircleMethodMajorMinorPartitionV172
