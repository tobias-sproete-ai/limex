import GoldbachCircleMethodTwoScaleDirichletBindingV1830

/-!
# Exact fixed-scale two-scale-mask integral partition, V1.8.31

The mask is the unchanged closed-ball union from V1.8.29. The integrand is
the unchanged V1.8.24 operator at ambient cutoff M+1 and frequency N.
Only measurability and exact partition identities are proved here.
No estimate, positivity, arc disjointness, or Goldbach conclusion is asserted.
-/

set_option autoImplicit false

namespace GoldbachCircleMethodTwoScaleIntegralPartitionV1831

open GoldbachCircleMethodTwoScaleMaskAdapterV1829
open GoldbachCircleMethodFixedScaleTransferV1824
open GoldbachVonMangoldtDecompositionV16

/-- Complement of the fixed mask; independent of the target frequency. -/
noncomputable def twoScaleMinorMask (M P R0 : Nat) : Set UnitAddCircle :=
  (twoScaleMajorMask M P R0)ᶜ

theorem twoScaleMajorMask_measurable (M P R0 : Nat) :
    MeasurableSet (twoScaleMajorMask M P R0) := by
  unfold twoScaleMajorMask
  exact MeasurableSet.iUnion (fun _ => measurableSet_closedBall)

theorem twoScaleMinorMask_measurable (M P R0 : Nat) :
    MeasurableSet (twoScaleMinorMask M P R0) :=
  (twoScaleMajorMask_measurable M P R0).compl

/-- Exact split of the unchanged operator, even outside the coefficient range. -/
theorem twoScale_integral_partition (M P R0 N : Nat) :
    (∫ x in twoScaleMajorMask M P R0,
        fixedScalePairFourierIntegrand M N x ∂AddCircle.haarAddCircle) +
      (∫ x in twoScaleMinorMask M P R0,
        fixedScalePairFourierIntegrand M N x ∂AddCircle.haarAddCircle) =
      ∫ x : UnitAddCircle,
        fixedScalePairFourierIntegrand M N x ∂AddCircle.haarAddCircle := by
  unfold twoScaleMinorMask
  exact MeasureTheory.integral_add_compl
    (twoScaleMajorMask_measurable M P R0)
    (fixedScalePairFourierIntegrand_integrable M N)

/-- Exact coefficient identity on the declared target range N ≤ M. -/
theorem twoScale_integral_partition_eq_vonMangoldtPairSum
    (M P R0 N : Nat) (hNM : N ≤ M) :
    (∫ x in twoScaleMajorMask M P R0,
        fixedScalePairFourierIntegrand M N x ∂AddCircle.haarAddCircle) +
      (∫ x in twoScaleMinorMask M P R0,
        fixedScalePairFourierIntegrand M N x ∂AddCircle.haarAddCircle) =
      (vonMangoldtPairSum N : Complex) :=
  (twoScale_integral_partition M P R0 N).trans
    (integral_fixedScalePairFourierIntegrand_eq_vonMangoldtPairSum M N hNM)

/-- Real part over the exact two-scale major mask, at fixed ambient scale M. -/
noncomputable def twoScaleMajorIntegralReal (M P R0 N : Nat) : Real :=
  Complex.re (∫ x in twoScaleMajorMask M P R0,
    fixedScalePairFourierIntegrand M N x ∂AddCircle.haarAddCircle)

/-- Real part over its complement, using the identical integrand. -/
noncomputable def twoScaleMinorIntegralReal (M P R0 N : Nat) : Real :=
  Complex.re (∫ x in twoScaleMinorMask M P R0,
    fixedScalePairFourierIntegrand M N x ∂AddCircle.haarAddCircle)

/-- Exact real-part balance, not a bound on either summand. -/
theorem twoScaleMajor_add_minor_eq_vonMangoldtPairSum
    (M P R0 N : Nat) (hNM : N ≤ M) :
    twoScaleMajorIntegralReal M P R0 N +
      twoScaleMinorIntegralReal M P R0 N = vonMangoldtPairSum N := by
  have h := congrArg Complex.re
    (twoScale_integral_partition_eq_vonMangoldtPairSum M P R0 N hNM)
  simpa only [twoScaleMajorIntegralReal, twoScaleMinorIntegralReal,
    Complex.add_re, Complex.ofReal_re] using h

end GoldbachCircleMethodTwoScaleIntegralPartitionV1831
