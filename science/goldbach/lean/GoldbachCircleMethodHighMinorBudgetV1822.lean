import GoldbachCircleMethodQStarBooleanGeometryV185

/-!
# Exact high-denominator budget interface, V1.8.22

This module attaches the high-denominator bookkeeping directly to the concrete
V1.7.1 Fourier integrand and the V1.8.5 denominator cover. It proves only:

* measurability of the finite denominator cover;
* the exact real-part partition into the cover and its complement;
* an exact restatement of the pointwise Goldbach target; and
* a conditional, noncircular error-budget theorem using V1.6.1's proved
  prime-power defect bound.

It constructs no analytic high-band estimate and proves no uniform Goldbach
statement.
-/

set_option autoImplicit false

namespace GoldbachCircleMethodHighMinorBudgetV1822

open GoldbachPurePrimeAdequacyV15
open GoldbachVonMangoldtDecompositionV16
open GoldbachPrimePowerDefectBoundV161
open GoldbachCircleMethodFourierIdentityV171
open GoldbachCircleMethodMajorMinorPartitionV172
open GoldbachCircleMethodMinorLocalizationV176
open GoldbachCircleMethodQStarBooleanGeometryV185

/-- The V1.8.5 finite denominator cover is measurable. -/
theorem denominatorCover_measurable (p : ArcParameters) (Q U : Nat) :
    MeasurableSet (denominatorCover p Q U) := by
  unfold denominatorCover
  rw [measurableSet_setOfPred]
  exact Measurable.exists fun q =>
    measurable_const.and (denominatorAdmissible_measurable p Q q)

/-- Under the Dirichlet-existence hypotheses, the cover is exactly the
sublevel set of the least admissible denominator. -/
theorem denominatorCover_eq_qStar_sublevel
    (p : ArcParameters) (Q : Nat)
    (hQ : 0 < Q) (hCoupling : p.N ≤ p.R * (Q + 1)) (U : Nat) :
    denominatorCover p Q U =
      {x | qStar p Q hQ hCoupling x ≤ U} := by
  ext x
  simp only [denominatorCover, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨q, hqU, hqAdmissible⟩
    exact (qStar_min p Q hQ hCoupling x hqAdmissible).trans hqU
  · intro hStar
    exact ⟨qStar p Q hQ hCoupling x, hStar,
      qStar_spec p Q hQ hCoupling x⟩

/-- Consequently the complementary integration domain is exactly `qStar > U`. -/
theorem high_complement_eq_qStar_strict_superlevel
    (p : ArcParameters) (Q : Nat)
    (hQ : 0 < Q) (hCoupling : p.N ≤ p.R * (Q + 1)) (U : Nat) :
    (denominatorCover p Q U)ᶜ =
      {x | U < qStar p Q hQ hCoupling x} := by
  rw [denominatorCover_eq_qStar_sublevel p Q hQ hCoupling U]
  ext x
  simp only [Set.mem_compl_iff, Set.mem_ofPred_eq]
  omega

/-- Real part of the exact V1.7.1 integrand over denominators at most `U`. -/
noncomputable def lowerIntegralReal
    (p : ArcParameters) (Q U : Nat) : Real :=
  Complex.re
    (∫ x in denominatorCover p Q U,
      pairFourierIntegrand p.N x ∂AddCircle.haarAddCircle)

/-- Real part of the same integrand over the complementary high band. -/
noncomputable def highIntegralReal
    (p : ArcParameters) (Q U : Nat) : Real :=
  Complex.re
    (∫ x in (denominatorCover p Q U)ᶜ,
      pairFourierIntegrand p.N x ∂AddCircle.haarAddCircle)

/--
Exact real-part partition. This is a measure-theoretic identity, not an
estimate on either band.
-/
theorem lower_add_high_eq_vonMangoldtPairSum
    (p : ArcParameters) (Q U : Nat) :
    lowerIntegralReal p Q U + highIntegralReal p Q U =
      vonMangoldtPairSum p.N := by
  have hSplit :
      (∫ x in denominatorCover p Q U,
          pairFourierIntegrand p.N x ∂AddCircle.haarAddCircle) +
        (∫ x in (denominatorCover p Q U)ᶜ,
          pairFourierIntegrand p.N x ∂AddCircle.haarAddCircle) =
        ∫ x : UnitAddCircle,
          pairFourierIntegrand p.N x ∂AddCircle.haarAddCircle := by
    exact MeasureTheory.integral_add_compl
      (denominatorCover_measurable p Q U)
      (pairFourierIntegrand_integrable p.N)
  have hFull :
      (∫ x : UnitAddCircle,
          pairFourierIntegrand p.N x ∂AddCircle.haarAddCircle) =
        (vonMangoldtPairSum p.N : Complex) :=
    integral_pairFourierIntegrand_eq_vonMangoldtPairSum p.N
  have hComplex := hSplit.trans hFull
  calc
    lowerIntegralReal p Q U + highIntegralReal p Q U =
        Complex.re
          ((∫ x in denominatorCover p Q U,
              pairFourierIntegrand p.N x ∂AddCircle.haarAddCircle) +
            (∫ x in (denominatorCover p Q U)ᶜ,
              pairFourierIntegrand p.N x ∂AddCircle.haarAddCircle)) := by
          simp [lowerIntegralReal, highIntegralReal]
    _ = Complex.re (vonMangoldtPairSum p.N : Complex) :=
      congrArg Complex.re hComplex
    _ = vonMangoldtPairSum p.N := by simp

/--
The exact target restatement for the concrete lower/high partition. The right
side is not an analytic estimate: using this equivalence backwards as if it
were one would be circular.
-/
theorem goldbachAt_iff_high_gt_defect_sub_lower
    (p : ArcParameters) (Q U : Nat) :
    GoldbachAt p.N ↔
      highIntegralReal p Q U >
        primePowerDefect p.N - lowerIntegralReal p Q U := by
  rw [← purePrimeSum_pos_iff_strictGoldbach]
  have hPartition := lower_add_high_eq_vonMangoldtPairSum p Q U
  have hDecomposition :=
    vonMangoldtPairSum_eq_purePrimeSum_add_primePowerDefect p.N
  constructor <;> intro h <;> linarith

/--
A genuinely sufficient fixed-`N` budget theorem. The hypotheses are explicit
analytic inputs; in particular this theorem does not construct the high-band
lower bound. `E_L` and `E_H` are required to be nonnegative error budgets.
-/
theorem analytic_budgets_imply_goldbachAt
    (p : ArcParameters) (Q U : Nat)
    (c eta E_L E_H : Real)
    (hN : 1 ≤ p.N)
    (hEtaPos : 0 < eta)
    (hEtaLt : eta < c)
    (hEL : 0 ≤ E_L)
    (hEH : 0 ≤ E_H)
    (hLower :
      c * (p.N : Real) - E_L ≤ lowerIntegralReal p Q U)
    (hHigh :
      -(c - eta) * (p.N : Real) - E_H ≤ highIntegralReal p Q U)
    (hBudget :
      E_L + E_H +
          4 * Real.sqrt (p.N : Real) * (Real.log (p.N : Real)) ^ 2 <
        eta * (p.N : Real)) :
    GoldbachAt p.N := by
  have hCPos : 0 < c := hEtaPos.trans hEtaLt
  have hErrorNonneg : 0 ≤ E_L + E_H := add_nonneg hEL hEH
  have hDefect := primePowerDefect_le_four_sqrt_mul_log_sq hN
  have hDefectLt :
      primePowerDefect p.N <
        lowerIntegralReal p Q U + highIntegralReal p Q U := by
    nlinarith [hCPos, hErrorNonneg]
  exact (goldbachAt_iff_high_gt_defect_sub_lower p Q U).2 (by linarith)

end GoldbachCircleMethodHighMinorBudgetV1822
