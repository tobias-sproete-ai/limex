import GoldbachCircleMethodCompleteDecisionReductionV18627

/-!
# V1.8.628: exact signed-magnitude identity for the one-sided minor gate

The Bessel route replaces the exact negative Fourier-coefficient energy by a
larger total fourth moment.  This module makes the lost sign information
explicit.  For a real coefficient `x`, the squared negative part is exactly

`(x^2 - x * |x|) / 2`.

After summing over a finite target block, the still-open analytic input is
therefore a signed magnitude correlation, not another copy of the total-energy
bound.  No estimate of that correlation is supplied here.

`proof_status = NO_PROOF`.
-/
set_option autoImplicit false
open scoped Classical BigOperators
open GoldbachPurePrimeAdequacyV15
open GoldbachCircleMethodExceptionalTransferV1823
open GoldbachCircleMethodTwoScaleIntegralPartitionV1831
open GoldbachCircleMethodTwoScaleEvenBlockDefectReserveV1833
open GoldbachCircleMethodNegativePartSubunitGateV18626

namespace GoldbachCircleMethodSignedMagnitudeIdentityV18628

/-- Ordinary square energy on a finite real-valued carrier. -/
def squareEnergy {ι : Type*} (s : Finset ι) (H : ι → ℝ) : ℝ :=
  ∑ i ∈ s, (H i) ^ 2

/-- Sign-sensitive magnitude correlation. Negative coefficients contribute
negative square energy, positive coefficients positive square energy. -/
def signedMagnitudeCorrelation {ι : Type*} (s : Finset ι) (H : ι → ℝ) : ℝ :=
  ∑ i ∈ s, H i * |H i|

/-- Pointwise identity exposing exactly the sign information discarded by an
absolute-value or Bessel majorant. -/
theorem negativePart_sq_eq_half_square_sub_signedMagnitude (x : ℝ) :
    (negativePart x) ^ 2 = (x ^ 2 - x * |x|) / 2 := by
  by_cases hx : 0 ≤ x
  · have hneg : -x ≤ 0 := neg_nonpos.mpr hx
    rw [abs_of_nonneg hx]
    simp [negativePart, max_eq_right hneg]
    ring
  · have hxle : x ≤ 0 := le_of_not_ge hx
    have hneg : 0 ≤ -x := neg_nonneg.mpr hxle
    rw [abs_of_nonpos hxle]
    simp [negativePart, max_eq_left hneg]
    ring

/-- Exact finite identity: the one-sided energy is half the gap between total
square energy and signed magnitude correlation. -/
theorem negativePartSquaredMoment_eq_half_signed_gap
    {ι : Type*} (s : Finset ι) (H : ι → ℝ) :
    negativePartSquaredMoment s H =
      (squareEnergy s H - signedMagnitudeCorrelation s H) / 2 := by
  classical
  unfold negativePartSquaredMoment squareEnergy signedMagnitudeCorrelation
  simp_rw [negativePart_sq_eq_half_square_sub_signedMagnitude]
  rw [← Finset.sum_sub_distrib]
  simp only [Finset.sum_div]

/-- The exact strict subunit gate is equivalent to a strict signed-correlation
gap below `M^2/392`; this is not an analytic estimate. -/
theorem negativePartMoment_subunit_iff_signed_gap_subunit
    {ι : Type*} (s : Finset ι) (H : ι → ℝ) (M : ℕ) :
    negativePartSquaredMoment s H < (M : ℝ) ^ 2 / 784 ↔
      squareEnergy s H - signedMagnitudeCorrelation s H <
        (M : ℝ) ^ 2 / 392 := by
  rw [negativePartSquaredMoment_eq_half_signed_gap]
  constructor <;> intro h <;> nlinarith

/-- Exact composition with V1.8.626.  The only changed analytic interface is
the equivalent signed-correlation gap; the Major and defect gates are
unchanged. -/
theorem evenBlock_goldbachExceptions_empty_of_signedMagnitudeGap
    (M P R₀ : ℕ)
    (hLarge : defectScaleThreshold ≤ M)
    (hMajor : ∀ N ∈ evenTargetBlock M,
      (M : ℝ) / 14 ≤ twoScaleMajorIntegralReal M P R₀ N)
    (hGap :
      squareEnergy (evenTargetBlock M) (twoScaleMinorIntegralReal M P R₀) -
          signedMagnitudeCorrelation (evenTargetBlock M)
            (twoScaleMinorIntegralReal M P R₀) <
        (M : ℝ) ^ 2 / 392) :
    (evenTargetBlock M).filter (fun N => ¬ GoldbachAt N) = ∅ := by
  apply evenBlock_goldbachExceptions_empty_of_negativePartMoment M P R₀ hLarge hMajor
  exact (negativePartMoment_subunit_iff_signed_gap_subunit
    (evenTargetBlock M) (twoScaleMinorIntegralReal M P R₀) M).2 hGap

end GoldbachCircleMethodSignedMagnitudeIdentityV18628
