import GoldbachCircleMethodSignedGapBroadClassObstructionV18629

/-!
# V1.8.630: exact actual-major overshoot identity

The remaining one-sided minor moment is not an abstract sign statistic.  On
the declared coefficient range it is exactly the squared positive overshoot of
the actual Major contribution above the full von-Mangoldt convolution.

This changes no operator and supplies no estimate.  It fixes the next analytic
object in terms of two actual arithmetic quantities and prevents a return to a
generic masked-L2 argument, which V1.8.629 rules out.

`proof_status = NO_PROOF`.
-/
set_option autoImplicit false

open scoped BigOperators Classical
open GoldbachVonMangoldtDecompositionV16
open GoldbachCircleMethodExceptionalTransferV1823
open GoldbachCircleMethodTwoScaleIntegralPartitionV1831
open GoldbachCircleMethodTwoScaleEvenBlockDefectReserveV1833

namespace GoldbachCircleMethodActualMajorOvershootIdentityV18630

/-- Positive part of the amount by which the actual Major coefficient exceeds
the full nonnegative von-Mangoldt coefficient. -/
noncomputable def actualMajorOvershoot (M P R₀ N : ℕ) : ℝ :=
  max (twoScaleMajorIntegralReal M P R₀ N - vonMangoldtPairSum N) 0

/-- Pointwise exact identity on the literal coefficient range. -/
theorem negativePart_minor_eq_actualMajorOvershoot
    (M P R₀ N : ℕ) (hNM : N ≤ M) :
    negativePart (twoScaleMinorIntegralReal M P R₀ N) =
      actualMajorOvershoot M P R₀ N := by
  have hBalance := twoScaleMajor_add_minor_eq_vonMangoldtPairSum M P R₀ N hNM
  unfold negativePart actualMajorOvershoot
  congr 1
  linarith

/-- Finite squared overshoot on a declared target carrier. -/
noncomputable def actualMajorOvershootSquaredMoment
    (M P R₀ : ℕ) (s : Finset ℕ) : ℝ :=
  ∑ N ∈ s, (actualMajorOvershoot M P R₀ N) ^ 2

/-- Exact carrier identity; no inequality or asymptotic input is used. -/
theorem negativePartSquaredMoment_eq_actualMajorOvershootSquaredMoment
    (M P R₀ : ℕ) (s : Finset ℕ)
    (hRange : ∀ N ∈ s, N ≤ M) :
    negativePartSquaredMoment s (twoScaleMinorIntegralReal M P R₀) =
      actualMajorOvershootSquaredMoment M P R₀ s := by
  unfold negativePartSquaredMoment actualMajorOvershootSquaredMoment
  apply Finset.sum_congr rfl
  intro N hN
  rw [negativePart_minor_eq_actualMajorOvershoot M P R₀ N (hRange N hN)]

/-- Specialization to the already fixed even target block. -/
theorem evenBlock_negativePartMoment_eq_actualMajorOvershootMoment
    (M P R₀ : ℕ) :
    negativePartSquaredMoment (evenTargetBlock M)
        (twoScaleMinorIntegralReal M P R₀) =
      actualMajorOvershootSquaredMoment M P R₀ (evenTargetBlock M) := by
  apply negativePartSquaredMoment_eq_actualMajorOvershootSquaredMoment
  intro N hN
  exact ((mem_evenTargetBlock_iff M N).1 hN).2.1

end GoldbachCircleMethodActualMajorOvershootIdentityV18630
