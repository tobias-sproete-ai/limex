import GoldbachCircleMethodStructurallyAdmissibleActiveSlotV18258

/-!
# Goldbach V1.8.259: adjusted reserve on the admissible slot interface

The V1.8.256 conditional reserve theorem is retyped so callers must supply the
dependent nonprincipal, self-inverse slot introduced in V1.8.258.  The
secondary-term budget remains an explicit analytic premise.
-/

open scoped Classical BigOperators

set_option autoImplicit false

namespace GoldbachCircleMethodAdmissibleSlotAdjustedReserveV18259

open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodActiveExceptionalCenteringV18129
open GoldbachCircleMethodTwoScaleEvenBlockDefectReserveV1833
open GoldbachCircleMethodTwoSourceScaleCoverV18232
open GoldbachCircleMethodActualResidualExactDecompositionV18225
open GoldbachCircleMethodResidualScaleAdmissionV18196
open GoldbachCircleMethodQuantitativeAdmittedPrincipalReserveV18236
open GoldbachCircleMethodActiveResidualExactDecompositionV18251
open GoldbachCircleMethodAdjustedModelSecondaryTermExpansionV18255
open GoldbachCircleMethodAdjustedModelReserveInterfaceV18256
open GoldbachCircleMethodStructurallyAdmissibleActiveSlotV18258

/-- Pointwise V1.8.256 reserve, now unreachable by the conductor-one
principal slot through the public argument type. -/
theorem admissibleAdjustedModel_re_gt_target_over_1024_of_secondary_budget
    (M B : ℕ) (rho b : ℝ)
    (e : StructurallyAdmissibleActiveSlot ⌊((B : ℝ)^rho)^2⌋₊) (k : ℤ)
    (hPrincipal : (M : ℝ) / 512 < (canonicalPrincipalModelAt B rho k).re)
    (hSecondary :
      2 * |(canonicalPrincipalSecondaryCrossAt B rho b e.val k).re| +
          |(canonicalActiveSecondarySquareAt B rho b e.val k).re| <
        (M : ℝ) / 1024) :
    (M : ℝ) / 1024 < (canonicalAdjustedModelAt B rho b e.val k).re :=
  adjustedModel_re_gt_target_over_1024_of_secondary_budget
    M B rho b e.val k hPrincipal hSecondary

/-- Two-source-scale reserve with both active slots structurally admissible.
No inhabitant or secondary budget is synthesized by this theorem. -/
theorem evenTargetBlock_admissibleAdjusted_gt_target_scale_over_1024
    {K : ℕ} [NeZero K]
    (M N : ℕ) (rho : ℝ) (hM : 37 ≤ M)
    (hN : N ∈ evenTargetBlock M)
    (hrho : 0 < rho) (hrhoUpper : rho ≤ (1 : ℝ) / 10000)
    (hLow : blockThreshold rho ≤ lowerSourceScale M)
    (hHigh : blockThreshold rho ≤ upperSourceScale M)
    (hKLow : ∀ q : PositiveLevel
        ⌊((lowerSourceScale M : ℝ) ^ rho) ^ 2⌋₊, q.val ∣ K)
    (hKHigh : ∀ q : PositiveLevel
        ⌊((upperSourceScale M : ℝ) ^ rho) ^ 2⌋₊, q.val ∣ K)
    (bLow : ℝ)
    (eLow : StructurallyAdmissibleActiveSlot
      ⌊((lowerSourceScale M : ℝ)^rho)^2⌋₊)
    (bHigh : ℝ)
    (eHigh : StructurallyAdmissibleActiveSlot
      ⌊((upperSourceScale M : ℝ)^rho)^2⌋₊)
    (hLowSecondary :
      2 * |(canonicalPrincipalSecondaryCrossAt (lowerSourceScale M)
            rho bLow eLow.val (N : ℤ)).re| +
          |(canonicalActiveSecondarySquareAt (lowerSourceScale M)
            rho bLow eLow.val (N : ℤ)).re| < (M : ℝ) / 1024)
    (hHighSecondary :
      2 * |(canonicalPrincipalSecondaryCrossAt (upperSourceScale M)
            rho bHigh eHigh.val (N : ℤ)).re| +
          |(canonicalActiveSecondarySquareAt (upperSourceScale M)
            rho bHigh eHigh.val (N : ℤ)).re| < (M : ℝ) / 1024) :
    (M : ℝ) / 1024 <
        (canonicalAdjustedModelAt (lowerSourceScale M) rho bLow eLow.val
          (N : ℤ)).re ∨
      (M : ℝ) / 1024 <
        (canonicalAdjustedModelAt (upperSourceScale M) rho bHigh eHigh.val
          (N : ℤ)).re :=
  evenTargetBlock_adjusted_gt_target_scale_over_1024
    (K := K) M N rho hM hN hrho hrhoUpper hLow hHigh hKLow hKHigh
      bLow eLow.val bHigh eHigh.val hLowSecondary hHighSecondary

end GoldbachCircleMethodAdmissibleSlotAdjustedReserveV18259

