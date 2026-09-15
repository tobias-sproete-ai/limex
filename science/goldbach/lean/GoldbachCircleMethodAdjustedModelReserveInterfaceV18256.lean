import GoldbachCircleMethodAdjustedModelSecondaryTermExpansionV18255

/-!
# Goldbach V1.8.256: adjusted-model reserve interface

The exact V1.8.255 expansion is converted into a quantitative reserve gate.
The gate exposes the complete budget needed for the active secondary cross
and square terms; it does not construct that budget.
-/

open scoped Classical BigOperators

set_option autoImplicit false

namespace GoldbachCircleMethodAdjustedModelReserveInterfaceV18256

open GoldbachCircleMethodFiniteResiduePrefixV1866
open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodActiveExceptionalCenteringV18129
open GoldbachCircleMethodTwoScaleEvenBlockDefectReserveV1833
open GoldbachCircleMethodTwoSourceScaleCoverV18232
open GoldbachCircleMethodActualResidualExactDecompositionV18225
open GoldbachCircleMethodResidualScaleAdmissionV18196
open GoldbachCircleMethodQuantitativeAdmittedPrincipalReserveV18236
open GoldbachCircleMethodActiveResidualExactDecompositionV18251
open GoldbachCircleMethodAdjustedModelSecondaryTermExpansionV18255

/-- Pointwise reserve transfer.  Losing at most `M/1024` through the active
cross and square terms preserves an adjusted reserve of `M/1024` from a
principal reserve of `M/512`. -/
theorem adjustedModel_re_gt_target_over_1024_of_secondary_budget
    (M B : ℕ) (rho b : ℝ)
    (e : CharacterSlot ⌊((B : ℝ)^rho)^2⌋₊) (k : ℤ)
    (hPrincipal : (M : ℝ) / 512 < (canonicalPrincipalModelAt B rho k).re)
    (hSecondary :
      2 * |(canonicalPrincipalSecondaryCrossAt B rho b e k).re| +
          |(canonicalActiveSecondarySquareAt B rho b e k).re| <
        (M : ℝ) / 1024) :
    (M : ℝ) / 1024 < (canonicalAdjustedModelAt B rho b e k).re := by
  have hEq :
      (canonicalAdjustedModelAt B rho b e k).re =
        (canonicalPrincipalModelAt B rho k).re -
          2 * (canonicalPrincipalSecondaryCrossAt B rho b e k).re +
          (canonicalActiveSecondarySquareAt B rho b e k).re := by
    rw [canonicalAdjustedModelAt_eq_principal_sub_cross_add_secondarySquare]
    norm_num
  have hCross := le_abs_self (canonicalPrincipalSecondaryCrossAt B rho b e k).re
  have hSquare := neg_abs_le (canonicalActiveSecondarySquareAt B rho b e k).re
  rw [hEq]
  linarith

/-- Two-source-scale adjusted reserve, conditional only on the displayed
secondary budgets at both candidate scales. -/
theorem evenTargetBlock_adjusted_gt_target_scale_over_1024
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
    (eLow : CharacterSlot ⌊((lowerSourceScale M : ℝ)^rho)^2⌋₊)
    (bHigh : ℝ)
    (eHigh : CharacterSlot ⌊((upperSourceScale M : ℝ)^rho)^2⌋₊)
    (hLowSecondary :
      2 * |(canonicalPrincipalSecondaryCrossAt (lowerSourceScale M)
            rho bLow eLow (N : ℤ)).re| +
          |(canonicalActiveSecondarySquareAt (lowerSourceScale M)
            rho bLow eLow (N : ℤ)).re| < (M : ℝ) / 1024)
    (hHighSecondary :
      2 * |(canonicalPrincipalSecondaryCrossAt (upperSourceScale M)
            rho bHigh eHigh (N : ℤ)).re| +
          |(canonicalActiveSecondarySquareAt (upperSourceScale M)
            rho bHigh eHigh (N : ℤ)).re| < (M : ℝ) / 1024) :
    (M : ℝ) / 1024 <
        (canonicalAdjustedModelAt (lowerSourceScale M) rho bLow eLow
          (N : ℤ)).re ∨
      (M : ℝ) / 1024 <
        (canonicalAdjustedModelAt (upperSourceScale M) rho bHigh eHigh
          (N : ℤ)).re := by
  rcases evenTargetBlock_principal_gt_target_scale_over_five_twelve
      (K := K) M N rho hM hN hrho hrhoUpper hLow hHigh hKLow hKHigh with
    hPrincipalLow | hPrincipalHigh
  · exact Or.inl
      (adjustedModel_re_gt_target_over_1024_of_secondary_budget
        M (lowerSourceScale M) rho bLow eLow (N : ℤ)
        hPrincipalLow hLowSecondary)
  · exact Or.inr
      (adjustedModel_re_gt_target_over_1024_of_secondary_budget
        M (upperSourceScale M) rho bHigh eHigh (N : ℤ)
        hPrincipalHigh hHighSecondary)

end GoldbachCircleMethodAdjustedModelReserveInterfaceV18256
