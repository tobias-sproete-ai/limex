import GoldbachCircleMethodTwoSourceScaleCoverV18232

/-!
# Goldbach V1.8.233: two-source-scale principal reserve

The exact two-scale carrier cover of V1.8.232 is combined with the actual
finite principal-model floor of V1.8.231.  Each target receives a certified
floor from at least one of two fixed source scales.  All conductor and
remainder-budget premises remain explicit.
-/

set_option autoImplicit false

namespace GoldbachCircleMethodTwoSourceScalePrincipalReserveV18233

open GoldbachCircleMethodFiniteResiduePrefixV1866
open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodActualResidualExactDecompositionV18225
open GoldbachCircleMethodActualBlockInteriorPairReserveV18231
open GoldbachCircleMethodTwoSourceScaleCoverV18232
open GoldbachCircleMethodTwoScaleEvenBlockDefectReserveV1833

/-- The explicit real-part floor attached to a source scale. -/
noncomputable def sourceScaleFloor (B : ℕ) (rho : ℝ) : ℝ :=
  (linearPairReserve B : ℝ) *
      (2 - Real.exp (Real.pi ^ 2 / 24)) -
    2 * (⌊((B : ℝ) ^ rho) ^ 2⌋₊ : ℝ) ^ 4

/-- Every even target in the historical dyadic block receives the literal
principal-model floor from at least one of the two covering source scales. -/
theorem evenTargetBlock_principal_floor_at_one_source_scale
    {K : ℕ} [NeZero K]
    (M N : ℕ) (rho : ℝ) (hM : 19 ≤ M)
    (hN : N ∈ evenTargetBlock M)
    (hRLow : 1 < (lowerSourceScale M : ℝ) ^ rho)
    (hRHigh : 1 < (upperSourceScale M : ℝ) ^ rho)
    (hKLow : ∀ q : PositiveLevel
        ⌊((lowerSourceScale M : ℝ) ^ rho) ^ 2⌋₊, q.val ∣ K)
    (hKHigh : ∀ q : PositiveLevel
        ⌊((upperSourceScale M : ℝ) ^ rho) ^ 2⌋₊, q.val ∣ K) :
    sourceScaleFloor (lowerSourceScale M) rho ≤
        (canonicalPrincipalModelAt (lowerSourceScale M) rho (N : ℤ)).re ∨
      sourceScaleFloor (upperSourceScale M) rho ≤
        (canonicalPrincipalModelAt (upperSourceScale M) rho (N : ℤ)).re := by
  have hEven : Even N := ((mem_evenTargetBlock_iff M N).mp hN).2.2.1
  rcases evenTargetBlock_two_source_scale_cover M N hM hN with hLow | hHigh
  · left
    exact canonicalPrincipalModelAt_real_floor_of_interior_reserve
      (lowerSourceScale M) N (linearPairReserve (lowerSourceScale M)) rho
      hRLow (by simp only [lowerSourceScale]; omega) hLow.1 hLow.2 hEven hKLow
  · right
    exact canonicalPrincipalModelAt_real_floor_of_interior_reserve
      (upperSourceScale M) N (linearPairReserve (upperSourceScale M)) rho
      hRHigh (by simp only [upperSourceScale]; omega) hHigh.1 hHigh.2 hEven hKHigh

/-- If the explicit floors at both candidate source scales are positive, the
actual supported principal model is positive at one covering scale for every
target in the dyadic block. -/
theorem evenTargetBlock_principal_positive_at_one_source_scale
    {K : ℕ} [NeZero K]
    (M N : ℕ) (rho : ℝ) (hM : 19 ≤ M)
    (hN : N ∈ evenTargetBlock M)
    (hRLow : 1 < (lowerSourceScale M : ℝ) ^ rho)
    (hRHigh : 1 < (upperSourceScale M : ℝ) ^ rho)
    (hKLow : ∀ q : PositiveLevel
        ⌊((lowerSourceScale M : ℝ) ^ rho) ^ 2⌋₊, q.val ∣ K)
    (hKHigh : ∀ q : PositiveLevel
        ⌊((upperSourceScale M : ℝ) ^ rho) ^ 2⌋₊, q.val ∣ K)
    (hBudgetLow : 0 < sourceScaleFloor (lowerSourceScale M) rho)
    (hBudgetHigh : 0 < sourceScaleFloor (upperSourceScale M) rho) :
    0 < (canonicalPrincipalModelAt
          (lowerSourceScale M) rho (N : ℤ)).re ∨
      0 < (canonicalPrincipalModelAt
          (upperSourceScale M) rho (N : ℤ)).re := by
  rcases evenTargetBlock_principal_floor_at_one_source_scale
    M N rho hM hN hRLow hRHigh hKLow hKHigh with hLow | hHigh
  · exact Or.inl (hBudgetLow.trans_le hLow)
  · exact Or.inr (hBudgetHigh.trans_le hHigh)

end GoldbachCircleMethodTwoSourceScalePrincipalReserveV18233
