import GoldbachCircleMethodTwoScaleCenteredContractMismatchV18241

/-!
# Goldbach V1.8.242: three-scale centered-contract cover

This module repairs the V1.8.241 signature mismatch.  Three explicit source
scales cover every target in the historical dyadic block while simultaneously
satisfying both the true convolution-interior reserve and the separate
`5B ≤ 4N ≤ 7B` band required by the existing centered-error estimate.

This is finite arithmetic geometry only.  It does not prove any source-family
estimate or centered-error smallness.
-/

set_option autoImplicit false

namespace GoldbachCircleMethodThreeScaleCenteredContractCoverV18242

open GoldbachCircleMethodTwoScaleEvenBlockDefectReserveV1833
open GoldbachCircleMethodActualBlockInteriorPairReserveV18231
open GoldbachCircleMethodTwoSourceScaleCoverV18232

/-- Lower analytic source scale; its admissible centered-error band begins at
the lower endpoint `M/2` of the target block. -/
def analyticLowerSourceScale (M : ℕ) : ℕ := 2 * M / 5

/-- Middle analytic source scale bridging the two outer ranges. -/
def analyticMiddleSourceScale (M : ℕ) : ℕ := M / 2

/-- Upper analytic source scale, rounded upward so `4M ≤ 7B` holds even at
the closed upper endpoint of the target block. -/
def analyticUpperSourceScale (M : ℕ) : ℕ := (4 * M + 6) / 7

/-- The same conservative one-eighth pair reserve used by the repaired
principal-model geometry. -/
def analyticPairReserve (B : ℕ) : ℕ := B / 8

/-- All arithmetic conditions needed by both the principal forcing theorem
and the existing centered-error estimate at one source scale. -/
def AnalyticCompatibleCover (M B N : ℕ) : Prop :=
  M ≤ 4 * B ∧
    1 ≤ analyticPairReserve B ∧
    HasInteriorPairReserve B N (analyticPairReserve B) ∧
    5 * B ≤ 4 * N ∧
    4 * N ≤ 7 * B

/-- Three fixed source scales cover the complete even dyadic target block
inside the exact analytic signature.  No asymptotic notation is used. -/
theorem evenTargetBlock_three_scale_analytic_cover
    (M N : ℕ) (hM : 128 ≤ M) (hN : N ∈ evenTargetBlock M) :
    AnalyticCompatibleCover M (analyticLowerSourceScale M) N ∨
      AnalyticCompatibleCover M (analyticMiddleSourceScale M) N ∨
      AnalyticCompatibleCover M (analyticUpperSourceScale M) N := by
  rcases (mem_evenTargetBlock_iff M N).mp hN with
    ⟨hN4, hNM, hEven, hLower⟩
  by_cases hFirst : 8 * N ≤ 5 * M
  · left
    simp only [AnalyticCompatibleCover, analyticLowerSourceScale,
      analyticPairReserve, HasInteriorPairReserve]
    omega
  · by_cases hSecond : 4 * N ≤ 3 * M
    · right
      left
      simp only [AnalyticCompatibleCover, analyticMiddleSourceScale,
        analyticPairReserve, HasInteriorPairReserve]
      omega
    · right
      right
      simp only [AnalyticCompatibleCover, analyticUpperSourceScale,
        analyticPairReserve, HasInteriorPairReserve]
      omega

/-- The cover also exposes the lower source-to-target comparison required
by the exact natural-target convolution identity. -/
theorem selected_analytic_cover_implies_source_le_target
    (M B N : ℕ) (h : AnalyticCompatibleCover M B N) : B ≤ N := by
  simp only [AnalyticCompatibleCover] at h
  omega

end GoldbachCircleMethodThreeScaleCenteredContractCoverV18242
