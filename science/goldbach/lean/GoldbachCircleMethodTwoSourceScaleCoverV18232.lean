import GoldbachCircleMethodActualBlockInteriorPairReserveV18231

/-!
# Goldbach V1.8.232: two-source-scale cover

This module repairs the scale mismatch isolated in V1.8.230.  It proves that
two explicit source scales cover every even target in the historical dyadic
block once `M ≥ 19`.  Each covered target lies inside a true self-convolution
interior band with a positive pair reserve equal to one eighth of the selected
source scale.

This is finite carrier geometry only.  It does not supply analytic estimates
uniformly over the two source scales.
-/

set_option autoImplicit false

namespace GoldbachCircleMethodTwoSourceScaleCoverV18232

open GoldbachCircleMethodTwoScaleEvenBlockDefectReserveV1833
open GoldbachCircleMethodActualBlockInteriorPairReserveV18231
open GoldbachCircleMethodBlockPairCarrierV18227

/-- Lower source scale used for the lower portion of the target block. -/
def lowerSourceScale (M : ℕ) : ℕ := 7 * M / 16

/-- Upper source scale used for the upper portion of the target block. -/
def upperSourceScale (M : ℕ) : ℕ := 8 * M / 15

/-- Concrete linear lattice reserve inside a source self-convolution. -/
def linearPairReserve (B : ℕ) : ℕ := B / 8

/-- Exact arithmetic cover of the old dyadic target block by two genuine
source-block interiors.  Positivity of the selected reserve is part of each
branch and therefore cannot be lost at small scales. -/
theorem evenTargetBlock_two_source_scale_cover
    (M N : ℕ) (hM : 19 ≤ M) (hN : N ∈ evenTargetBlock M) :
    (1 ≤ linearPairReserve (lowerSourceScale M) ∧
      HasInteriorPairReserve (lowerSourceScale M) N
        (linearPairReserve (lowerSourceScale M))) ∨
    (1 ≤ linearPairReserve (upperSourceScale M) ∧
      HasInteriorPairReserve (upperSourceScale M) N
        (linearPairReserve (upperSourceScale M))) := by
  rcases (mem_evenTargetBlock_iff M N).mp hN with
    ⟨_h4, hNM, hEven, hLower⟩
  rcases hEven with ⟨k, hk⟩
  by_cases hSplit : 4 * N ≤ 3 * M
  · left
    simp only [lowerSourceScale, linearPairReserve, HasInteriorPairReserve]
    omega
  · right
    simp only [upperSourceScale, linearPairReserve, HasInteriorPairReserve]
    omega

/-- Whichever source scale covers the target carries at least its declared
one-eighth reserve in the exact pair-count expression. -/
theorem evenTargetBlock_two_source_scale_pair_count
    (M N : ℕ) (hM : 19 ≤ M) (hN : N ∈ evenTargetBlock M) :
    (linearPairReserve (lowerSourceScale M) ≤
      blockPairUpper (lowerSourceScale M) N -
        blockPairLower (lowerSourceScale M) N + 1) ∨
    (linearPairReserve (upperSourceScale M) ≤
      blockPairUpper (upperSourceScale M) N -
        blockPairLower (upperSourceScale M) N + 1) := by
  rcases evenTargetBlock_two_source_scale_cover M N hM hN with hLow | hHigh
  · left
    exact blockPair_count_ge_interior_reserve
      (lowerSourceScale M) N (linearPairReserve (lowerSourceScale M))
      (by simp only [lowerSourceScale]; omega) hLow.1 hLow.2
  · right
    exact blockPair_count_ge_interior_reserve
      (upperSourceScale M) N (linearPairReserve (upperSourceScale M))
      (by simp only [upperSourceScale]; omega) hHigh.1 hHigh.2

end GoldbachCircleMethodTwoSourceScaleCoverV18232
