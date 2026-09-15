import GoldbachCircleMethodQuantitativeAdmittedPrincipalReserveV18236
import GoldbachPrimePowerDefectBoundV161

/-!
# Goldbach V1.8.237: non-Goldbach block-source defect bridge

This module binds the literal source coefficient from the recent actual-block
chain to the original finite von-Mangoldt convolution.  At a target without a
pure prime representation, the restricted block source is bounded above by
the explicit prime-power defect.  No model or residual estimate is used.
-/

open scoped BigOperators Classical ArithmeticFunction.vonMangoldt

set_option autoImplicit false

namespace GoldbachCircleMethodNonGoldbachBlockSourceDefectBridgeV18237

open GoldbachPurePrimeAdequacyV15
open GoldbachVonMangoldtDecompositionV16
open GoldbachPrimePowerDefectBoundV161
open GoldbachCircleMethodLogCutoffPresieveBindingV18120
open GoldbachCircleMethodActualResidualExactDecompositionV18225
open GoldbachCircleMethodBlockPairCarrierV18227

/-- At a natural target above the source scale, the literal complex block
coefficient is exactly the real von-Mangoldt sum on its complement-closed
pair carrier. -/
theorem canonicalBlockSourceAt_nat_eq_restricted_vonMangoldt_sum
    (B N : ℕ) (hBN : B ≤ N) :
    canonicalBlockSourceAt B (N : ℤ) =
      ((∑ n ∈ pairFirstCarrier (blockCarrier B) N,
        ArithmeticFunction.vonMangoldt n *
          ArithmeticFunction.vonMangoldt (N - n) : ℝ) : ℂ) := by
  rw [canonicalBlockSourceAt,
    integerPairConvolution_nat_eq_pairFirstCarrier]
  · push_cast
    apply Finset.sum_congr rfl
    intro n hn
    have hnData := Finset.mem_filter.mp hn
    have hnBlock : n ∈ blockCarrier B := hnData.1
    have hcompBlock : N - n ∈ blockCarrier B := hnData.2
    rw [blockInput, if_pos hnBlock, blockInput, if_pos hcompBlock]
  · intro n hn
    exact (Finset.mem_Ioc.mp hn).2.trans hBN

/-- The complement-closed block pair carrier is a subset of the full
von-Mangoldt convolution carrier. -/
theorem pairFirstCarrier_block_subset_range
    (B N : ℕ) :
    pairFirstCarrier (blockCarrier B) N ⊆ Finset.range N := by
  intro n hn
  have hnData := Finset.mem_filter.mp hn
  have hcomp := Finset.mem_Ioc.mp hnData.2
  exact Finset.mem_range.mpr (by omega)

/-- Restricting to one source block cannot increase the nonnegative full
von-Mangoldt convolution. -/
theorem canonicalBlockSourceAt_re_le_vonMangoldtPairSum
    (B N : ℕ) (hBN : B ≤ N) :
    (canonicalBlockSourceAt B (N : ℤ)).re ≤ vonMangoldtPairSum N := by
  rw [canonicalBlockSourceAt_nat_eq_restricted_vonMangoldt_sum B N hBN]
  simp only [Complex.ofReal_re, vonMangoldtPairSum]
  apply Finset.sum_le_sum_of_subset_of_nonneg
    (pairFirstCarrier_block_subset_range B N)
  intro n _hn _hnot
  exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
    ArithmeticFunction.vonMangoldt_nonneg

/-- The pure-prime logarithmic fibre is nonnegative independently of whether
it has a witness. -/
theorem purePrimeSum_nonneg (N : ℕ) : 0 ≤ purePrimeSum N := by
  unfold purePrimeSum
  exact Finset.sum_nonneg fun n hn => (purePrimeWeight_pos hn).le

/-- A failed pointwise Goldbach predicate forces the pure-prime fibre to be
exactly zero, by the previously kernel-checked semantic adequacy theorem. -/
theorem purePrimeSum_eq_zero_of_not_goldbachAt
    (N : ℕ) (hNot : ¬ GoldbachAt N) :
    purePrimeSum N = 0 := by
  have hNotPos : ¬ 0 < purePrimeSum N := by
    intro hPos
    exact hNot ((purePrimeSum_pos_iff_strictGoldbach N).mp hPos)
  exact le_antisymm (le_of_not_gt hNotPos) (purePrimeSum_nonneg N)

/-- Exact semantic bridge required by the signed two-error split: if `N` is
not Goldbach, the literal source coefficient on any lower block is at most
the global explicit prime-power defect. -/
theorem canonicalBlockSourceAt_re_le_primePowerDefect_of_not_goldbachAt
    (B N : ℕ) (hBN : B ≤ N) (hNot : ¬ GoldbachAt N) :
    (canonicalBlockSourceAt B (N : ℤ)).re ≤ primePowerDefect N := by
  have hSource := canonicalBlockSourceAt_re_le_vonMangoldtPairSum B N hBN
  have hPure := purePrimeSum_eq_zero_of_not_goldbachAt N hNot
  rw [vonMangoldtPairSum_eq_purePrimeSum_add_primePowerDefect, hPure,
    zero_add] at hSource
  exact hSource

end GoldbachCircleMethodNonGoldbachBlockSourceDefectBridgeV18237
