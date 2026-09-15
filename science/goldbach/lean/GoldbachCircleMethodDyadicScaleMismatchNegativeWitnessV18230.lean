import GoldbachCircleMethodFiniteIntervalRemainderReserveV18229
import GoldbachCircleMethodTwoScaleEvenBlockDefectReserveV1833

/-!
# Goldbach V1.8.230: dyadic same-scale mismatch negative witness

The canonical source block is `(B/2, B]`, while the historical dyadic target
block `evenTargetBlock B` is contained in `[4, B]`.  This module proves in the
kernel that both the literal source self-convolution and the supported
principal-model self-convolution vanish throughout that historical target
block when the same parameter `B` is used on both sides.

This is a negative witness against one scale adapter.  It is not a statement
about Goldbach and does not exclude a corrected multi-scale cover.
-/

open scoped BigOperators Classical

set_option autoImplicit false

namespace GoldbachCircleMethodDyadicScaleMismatchNegativeWitnessV18230

open GoldbachCircleMethodLogCutoffPresieveBindingV18120
open GoldbachCircleMethodSupportedResidualParsevalV18190
open GoldbachCircleMethodUncorrectedSupportedErrorConvolutionV18184
open GoldbachCircleMethodCanonicalBumpPrincipalFloorV18220
open GoldbachCircleMethodActualResidualExactDecompositionV18225
open GoldbachCircleMethodBlockPairCarrierV18227
open GoldbachCircleMethodTwoScaleEvenBlockDefectReserveV1833

/-- No natural first coordinate can belong to the complement carrier of the
upper-half source block at a target at or below the same scale. -/
theorem not_mem_pairFirstCarrier_block_of_target_le_scale
    (B N n : ℕ) (hNB : N ≤ B) :
    n ∉ pairFirstCarrier (blockCarrier B) N := by
  intro hn
  simp only [pairFirstCarrier, blockCarrier, Finset.mem_filter,
    Finset.mem_Ioc] at hn
  omega

/-- Direct integer-frequency version of the same support obstruction.  The
proof does not use natural subtraction and therefore also closes the possible
truncation loophole. -/
theorem integerPairConvolution_block_zero_of_target_le_scale
    (B N : ℕ) (v w : ℕ → ℂ) (hNB : N ≤ B) :
    integerPairConvolution (blockCarrier B) v w (N : ℤ) = 0 := by
  unfold integerPairConvolution
  apply Finset.sum_eq_zero
  intro n hn
  apply Finset.sum_eq_zero
  intro u hu
  rw [if_neg]
  intro heq
  have hn' : B / 2 < n := (Finset.mem_Ioc.mp hn).1
  have hu' : B / 2 < u := (Finset.mem_Ioc.mp hu).1
  have hNat : N = n + u := by exact_mod_cast heq
  omega

/-- The actual von-Mangoldt source block has zero coefficient throughout the
same-scale historical target range. -/
theorem canonicalBlockSourceAt_zero_of_target_le_scale
    (B N : ℕ) (hNB : N ≤ B) :
    canonicalBlockSourceAt B (N : ℤ) = 0 := by
  exact integerPairConvolution_block_zero_of_target_le_scale
    B N (blockInput B) (blockInput B) hNB

/-- The supported principal model has the identical support obstruction. -/
theorem canonicalPrincipalModelAt_zero_of_target_le_scale
    (B N : ℕ) (rho : ℝ) (hNB : N ≤ B) :
    canonicalPrincipalModelAt B rho (N : ℤ) = 0 := by
  exact integerPairConvolution_block_zero_of_target_le_scale B N
    (fun n => supportedPrincipalModel B n ((B : ℝ) ^ rho) canonicalLogBump)
    (fun n => supportedPrincipalModel B n ((B : ℝ) ^ rho) canonicalLogBump)
    hNB

/-- Kernel-level rejection of the naive adapter that identifies the old
dyadic target ceiling and the new source-block ceiling. -/
theorem same_scale_source_and_model_zero_on_evenTargetBlock
    (B N : ℕ) (rho : ℝ) (hN : N ∈ evenTargetBlock B) :
    canonicalBlockSourceAt B (N : ℤ) = 0 ∧
      canonicalPrincipalModelAt B rho (N : ℤ) = 0 := by
  have hNB : N ≤ B := ((mem_evenTargetBlock_iff B N).mp hN).2.1
  exact ⟨canonicalBlockSourceAt_zero_of_target_le_scale B N hNB,
    canonicalPrincipalModelAt_zero_of_target_le_scale B N rho hNB⟩

end GoldbachCircleMethodDyadicScaleMismatchNegativeWitnessV18230
