import GoldbachCircleMethodCenteredCorrectionNumericAbsorptionV18250

/-!
# Goldbach V1.8.251: active-character exact residual decomposition

This module mirrors the exact V1.8.225 accounting identity on the already
defined active-character branch.  It changes no analytic estimate and makes
no exceptional-zero existence claim.  The character slot and its coefficient
remain explicit parameters throughout.
-/

open scoped BigOperators Classical

set_option autoImplicit false

namespace GoldbachCircleMethodActiveResidualExactDecompositionV18251

open GoldbachCircleMethodLogCutoffPresieveBindingV18120
open GoldbachCircleMethodActiveExceptionalCenteringV18129
open GoldbachCircleMethodActualInputModelResidualV18138
open GoldbachCircleMethodSupportedModelErrorConvolutionV18182
open GoldbachCircleMethodSupportedResidualParsevalV18190
open GoldbachCircleMethodActualResidualExactDecompositionV18225
open GoldbachCircleMethodCanonicalBumpPrincipalFloorV18220

/-- On the actual block carrier, the active residual is literally the source
minus the supported adjusted model minus the supported adjusted centered
error.  The active character is an admitted slot, not an asserted exceptional
character. -/
theorem inputActiveResidual_eq_supported_difference_on_block
    (B N : ℕ) (R : ℝ) (hR : 1 < R) (b : ℝ) (G : ℝ → ℝ)
    (e : CharacterSlot ⌊R^2⌋₊) (hN : N ∈ blockCarrier B) :
    inputActiveResidual B N R hR b G e =
      blockInput B N - supportedAdjustedModel B N R b G e -
        supportedAdjustedError B N R b G e := by
  unfold inputActiveResidual supportedAdjustedModel supportedAdjustedError
  have hNIoc : N ∈ Finset.Ioc (B / 2) B := by
    simpa only [blockCarrier] using hN
  rw [dif_pos hR, if_pos hNIoc, if_pos hNIoc]

/-- Literal self-convolution of the active adjusted model. -/
noncomputable def canonicalAdjustedModelAt
    (B : ℕ) (rho b : ℝ)
    (e : CharacterSlot ⌊((B : ℝ)^rho)^2⌋₊) (k : ℤ) : ℂ :=
  integerPairConvolution (blockCarrier B)
    (fun N => supportedAdjustedModel B N ((B : ℝ)^rho) b canonicalLogBump e)
    (fun N => supportedAdjustedModel B N ((B : ℝ)^rho) b canonicalLogBump e) k

/-- Literal active residual term already controlled in averaged square by
the active V1.8.222 theorem. -/
noncomputable def canonicalActiveResidualAt
    (B : ℕ) (rho : ℝ) (hR2 : 2 ≤ (B : ℝ)^rho) (b : ℝ)
    (e : CharacterSlot ⌊((B : ℝ)^rho)^2⌋₊) (k : ℤ) : ℂ :=
  integerPairConvolution (blockCarrier B)
    (fun N => inputActiveResidual B N ((B : ℝ)^rho) (by linarith)
      b canonicalLogBump e)
    (fun N => blockInput B N +
      supportedAdjustedModel B N ((B : ℝ)^rho) b canonicalLogBump e) k

/-- Centered-error correction on the active adjusted branch. -/
noncomputable def canonicalAdjustedCenteredErrorCorrectionAt
    (B : ℕ) (rho b : ℝ)
    (e : CharacterSlot ⌊((B : ℝ)^rho)^2⌋₊) (k : ℤ) : ℂ :=
  integerPairConvolution (blockCarrier B)
    (fun N => supportedAdjustedError B N ((B : ℝ)^rho) b canonicalLogBump e)
    (fun N => blockInput B N +
      supportedAdjustedModel B N ((B : ℝ)^rho) b canonicalLogBump e) k

/-- Exact active-branch source accounting.  This is an identity only: no
positivity of the adjusted model and no bound for its centered correction is
inferred. -/
theorem canonicalBlockSourceAt_eq_adjustedModel_add_activeResidual_add_adjustedError
    (B : ℕ) (rho : ℝ) (hR2 : 2 ≤ (B : ℝ)^rho) (b : ℝ)
    (e : CharacterSlot ⌊((B : ℝ)^rho)^2⌋₊) (k : ℤ) :
    canonicalBlockSourceAt B k =
      canonicalAdjustedModelAt B rho b e k +
        canonicalActiveResidualAt B rho hR2 b e k +
        canonicalAdjustedCenteredErrorCorrectionAt B rho b e k := by
  have hR : 1 < (B : ℝ)^rho := by linarith
  let a : ℕ → ℂ := blockInput B
  let m : ℕ → ℂ := fun N =>
    supportedAdjustedModel B N ((B : ℝ)^rho) b canonicalLogBump e
  let err : ℕ → ℂ := fun N =>
    supportedAdjustedError B N ((B : ℝ)^rho) b canonicalLogBump e
  have hpoint (N : ℕ) (hN : N ∈ blockCarrier B) :
      inputActiveResidual B N ((B : ℝ)^rho) (by linarith)
          b canonicalLogBump e = a N - m N - err N := by
    dsimp [a, m, err]
    exact inputActiveResidual_eq_supported_difference_on_block
      B N ((B : ℝ)^rho) hR b canonicalLogBump e hN
  have hres :
      canonicalActiveResidualAt B rho hR2 b e k =
        integerPairConvolution (blockCarrier B)
          (fun N => a N - m N - err N) (fun N => a N + m N) k := by
    unfold canonicalActiveResidualAt
    apply Finset.sum_congr rfl
    intro n hn
    apply Finset.sum_congr rfl
    intro u _hu
    by_cases hk : k = (n : ℤ) + (u : ℤ)
    · simp only [hk, if_true]
      rw [hpoint n hn]
    · simp only [hk, if_false]
  have hcombine :
      integerPairConvolution (blockCarrier B)
          (fun N => a N - m N - err N) (fun N => a N + m N) k +
        integerPairConvolution (blockCarrier B) err (fun N => a N + m N) k =
      integerPairConvolution (blockCarrier B)
          (fun N => a N - m N) (fun N => a N + m N) k := by
    rw [← integerPairConvolution_add_left]
    congr 1
    funext N
    ring
  rw [hres]
  change integerPairConvolution (blockCarrier B) a a k =
    integerPairConvolution (blockCarrier B) m m k +
      integerPairConvolution (blockCarrier B) (fun N => a N - m N - err N)
        (fun N => a N + m N) k +
      integerPairConvolution (blockCarrier B) err (fun N => a N + m N) k
  have hsquare := integerPairConvolution_difference_of_squares
    (blockCarrier B) a m k
  calc
    _ = integerPairConvolution (blockCarrier B) (fun N => a N - m N)
          (fun N => a N + m N) k +
        integerPairConvolution (blockCarrier B) m m k := hsquare.symm
    _ = integerPairConvolution (blockCarrier B) m m k +
        integerPairConvolution (blockCarrier B) (fun N => a N - m N)
          (fun N => a N + m N) k := add_comm _ _
    _ = _ := by rw [← hcombine]; ring

end GoldbachCircleMethodActiveResidualExactDecompositionV18251
