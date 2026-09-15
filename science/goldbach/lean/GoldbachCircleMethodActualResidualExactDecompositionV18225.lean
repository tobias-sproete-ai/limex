import GoldbachCircleMethodActualResidualLargeValueTransferV18224

/-!
# Goldbach V1.8.225: exact actual-residual decomposition

This module identifies exactly what the V1.8.224 residual controls.  The
centered-window error is retained as a separate convolution correction.  No
principal floor, error estimate, exception inclusion, or Goldbach result is
inferred here.
-/

open scoped BigOperators Classical

set_option autoImplicit false

namespace GoldbachCircleMethodActualResidualExactDecompositionV18225

open GoldbachCircleMethodLogCutoffPresieveBindingV18120
open GoldbachCircleMethodActualInputModelResidualV18138
open GoldbachCircleMethodSupportedResidualParsevalV18190
open GoldbachCircleMethodUncorrectedSupportedErrorConvolutionV18184
open GoldbachCircleMethodCanonicalBumpPrincipalFloorV18220
open GoldbachCircleMethodActualResidualLargeValueTransferV18224

/-- Integer-pair convolution is commutative when both inputs use the same
finite carrier. -/
theorem integerPairConvolution_comm
    (J : Finset ℕ) (v w : ℕ → ℂ) (k : ℤ) :
    integerPairConvolution J v w k = integerPairConvolution J w v k := by
  unfold integerPairConvolution
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n _hn
  apply Finset.sum_congr rfl
  intro u _hu
  simp only [add_comm, mul_comm]

/-- Exact additivity in the first input. -/
theorem integerPairConvolution_add_left
    (J : Finset ℕ) (v w z : ℕ → ℂ) (k : ℤ) :
    integerPairConvolution J (fun n => v n + w n) z k =
      integerPairConvolution J v z k + integerPairConvolution J w z k := by
  unfold integerPairConvolution
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n _hn
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro u _hu
  split_ifs <;> ring

/-- Exact additivity in the second input. -/
theorem integerPairConvolution_add_right
    (J : Finset ℕ) (v w z : ℕ → ℂ) (k : ℤ) :
    integerPairConvolution J v (fun n => w n + z n) k =
      integerPairConvolution J v w k + integerPairConvolution J v z k := by
  rw [integerPairConvolution_comm J v (fun n => w n + z n) k,
    integerPairConvolution_add_left J w z v k,
    integerPairConvolution_comm J w v k,
    integerPairConvolution_comm J z v k]

/-- Exact subtraction in the first input. -/
theorem integerPairConvolution_sub_left
    (J : Finset ℕ) (v w z : ℕ → ℂ) (k : ℤ) :
    integerPairConvolution J (fun n => v n - w n) z k =
      integerPairConvolution J v z k - integerPairConvolution J w z k := by
  unfold integerPairConvolution
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n _hn
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro u _hu
  split_ifs <;> ring

/-- Exact difference-of-squares identity at the finite-convolution level. -/
theorem integerPairConvolution_difference_of_squares
    (J : Finset ℕ) (a m : ℕ → ℂ) (k : ℤ) :
    integerPairConvolution J (fun n => a n - m n)
        (fun n => a n + m n) k +
      integerPairConvolution J m m k =
      integerPairConvolution J a a k := by
  rw [integerPairConvolution_sub_left J a m (fun n => a n + m n) k,
    integerPairConvolution_add_right J a a m k,
    integerPairConvolution_add_right J m a m k,
    integerPairConvolution_comm J m a k]
  ring

/-- On the actual block carrier, the V1.8.138 residual is literally the
source minus the supported principal model minus the supported centered
error. -/
theorem inputPrincipalResidual_eq_supported_difference_on_block
    (B N : ℕ) (R : ℝ) (hR : 1 < R) (G : ℝ → ℝ)
    (hN : N ∈ blockCarrier B) :
    inputPrincipalResidual B N R hR G =
      blockInput B N - supportedPrincipalModel B N R G -
        supportedUncorrectedError B N R G := by
  unfold inputPrincipalResidual supportedPrincipalModel supportedUncorrectedError
  have hNIoc : N ∈ Finset.Ioc (B / 2) B := by simpa only [blockCarrier] using hN
  rw [dif_pos hR, if_pos hNIoc, if_pos hNIoc]

/-- Literal self-convolution of the actual von-Mangoldt block. -/
noncomputable def canonicalBlockSourceAt (B : ℕ) (k : ℤ) : ℂ :=
  integerPairConvolution (blockCarrier B) (blockInput B) (blockInput B) k

/-- Literal self-convolution of the supported conductor-one model. -/
noncomputable def canonicalPrincipalModelAt
    (B : ℕ) (rho : ℝ) (k : ℤ) : ℂ :=
  integerPairConvolution (blockCarrier B)
    (fun N => supportedPrincipalModel B N ((B : ℝ)^rho) canonicalLogBump)
    (fun N => supportedPrincipalModel B N ((B : ℝ)^rho) canonicalLogBump) k

/-- The centered-error correction deliberately omitted from the V1.8.224
large-value set. -/
noncomputable def canonicalCenteredErrorCorrectionAt
    (B : ℕ) (rho : ℝ) (k : ℤ) : ℂ :=
  integerPairConvolution (blockCarrier B)
    (fun N => supportedUncorrectedError B N ((B : ℝ)^rho) canonicalLogBump)
    (fun N => blockInput B N +
      supportedPrincipalModel B N ((B : ℝ)^rho) canonicalLogBump) k

/-- Exact accounting identity for the actual residual.  This theorem exposes
the mandatory centered-error correction instead of silently identifying the
V1.8.224 residual with source-minus-model. -/
theorem canonicalBlockSourceAt_eq_model_add_residual_add_centeredError
    (B : ℕ) (rho : ℝ) (hR2 : 2 ≤ (B : ℝ)^rho) (k : ℤ) :
    canonicalBlockSourceAt B k =
      canonicalPrincipalModelAt B rho k +
        canonicalPrincipalResidualAt B rho hR2 k +
        canonicalCenteredErrorCorrectionAt B rho k := by
  have hR : 1 < (B : ℝ)^rho := by linarith
  let a : ℕ → ℂ := blockInput B
  let m : ℕ → ℂ := fun N =>
    supportedPrincipalModel B N ((B : ℝ)^rho) canonicalLogBump
  let e : ℕ → ℂ := fun N =>
    supportedUncorrectedError B N ((B : ℝ)^rho) canonicalLogBump
  have hpoint (N : ℕ) (hN : N ∈ blockCarrier B) :
      inputPrincipalResidual B N ((B : ℝ)^rho) (by linarith)
          canonicalLogBump = a N - m N - e N := by
    dsimp [a, m, e]
    exact inputPrincipalResidual_eq_supported_difference_on_block
      B N ((B : ℝ)^rho) hR canonicalLogBump hN
  have hres :
      canonicalPrincipalResidualAt B rho hR2 k =
        integerPairConvolution (blockCarrier B)
          (fun N => a N - m N - e N) (fun N => a N + m N) k := by
    unfold canonicalPrincipalResidualAt
    apply Finset.sum_congr rfl
    intro n hn
    apply Finset.sum_congr rfl
    intro u hu
    by_cases hk : k = (n : ℤ) + (u : ℤ)
    · simp only [hk, if_true]
      rw [hpoint n hn]
    · simp only [hk, if_false]
  have hcombine :
      integerPairConvolution (blockCarrier B)
          (fun N => a N - m N - e N) (fun N => a N + m N) k +
        integerPairConvolution (blockCarrier B) e (fun N => a N + m N) k =
      integerPairConvolution (blockCarrier B)
          (fun N => a N - m N) (fun N => a N + m N) k := by
    rw [← integerPairConvolution_add_left]
    congr 1
    funext N
    ring
  rw [hres]
  change integerPairConvolution (blockCarrier B) a a k =
    integerPairConvolution (blockCarrier B) m m k +
      integerPairConvolution (blockCarrier B) (fun N => a N - m N - e N)
        (fun N => a N + m N) k +
      integerPairConvolution (blockCarrier B) e (fun N => a N + m N) k
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

end GoldbachCircleMethodActualResidualExactDecompositionV18225
