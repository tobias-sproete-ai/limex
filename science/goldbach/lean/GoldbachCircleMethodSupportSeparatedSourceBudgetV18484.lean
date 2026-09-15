import GoldbachCircleMethodPrincipalSupportEnergySplitV18483

/-!
# Goldbach V1.8.484: support-separated source budget

The pointwise support-separated correlation bound is summed over the literal
source block. This replaces the old product of full coefficient and adjusted
source energies by three explicit channels.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodSupportSeparatedSourceBudgetV18484

open GoldbachCircleMethodActiveExceptionalCenteringV18129
open GoldbachCircleMethodAdjustedCharacterSlotL2AdapterV18449
open GoldbachCircleMethodAdjustedCorrectionL2CompositionV18451
open GoldbachCircleMethodCanonicalBumpPrincipalFloorV18220
open GoldbachCircleMethodFiniteCompanionBindingV18118
open GoldbachCircleMethodLogCutoffPresieveBindingV18120
open GoldbachCircleMethodPrincipalWindowBoundaryV18121
open GoldbachCircleMethodPrimitiveBaseSlotEnergyV18474
open GoldbachCircleMethodPrincipalSupportEnergySplitV18483
open GoldbachCircleMethodSupportedModelErrorConvolutionV18182

/-- The three exact source-side channels after preserving the sparse supports
of the principal and exceptional corrections. -/
noncomputable def supportSeparatedSourceBudget
    (B : ℕ) (rho _b : ℝ)
    (e : CharacterSlot ⌊((B : ℝ) ^ rho) ^ 2⌋₊) : ℝ :=
  let Q := ⌊((B : ℝ) ^ rho) ^ 2⌋₊
  let H := (B : ℝ) / ((B : ℝ) ^ rho) ^ 4
  let w := logWeight ((B : ℝ) ^ rho) canonicalLogBump
  ∑ n ∈ blockCarrier B,
    (adjustedCoefficientEnergy Q n w * primitiveBaseSourceEnergy Q B n H +
      (9 / 4 : ℝ) * principalCoefficientEnergy Q n w +
      (9 / 4 : ℝ) * ‖windowCoefficient e.1 n w e.2‖ ^ 2)

theorem supportSeparatedSourceBudget_nonneg
    (B : ℕ) (rho b : ℝ)
    (e : CharacterSlot ⌊((B : ℝ) ^ rho) ^ 2⌋₊) :
    0 ≤ supportSeparatedSourceBudget B rho b e := by
  unfold supportSeparatedSourceBudget
  apply Finset.sum_nonneg
  intro n _hn
  have hcoefficient : 0 ≤ adjustedCoefficientEnergy
      ⌊((B : ℝ) ^ rho) ^ 2⌋₊ n
      (logWeight ((B : ℝ) ^ rho) canonicalLogBump) := by
    unfold adjustedCoefficientEnergy
    positivity
  have hbase : 0 ≤ primitiveBaseSourceEnergy
      ⌊((B : ℝ) ^ rho) ^ 2⌋₊ B n
      ((B : ℝ) / ((B : ℝ) ^ rho) ^ 4) := by
    unfold primitiveBaseSourceEnergy
    positivity
  have hprincipal : 0 ≤ principalCoefficientEnergy
      ⌊((B : ℝ) ^ rho) ^ 2⌋₊ n
      (logWeight ((B : ℝ) ^ rho) canonicalLogBump) := by
    unfold principalCoefficientEnergy
    exact Finset.sum_nonneg fun t _ht => by split_ifs <;> positivity
  positivity

/-- Literal supported adjusted-error energy with all sparse supports retained.
This is a strict improvement of the earlier full-family product interface. -/
theorem supportedAdjustedErrorEnergy_le_three_supportSeparatedSourceBudget
    (B : ℕ) (rho b : ℝ)
    (e : CharacterSlot ⌊((B : ℝ) ^ rho) ^ 2⌋₊)
    (hH : 1 ≤ (B : ℝ) / ((B : ℝ) ^ rho) ^ 4)
    (hb : 0 ≤ b) :
    supportedAdjustedErrorEnergy B rho b e ≤
      3 * supportSeparatedSourceBudget B rho b e := by
  unfold supportedAdjustedErrorEnergy supportSeparatedSourceBudget
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n hn
  have hnIoc : n ∈ Finset.Ioc (B / 2) B := by
    simpa only [blockCarrier] using hn
  rw [supportedAdjustedError, if_pos hnIoc]
  exact adjustedCenteredError_sq_le_support_separated
    ⌊((B : ℝ) ^ rho) ^ 2⌋₊ B n
    ((B : ℝ) / ((B : ℝ) ^ rho) ^ 4) b
    (logWeight ((B : ℝ) ^ rho) canonicalLogBump) hH hb e

end GoldbachCircleMethodSupportSeparatedSourceBudgetV18484
