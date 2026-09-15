import GoldbachCircleMethodCollisionPolylogSourceBoundV18573

/-!
# Goldbach V1.8.574: explicit polynomial collision bound

This module composes the closed arithmetic fourth-moment bound with the
polylogarithmic source cap and the actual target-block cardinality.  The result
is unconditional under the displayed finite-window admissions, but it is only
an absolute polynomial majorant.  It does not provide the cancellation needed
for minor-arc absorption.
-/

set_option autoImplicit false

open scoped BigOperators Classical ComplexConjugate

namespace GoldbachCircleMethodCollisionExplicitPolynomialBoundV18574

open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodCollisionLinearMomentTransferV18572
open GoldbachCircleMethodCollisionPolylogSourceBoundV18573
open GoldbachCircleMethodCrossDenominatorCollisionPartitionV18547
open GoldbachCircleMethodLogCutoffPresieveBindingV18120

theorem blockCarrier_card_cast_le (B : ℕ) :
    ((blockCarrier B).card : ℝ) ≤ (B : ℝ) := by
  exact_mod_cast (show (blockCarrier B).card ≤ B by
    simp only [blockCarrier, Nat.card_Ioc]
    omega)

/-- Fully explicit absolute collision bound.  Its `Q^4` cost is retained
literally; no decay claim is hidden in asymptotic notation. -/
theorem collisionLiteralCrossBlockCorrelation_sq_le_explicit_polynomial
    (Q B : ℕ) (H V : ℝ) (w : ℕ → ℂ)
    (r s : PositiveLevel Q)
    (hB : 2 ≤ B) (hH : 1 ≤ H) (hQH : (Q : ℝ) ≤ H)
    (hw : ∀ n, ‖w n‖ ≤ V) :
    (collisionLiteralCrossBlockCorrelation Q B H w r s) ^ 2 ≤
      Real.exp 30 * (B : ℝ) ^ 2 * (Q : ℝ) ^ 4 * V ^ 4 *
        (collisionSourcePolylogCap B) ^ 2 := by
  have hfront : 0 ≤ Real.exp 30 * (B : ℝ) * (Q : ℝ) ^ 4 := by
    positivity
  have htail : 0 ≤ V ^ 4 * (collisionSourcePolylogCap B) ^ 2 := by
    positivity
  calc
    (collisionLiteralCrossBlockCorrelation Q B H w r s) ^ 2 ≤
        Real.exp 30 * (B : ℝ) * (Q : ℝ) ^ 4 *
          collisionPrimitiveSourceProductEnergy Q B H V r s :=
      collisionLiteralCrossBlockCorrelation_sq_le_exp_thirty_Q_four_source
        Q B H V w r s hw
    _ ≤ Real.exp 30 * (B : ℝ) * (Q : ℝ) ^ 4 *
          (((blockCarrier B).card : ℝ) *
            (V ^ 4 * (collisionSourcePolylogCap B) ^ 2)) :=
      mul_le_mul_of_nonneg_left
        (collisionPrimitiveSourceProductEnergy_le_block_polylog
          Q B H V r s hB hH hQH) hfront
    _ ≤ Real.exp 30 * (B : ℝ) * (Q : ℝ) ^ 4 *
          ((B : ℝ) *
            (V ^ 4 * (collisionSourcePolylogCap B) ^ 2)) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (blockCarrier_card_cast_le B) htail)
        hfront
    _ = Real.exp 30 * (B : ℝ) ^ 2 * (Q : ℝ) ^ 4 * V ^ 4 *
          (collisionSourcePolylogCap B) ^ 2 := by ring

end GoldbachCircleMethodCollisionExplicitPolynomialBoundV18574
