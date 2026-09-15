import GoldbachCircleMethodActualResidualExactDecompositionV18225

/-!
# Goldbach V1.8.226: signed two-error split

An exact source/model/residual/correction identity yields a fail-closed
alternative: if the real model reserve exceeds the real source budget by at
least twice a positive threshold, either the residual or the retained
centered-error correction is large in norm.  No moment or arithmetic premise
is supplied here.
-/

set_option autoImplicit false

namespace GoldbachCircleMethodSignedTwoErrorSplitV18226

open GoldbachCircleMethodActualResidualLargeValueTransferV18224
open GoldbachCircleMethodActualResidualExactDecompositionV18225

/-- Pure ordered complex algebra behind the two-error split. -/
theorem one_of_two_errors_large_of_real_gap
    (source model residual correction : ℂ) (D reserve T : ℝ)
    (hIdentity : source = model + residual + correction)
    (hSource : source.re ≤ D) (hModel : reserve ≤ model.re)
    (hGap : 2 * T ≤ reserve - D) :
    T ≤ ‖residual‖ ∨ T ≤ ‖correction‖ := by
  by_contra hBoth
  have h : ¬ T ≤ ‖residual‖ ∧ ¬ T ≤ ‖correction‖ := not_or.mp hBoth
  have hrLt : ‖residual‖ < T := lt_of_not_ge h.1
  have hcLt : ‖correction‖ < T := lt_of_not_ge h.2
  have hrAbs : |residual.re| ≤ ‖residual‖ := Complex.abs_re_le_norm residual
  have hcAbs : |correction.re| ≤ ‖correction‖ := Complex.abs_re_le_norm correction
  have hrLower : -T < residual.re := by
    have hrNeg : -‖residual‖ ≤ residual.re := neg_le_of_abs_le hrAbs
    linarith [hrLt]
  have hcLower : -T < correction.re := by
    have hcNeg : -‖correction‖ ≤ correction.re := neg_le_of_abs_le hcAbs
    linarith [hcLt]
  have hReal : source.re = model.re + residual.re + correction.re := by
    simpa only [Complex.add_re] using congrArg Complex.re hIdentity
  linarith

/-- Actual specialization to the exact V1.8.225 decomposition.  Every
quantity is the literal finite coefficient from the predecessor modules. -/
theorem canonical_one_of_two_errors_large_of_real_gap
    (B : ℕ) (rho : ℝ) (hR2 : 2 ≤ (B : ℝ)^rho) (k : ℤ)
    (D reserve T : ℝ)
    (hSource : (canonicalBlockSourceAt B k).re ≤ D)
    (hModel : reserve ≤ (canonicalPrincipalModelAt B rho k).re)
    (hGap : 2 * T ≤ reserve - D) :
    T ≤ ‖canonicalPrincipalResidualAt B rho hR2 k‖ ∨
      T ≤ ‖canonicalCenteredErrorCorrectionAt B rho k‖ := by
  exact one_of_two_errors_large_of_real_gap
    (canonicalBlockSourceAt B k) (canonicalPrincipalModelAt B rho k)
    (canonicalPrincipalResidualAt B rho hR2 k)
    (canonicalCenteredErrorCorrectionAt B rho k) D reserve T
    (canonicalBlockSourceAt_eq_model_add_residual_add_centeredError
      B rho hR2 k)
    hSource hModel hGap

end GoldbachCircleMethodSignedTwoErrorSplitV18226
