import GoldbachCircleMethodExceptionalZeroAttestationContractV18260

/-!
# Goldbach V1.8.261: case-selected exact source decomposition

The proof-carrying absent/active exceptional-zero case selects the exact
model, residual, and centered-correction accounting branch.  Both branches
reduce to already kernel-verified finite convolution identities.
-/

open scoped Classical BigOperators

set_option autoImplicit false

namespace GoldbachCircleMethodCaseSelectedExactSourceDecompositionV18261

open GoldbachCircleMethodActiveExceptionalCenteringV18129
open GoldbachCircleMethodActualResidualLargeValueTransferV18224
open GoldbachCircleMethodActualResidualExactDecompositionV18225
open GoldbachCircleMethodActiveResidualExactDecompositionV18251
open GoldbachCircleMethodStructurallyAdmissibleActiveSlotV18258
open GoldbachCircleMethodExceptionalZeroAttestationContractV18260

noncomputable def caseSelectedModelAt
    (B : ℕ) (rho : ℝ)
    (ExceptionalZeroAt :
      StructurallyAdmissibleActiveSlot ⌊((B : ℝ)^rho)^2⌋₊ → ℝ → Prop)
    (c : ExceptionalZeroCase ⌊((B : ℝ)^rho)^2⌋₊ ExceptionalZeroAt)
    (k : ℤ) : ℂ :=
  match c with
  | .absent _ => canonicalPrincipalModelAt B rho k
  | .active d => canonicalAdjustedModelAt B rho d.beta d.slot.val k

noncomputable def caseSelectedResidualAt
    (B : ℕ) (rho : ℝ) (hR2 : 2 ≤ (B : ℝ)^rho)
    (ExceptionalZeroAt :
      StructurallyAdmissibleActiveSlot ⌊((B : ℝ)^rho)^2⌋₊ → ℝ → Prop)
    (c : ExceptionalZeroCase ⌊((B : ℝ)^rho)^2⌋₊ ExceptionalZeroAt)
    (k : ℤ) : ℂ :=
  match c with
  | .absent _ => canonicalPrincipalResidualAt B rho hR2 k
  | .active d => canonicalActiveResidualAt B rho hR2 d.beta d.slot.val k

noncomputable def caseSelectedCenteredCorrectionAt
    (B : ℕ) (rho : ℝ)
    (ExceptionalZeroAt :
      StructurallyAdmissibleActiveSlot ⌊((B : ℝ)^rho)^2⌋₊ → ℝ → Prop)
    (c : ExceptionalZeroCase ⌊((B : ℝ)^rho)^2⌋₊ ExceptionalZeroAt)
    (k : ℤ) : ℂ :=
  match c with
  | .absent _ => canonicalCenteredErrorCorrectionAt B rho k
  | .active d =>
      canonicalAdjustedCenteredErrorCorrectionAt B rho d.beta d.slot.val k

/-- Exact source accounting in either proof-carrying exceptional-zero branch.
This theorem is branch algebra only; it neither constructs a case nor bounds
any selected error term. -/
theorem canonicalBlockSourceAt_eq_caseSelected_decomposition
    (B : ℕ) (rho : ℝ) (hR2 : 2 ≤ (B : ℝ)^rho)
    (ExceptionalZeroAt :
      StructurallyAdmissibleActiveSlot ⌊((B : ℝ)^rho)^2⌋₊ → ℝ → Prop)
    (c : ExceptionalZeroCase ⌊((B : ℝ)^rho)^2⌋₊ ExceptionalZeroAt)
    (k : ℤ) :
    canonicalBlockSourceAt B k =
      caseSelectedModelAt B rho ExceptionalZeroAt c k +
        caseSelectedResidualAt B rho hR2 ExceptionalZeroAt c k +
        caseSelectedCenteredCorrectionAt B rho ExceptionalZeroAt c k := by
  cases c with
  | absent hAbsent =>
      simpa [caseSelectedModelAt, caseSelectedResidualAt,
        caseSelectedCenteredCorrectionAt] using
        canonicalBlockSourceAt_eq_model_add_residual_add_centeredError
          B rho hR2 k
  | active d =>
      simpa [caseSelectedModelAt, caseSelectedResidualAt,
        caseSelectedCenteredCorrectionAt] using
        canonicalBlockSourceAt_eq_adjustedModel_add_activeResidual_add_adjustedError
          B rho hR2 d.beta d.slot.val k

end GoldbachCircleMethodCaseSelectedExactSourceDecompositionV18261
