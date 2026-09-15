import GoldbachCircleMethodLocalizedPrincipalRealNonnegativeReserveV18296

/-!
# Goldbach V1.8.297: localized adjusted explicit-correction reserve

The V1.8.296 principal floor is combined with the V1.8.294 exact active
scalar.  The resulting theorem exposes the precise norm budget that must be
beaten before the localized adjusted channel can be declared positive.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodLocalizedAdjustedExplicitCorrectionReserveV18297

open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodPrincipalWindowBoundaryV18121
open GoldbachCircleMethodLogCutoffPresieveBindingV18120
open GoldbachCircleMethodCanonicalBumpPrincipalFloorV18220
open GoldbachCircleMethodExceptionalWeightBoundaryV18128
open GoldbachCircleMethodActiveConductorDivisorLocalizationV18290
open GoldbachCircleMethodLocalizedActiveCompanionCollapseV18294
open GoldbachCircleMethodLocalizedPrincipalRealNonnegativeReserveV18296

/-- The literal active-character correction after the localized active
companion collapse. -/
noncomputable def localizedActiveCorrection {Q : ℕ}
    (active : PositiveLevel Q)
    (chi : {χ : DirichletCharacter ℂ active.val // χ.IsPrimitive})
    (N : ℕ) (b R : ℝ) : ℂ :=
  (((active.val : ℂ) / (active.val.totient : ℂ)) *
      logWeight R canonicalLogBump active.val) *
    (powerWeight b N : ℂ) * chi.val (N : ZMod active.val)

/-- Exact normal form of the localized adjusted factor for the canonical
weight. -/
theorem divisorLocalizedAdjustedFactor_canonical_eq
    {Q : ℕ} (hQ : 1 ≤ Q) (active : PositiveLevel Q)
    (chi : {χ : DirichletCharacter ℂ active.val // χ.IsPrimitive})
    (N : ℕ) (b R : ℝ) :
    divisorLocalizedAdjustedFactor hQ active chi N b
        (logWeight R canonicalLogBump) =
      divisorLocalizedFiniteCompanion active (oneLevel hQ) N
          (logWeight R canonicalLogBump) -
        localizedActiveCorrection active chi N b R := by
  rw [divisorLocalizedAdjustedFactor_eq_explicitActiveScalar hQ]
  rfl

/-- Fail-closed localized reserve: principal floor one minus the exact active
correction norm. -/
theorem one_sub_correction_norm_le_localizedAdjusted_re
    {Q : ℕ} (hQ : 1 ≤ Q) (active : PositiveLevel Q)
    (chi : {χ : DirichletCharacter ℂ active.val // χ.IsPrimitive})
    (N : ℕ) (hN : Nat.Coprime N active.val) (b R : ℝ) :
    1 - ‖localizedActiveCorrection active chi N b R‖ ≤
      (divisorLocalizedAdjustedFactor hQ active chi N b
        (logWeight R canonicalLogBump)).re := by
  rw [divisorLocalizedAdjustedFactor_canonical_eq hQ]
  simp only [Complex.sub_re]
  have hprincipal :=
    one_le_divisorLocalizedFiniteCompanion_oneLevel_canonical_re
      hQ active N hN R
  have hcorrection := Complex.re_le_norm (localizedActiveCorrection active chi N b R)
  linarith

/-- The exact remaining condition for strict positivity of the localized
adjusted channel. -/
theorem localizedAdjusted_re_pos_of_correction_norm_lt_one
    {Q : ℕ} (hQ : 1 ≤ Q) (active : PositiveLevel Q)
    (chi : {χ : DirichletCharacter ℂ active.val // χ.IsPrimitive})
    (N : ℕ) (hN : Nat.Coprime N active.val) (b R : ℝ)
    (hcorr : ‖localizedActiveCorrection active chi N b R‖ < 1) :
    0 < (divisorLocalizedAdjustedFactor hQ active chi N b
      (logWeight R canonicalLogBump)).re := by
  have hreserve := one_sub_correction_norm_le_localizedAdjusted_re
    hQ active chi N hN b R
  linarith

end GoldbachCircleMethodLocalizedAdjustedExplicitCorrectionReserveV18297

