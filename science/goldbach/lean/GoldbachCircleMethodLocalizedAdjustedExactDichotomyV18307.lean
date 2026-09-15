import GoldbachCircleMethodNoncoprimeLocalizedAdjustedVanishingV18305

/-!
# Goldbach V1.8.307: localized adjusted exact dichotomy

The localized adjusted factor is evaluated exactly on the canonical plateau.
On reduced residue classes it is a totient-ratio scalar times the literal
exceptional-character factor; outside those classes it is zero.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodLocalizedAdjustedExactDichotomyV18307

open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodPrincipalWindowBoundaryV18121
open GoldbachCircleMethodLogCutoffPresieveBindingV18120
open GoldbachCircleMethodCanonicalBumpPrincipalFloorV18220
open GoldbachCircleMethodCanonicalBumpResidualMomentsV18222
open GoldbachCircleMethodActualMultiplierScaleV18135
open GoldbachCircleMethodExceptionalWeightBoundaryV18128
open GoldbachCircleMethodActiveConductorDivisorLocalizationV18290
open GoldbachCircleMethodLocalizedAdjustedExplicitCorrectionReserveV18297
open GoldbachCircleMethodCanonicalWeightLocalizedRadicalDichotomyV18301
open GoldbachCircleMethodNoncoprimeLocalizedAdjustedVanishingV18305

/-- The canonical plateau removes the remaining active-conductor cutoff
weight from the explicit correction. -/
theorem localizedActiveCorrection_canonical_eq
    {Q : ℕ} (active : PositiveLevel Q)
    (chi : {χ : DirichletCharacter ℂ active.val // χ.IsPrimitive})
    (N : ℕ) (b R : ℝ) (hR : 1 < R)
    (hactiveR : (active.val : ℝ) ≤ R) :
    localizedActiveCorrection active chi N b R =
      ((active.val : ℂ) / (active.val.totient : ℂ)) *
        (powerWeight b N : ℂ) * chi.val (N : ZMod active.val) := by
  unfold localizedActiveCorrection
  rw [log_weight_eq_one R hR canonicalLogBump
    (fun _ hx0 hx1 => canonicalLogBump_plateau hx0 hx1)
    active.val (Nat.pos_of_ne_zero (NeZero.ne active.val)) hactiveR]
  ring

/-- Exact reduced-residue normal form. -/
theorem divisorLocalizedAdjustedFactor_canonical_eq_of_coprime
    {Q : ℕ} (hQ : 1 ≤ Q) (active : PositiveLevel Q)
    (chi : {χ : DirichletCharacter ℂ active.val // χ.IsPrimitive})
    (N : ℕ) (hN : Nat.Coprime N active.val)
    (b R : ℝ) (hR : 1 < R) (hactiveR : (active.val : ℝ) ≤ R) :
    divisorLocalizedAdjustedFactor hQ active chi N b
        (logWeight R canonicalLogBump) =
      ((active.val : ℂ) / (active.val.totient : ℂ)) *
        (1 - (powerWeight b N : ℂ) *
          chi.val (N : ZMod active.val)) := by
  rw [divisorLocalizedAdjustedFactor_canonical_eq hQ]
  rw [divisorLocalizedFiniteCompanion_oneLevel_canonical_eq_ite
    hQ active N R hR hactiveR]
  rw [if_pos hN]
  rw [localizedActiveCorrection_canonical_eq
    active chi N b R hR hactiveR]
  ring

/-- Full exact dichotomy, including the zero branch outside the reduced
residue classes. -/
theorem divisorLocalizedAdjustedFactor_canonical_eq_ite
    {Q : ℕ} (hQ : 1 ≤ Q) (active : PositiveLevel Q)
    (chi : {χ : DirichletCharacter ℂ active.val // χ.IsPrimitive})
    (N : ℕ) (b R : ℝ) (hR : 1 < R)
    (hactiveR : (active.val : ℝ) ≤ R) :
    divisorLocalizedAdjustedFactor hQ active chi N b
        (logWeight R canonicalLogBump) =
      if Nat.Coprime N active.val then
        ((active.val : ℂ) / (active.val.totient : ℂ)) *
          (1 - (powerWeight b N : ℂ) *
            chi.val (N : ZMod active.val))
      else 0 := by
  by_cases hN : Nat.Coprime N active.val
  · rw [if_pos hN]
    exact divisorLocalizedAdjustedFactor_canonical_eq_of_coprime
      hQ active chi N hN b R hR hactiveR
  · rw [if_neg hN]
    exact divisorLocalizedAdjustedFactor_canonical_eq_zero_of_not_coprime
      hQ active chi N hN b R hR hactiveR

end GoldbachCircleMethodLocalizedAdjustedExactDichotomyV18307
