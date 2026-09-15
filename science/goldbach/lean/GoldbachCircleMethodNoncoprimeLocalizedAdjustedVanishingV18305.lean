import GoldbachCircleMethodLocalizedAdjustedExplicitCorrectionReserveV18297
import GoldbachCircleMethodCanonicalWeightLocalizedRadicalDichotomyV18301

/-!
# Goldbach V1.8.305: noncoprime localized adjusted vanishing

The even/even vanishing of V1.8.302 is generalized to the exact arithmetic
condition.  Whenever an evaluation argument is not coprime to the active
conductor, both the canonical localized principal companion and the primitive
character correction vanish, so the full localized adjusted factor is zero.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodNoncoprimeLocalizedAdjustedVanishingV18305

open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodPrincipalWindowBoundaryV18121
open GoldbachCircleMethodLogCutoffPresieveBindingV18120
open GoldbachCircleMethodCanonicalBumpPrincipalFloorV18220
open GoldbachCircleMethodActiveConductorDivisorLocalizationV18290
open GoldbachCircleMethodLocalizedAdjustedExplicitCorrectionReserveV18297
open GoldbachCircleMethodCanonicalWeightLocalizedRadicalDichotomyV18301

/-- Noncoprimality with the active conductor is exactly a nonunit condition in
the corresponding residue ring. -/
theorem not_isUnit_zmod_of_not_coprime
    {Q : ℕ} (active : PositiveLevel Q) (N : ℕ)
    (hN : ¬ Nat.Coprime N active.val) :
    ¬ IsUnit (N : ZMod active.val) := by
  intro hunit
  exact hN ((ZMod.isUnit_iff_coprime N active.val).mp hunit)

/-- A primitive character vanishes outside the reduced residue classes. -/
theorem primitiveCharacter_eq_zero_of_not_coprime
    {Q : ℕ} (active : PositiveLevel Q)
    (chi : {χ : DirichletCharacter ℂ active.val // χ.IsPrimitive})
    (N : ℕ) (hN : ¬ Nat.Coprime N active.val) :
    chi.val (N : ZMod active.val) = 0 := by
  exact chi.val.map_nonunit (not_isUnit_zmod_of_not_coprime active N hN)

/-- The explicit active-character correction vanishes outside the reduced
residue classes. -/
theorem localizedActiveCorrection_eq_zero_of_not_coprime
    {Q : ℕ} (active : PositiveLevel Q)
    (chi : {χ : DirichletCharacter ℂ active.val // χ.IsPrimitive})
    (N : ℕ) (hN : ¬ Nat.Coprime N active.val) (b R : ℝ) :
    localizedActiveCorrection active chi N b R = 0 := by
  unfold localizedActiveCorrection
  rw [primitiveCharacter_eq_zero_of_not_coprime active chi N hN]
  simp

/-- Exact canonical localized-factor vanishing away from the reduced residue
classes of the active conductor. -/
theorem divisorLocalizedAdjustedFactor_canonical_eq_zero_of_not_coprime
    {Q : ℕ} (hQ : 1 ≤ Q) (active : PositiveLevel Q)
    (chi : {χ : DirichletCharacter ℂ active.val // χ.IsPrimitive})
    (N : ℕ) (hN : ¬ Nat.Coprime N active.val)
    (b R : ℝ) (hR : 1 < R) (hactiveR : (active.val : ℝ) ≤ R) :
    divisorLocalizedAdjustedFactor hQ active chi N b
        (logWeight R canonicalLogBump) = 0 := by
  rw [divisorLocalizedAdjustedFactor_canonical_eq hQ]
  rw [divisorLocalizedFiniteCompanion_oneLevel_canonical_eq_ite
    hQ active N R hR hactiveR]
  rw [if_neg hN]
  rw [localizedActiveCorrection_eq_zero_of_not_coprime
    active chi N hN b R]
  simp

end GoldbachCircleMethodNoncoprimeLocalizedAdjustedVanishingV18305

