import GoldbachCircleMethodCanonicalAdjustedFourChannelBindingV18293

/-!
# Goldbach V1.8.294: localized active companion collapse

In the localized active companion a denominator `l` both divides the active
conductor and is coprime to it.  Hence `l = 1`, so the whole finite sum
collapses exactly to the single conductor-one term.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodLocalizedActiveCompanionCollapseV18294

open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodFiniteResiduePrefixV1866
open GoldbachCircleMethodPrincipalWindowBoundaryV18121
open GoldbachCircleMethodActiveConductorDivisorLocalizationV18290

/-- The divisor-localized companion at the active conductor contains only the
denominator-one term. -/
theorem divisorLocalizedFiniteCompanion_active_eq_weight
    {Q : ℕ} (hQ : 1 ≤ Q) (active : PositiveLevel Q)
    (N : ℕ) (w : ℕ → ℂ) :
    divisorLocalizedFiniteCompanion active active N w = w active.val := by
  unfold divisorLocalizedFiniteCompanion
  rw [Finset.sum_eq_single (oneLevel hQ)]
  · have hactiveQ : active.val ≤ Q := (Finset.mem_Icc.mp active.property).2
    have hunit : unitCharacterSum 1 (N : ZMod 1) = 1 := by
      have hone : (1 : ZMod 1) = default := Subsingleton.elim _ _
      have hchar :
          ZMod.stdAddChar ((N : ZMod 1) * default) = 1 := by
        rw [Subsingleton.elim ((N : ZMod 1) * default) 0]
        exact AddChar.map_zero_eq_one _
      unfold unitCharacterSum
      simpa [hone, hchar]
    have hgate :
        active.val * (oneLevel hQ).val ≤ Q ∧
          Nat.Coprime active.val (oneLevel hQ).val ∧
            (oneLevel hQ).val ∣ active.val := by
      simp [oneLevel, hactiveQ]
    rw [if_pos hgate]
    unfold companionKernelTerm
    simp only [oneLevel]
    rw [ArithmeticFunction.moebius_apply_one]
    norm_num
    exact hunit ▸ one_mul (w active.val)
  · intro l _hl hne
    rw [if_neg]
    intro hgate
    have hl1 : l.val = 1 := hgate.2.1.symm.eq_one_of_dvd hgate.2.2
    exact hne (Subtype.ext hl1)
  · simp

/-- The localized active radial amplitude therefore has one explicit scalar
coefficient and no hidden denominator sum. -/
theorem divisorLocalizedActiveRadialAmplitude_eq
    {Q : ℕ} (hQ : 1 ≤ Q) (active : PositiveLevel Q)
    (N : ℕ) (w : ℕ → ℂ) :
    divisorLocalizedActiveRadialAmplitude active N w =
      ((active.val : ℂ) / (active.val.totient : ℂ)) * w active.val := by
  unfold divisorLocalizedActiveRadialAmplitude
  rw [divisorLocalizedFiniteCompanion_active_eq_weight hQ]

/-- Exact localized adjusted-factor normal form after the active companion
collapse.  The localized principal companion remains visible. -/
theorem divisorLocalizedAdjustedFactor_eq_explicitActiveScalar
    {Q : ℕ} (hQ : 1 ≤ Q) (active : PositiveLevel Q)
    (chi : {χ : DirichletCharacter ℂ active.val // χ.IsPrimitive})
    (N : ℕ) (b : ℝ) (w : ℕ → ℂ) :
    divisorLocalizedAdjustedFactor hQ active chi N b w =
      divisorLocalizedFiniteCompanion active (oneLevel hQ) N w -
        (((active.val : ℂ) / (active.val.totient : ℂ)) * w active.val) *
          (GoldbachCircleMethodExceptionalWeightBoundaryV18128.powerWeight b N : ℂ) *
            chi.val (N : ZMod active.val) := by
  unfold divisorLocalizedAdjustedFactor
  rw [divisorLocalizedActiveRadialAmplitude_eq hQ]

end GoldbachCircleMethodLocalizedActiveCompanionCollapseV18294
