import GoldbachCircleMethodActiveConductorDivisorLocalizationV18290

/-!
# Goldbach V1.8.291: divisor-localized active periodicity

Every denominator retained by the localized channel divides the active
conductor.  Hence the localized companions, localized active amplitude and a
frozen-power localized adjusted factor inherit the active-conductor period.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodDivisorLocalizedActivePeriodicityV18291

open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodPrincipalWindowBoundaryV18121
open GoldbachCircleMethodActiveExceptionalCenteringV18129
open GoldbachCircleMethodActiveConductorDivisorLocalizationV18290

/-- A localized companion has the active conductor as a genuine period,
because every surviving denominator divides that conductor. -/
theorem divisorLocalizedFiniteCompanion_periodic {Q : ℕ}
    (active r : PositiveLevel Q) (w : ℕ → ℂ) :
    Function.Periodic
      (fun N => divisorLocalizedFiniteCompanion active r N w) active.val := by
  intro N
  unfold divisorLocalizedFiniteCompanion
  apply Finset.sum_congr rfl
  intro l _hl
  by_cases hgate :
      r.val*l.val ≤ Q ∧ Nat.Coprime r.val l.val ∧ l.val ∣ active.val
  · rw [if_pos hgate, if_pos hgate]
    obtain ⟨k, hk⟩ := hgate.2.2
    unfold companionKernelTerm
    have hcast :
        ((N + active.val : ℕ) : ZMod l.val) = (N : ZMod l.val) := by
      rw [hk]
      simp only [Nat.cast_add, Nat.cast_mul, ZMod.natCast_self,
        zero_mul, add_zero]
    rw [hcast]
  · rw [if_neg hgate, if_neg hgate]

/-- The scalar multiple defining the localized active radial amplitude keeps
the same active-conductor period. -/
theorem divisorLocalizedActiveRadialAmplitude_periodic {Q : ℕ}
    (active : PositiveLevel Q) (w : ℕ → ℂ) :
    Function.Periodic
      (fun N => divisorLocalizedActiveRadialAmplitude active N w)
      active.val := by
  intro N
  unfold divisorLocalizedActiveRadialAmplitude
  have hcomp := divisorLocalizedFiniteCompanion_periodic active active w N
  change divisorLocalizedFiniteCompanion active active (N + active.val) w =
    divisorLocalizedFiniteCompanion active active N w at hcomp
  change ((active.val : ℂ) / (active.val.totient : ℂ)) *
      divisorLocalizedFiniteCompanion active active (N + active.val) w =
    ((active.val : ℂ) / (active.val.totient : ℂ)) *
      divisorLocalizedFiniteCompanion active active N w
  rw [hcomp]

/-- Localized adjusted factor with the spatial power replaced by one explicit
frozen scalar. -/
noncomputable def divisorLocalizedFrozenAdjustedFactor {Q : ℕ} (hQ : 1 ≤ Q)
    (active : PositiveLevel Q)
    (chi : {χ : DirichletCharacter ℂ active.val // χ.IsPrimitive})
    (w : ℕ → ℂ) (t : ℂ) (N : ℕ) : ℂ :=
  divisorLocalizedFiniteCompanion active (oneLevel hQ) N w -
    divisorLocalizedActiveRadialAmplitude active N w * t *
      chi.val (N : ZMod active.val)

/-- Exact pointwise readback: the non-frozen localized adjusted factor is the
frozen factor evaluated at its literal spatial power. -/
theorem divisorLocalizedAdjustedFactor_eq_frozen
    {Q : ℕ} (hQ : 1 ≤ Q)
    (active : PositiveLevel Q)
    (chi : {χ : DirichletCharacter ℂ active.val // χ.IsPrimitive})
    (N : ℕ) (b : ℝ) (w : ℕ → ℂ) :
    divisorLocalizedAdjustedFactor hQ active chi N b w =
      divisorLocalizedFrozenAdjustedFactor hQ active chi w
        (GoldbachCircleMethodExceptionalWeightBoundaryV18128.powerWeight b N : ℂ) N := by
  rfl

/-- With the power frozen, the entire localized adjusted factor has active
conductor period. -/
theorem divisorLocalizedFrozenAdjustedFactor_periodic
    {Q : ℕ} (hQ : 1 ≤ Q)
    (active : PositiveLevel Q)
    (chi : {χ : DirichletCharacter ℂ active.val // χ.IsPrimitive})
    (w : ℕ → ℂ) (t : ℂ) :
    Function.Periodic
      (divisorLocalizedFrozenAdjustedFactor hQ active chi w t)
      active.val := by
  intro N
  unfold divisorLocalizedFrozenAdjustedFactor
  have hprincipal :=
    divisorLocalizedFiniteCompanion_periodic active (oneLevel hQ) w N
  have hactive := divisorLocalizedActiveRadialAmplitude_periodic active w N
  change divisorLocalizedFiniteCompanion active (oneLevel hQ)
    (N + active.val) w =
      divisorLocalizedFiniteCompanion active (oneLevel hQ) N w at hprincipal
  change divisorLocalizedActiveRadialAmplitude active (N + active.val) w =
    divisorLocalizedActiveRadialAmplitude active N w at hactive
  rw [hprincipal, hactive]
  simp only [Nat.cast_add, ZMod.natCast_self, add_zero]

end GoldbachCircleMethodDivisorLocalizedActivePeriodicityV18291
