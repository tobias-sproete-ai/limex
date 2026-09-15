import GoldbachCircleMethodActiveConductorCommonPeriodMismatchV18289

/-!
# Goldbach V1.8.290: active-conductor divisor localization

The full finite companion is split exactly into denominator levels dividing
the active conductor and the complementary levels.  This preserves the
periodic channel that may legitimately use the active conductor while keeping
every non-divisor denominator as an explicit error channel.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodActiveConductorDivisorLocalizationV18290

open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodFiniteCompanionBindingV18118
open GoldbachCircleMethodFiniteResiduePrefixV1866
open GoldbachCircleMethodPrincipalWindowBoundaryV18121
open GoldbachCircleMethodExceptionalWeightBoundaryV18128
open GoldbachCircleMethodActiveExceptionalCenteringV18129
open GoldbachCircleMethodSupportedAdjustedModelBindingAuditV18285

/-- The ungated summand appearing in the literal finite companion. -/
noncomputable def companionKernelTerm {Q : ℕ}
    (r l : PositiveLevel Q) (N : ℕ) (w : ℕ → ℂ) : ℂ :=
  ((ArithmeticFunction.moebius l.val : ℤ) : ℂ) *
    unitCharacterSum l.val (N : ZMod l.val) / (l.val.totient : ℂ) *
      w (r.val*l.val)

/-- Exact part of a finite companion supported on denominator levels dividing
the chosen active conductor. -/
noncomputable def divisorLocalizedFiniteCompanion {Q : ℕ}
    (active r : PositiveLevel Q) (N : ℕ) (w : ℕ → ℂ) : ℂ :=
  ∑ l : PositiveLevel Q,
    if r.val*l.val ≤ Q ∧ Nat.Coprime r.val l.val ∧ l.val ∣ active.val then
      companionKernelTerm r l N w
    else 0

/-- Exact complementary part, retaining every admissible denominator that
does not divide the active conductor. -/
noncomputable def offDivisorFiniteCompanion {Q : ℕ}
    (active r : PositiveLevel Q) (N : ℕ) (w : ℕ → ℂ) : ℂ :=
  ∑ l : PositiveLevel Q,
    if r.val*l.val ≤ Q ∧ Nat.Coprime r.val l.val ∧ ¬ l.val ∣ active.val then
      companionKernelTerm r l N w
    else 0

/-- Exact partition of the original companion; no term is discarded and no
new analytic estimate is assumed. -/
theorem finiteCompanion_eq_divisorLocalized_add_offDivisor {Q : ℕ}
    (active r : PositiveLevel Q) (N : ℕ) (w : ℕ → ℂ) :
    finiteCompanion r N w =
      divisorLocalizedFiniteCompanion active r N w +
        offDivisorFiniteCompanion active r N w := by
  unfold finiteCompanion divisorLocalizedFiniteCompanion
    offDivisorFiniteCompanion companionKernelTerm
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro l _hl
  by_cases hbase : r.val*l.val ≤ Q ∧ Nat.Coprime r.val l.val
  · by_cases hdiv : l.val ∣ active.val
    · simp [hbase, hdiv]
    · simp [hbase, hdiv]
  · have hlocal :
        ¬ (r.val*l.val ≤ Q ∧ Nat.Coprime r.val l.val ∧
          l.val ∣ active.val) := by
      intro h
      exact hbase ⟨h.1, h.2.1⟩
    have hoff :
        ¬ (r.val*l.val ≤ Q ∧ Nat.Coprime r.val l.val ∧
          ¬ l.val ∣ active.val) := by
      intro h
      exact hbase ⟨h.1, h.2.1⟩
    simp [hbase, hlocal, hoff]

/-- Localized active radial amplitude. -/
noncomputable def divisorLocalizedActiveRadialAmplitude {Q : ℕ}
    (active : PositiveLevel Q) (N : ℕ) (w : ℕ → ℂ) : ℂ :=
  ((active.val : ℂ) / (active.val.totient : ℂ)) *
    divisorLocalizedFiniteCompanion active active N w

/-- Off-divisor active radial amplitude. -/
noncomputable def offDivisorActiveRadialAmplitude {Q : ℕ}
    (active : PositiveLevel Q) (N : ℕ) (w : ℕ → ℂ) : ℂ :=
  ((active.val : ℂ) / (active.val.totient : ℂ)) *
    offDivisorFiniteCompanion active active N w

/-- Exact amplitude split at the active radial channel. -/
theorem activeRadialAmplitude_eq_divisorLocalized_add_offDivisor {Q : ℕ}
    (active : PositiveLevel Q) (N : ℕ) (w : ℕ → ℂ) :
    activeRadialAmplitude active N w =
      divisorLocalizedActiveRadialAmplitude active N w +
        offDivisorActiveRadialAmplitude active N w := by
  unfold activeRadialAmplitude divisorLocalizedActiveRadialAmplitude
    offDivisorActiveRadialAmplitude
  rw [finiteCompanion_eq_divisorLocalized_add_offDivisor]
  ring

/-- The part of the adjusted factor whose companion denominators divide the
active conductor. -/
noncomputable def divisorLocalizedAdjustedFactor {Q : ℕ} (hQ : 1 ≤ Q)
    (active : PositiveLevel Q)
    (chi : {χ : DirichletCharacter ℂ active.val // χ.IsPrimitive})
    (N : ℕ) (b : ℝ) (w : ℕ → ℂ) : ℂ :=
  divisorLocalizedFiniteCompanion active (oneLevel hQ) N w -
    divisorLocalizedActiveRadialAmplitude active N w *
      (powerWeight b N : ℂ) * chi.val (N : ZMod active.val)

/-- The exact off-divisor remainder of the adjusted factor. -/
noncomputable def offDivisorAdjustedFactor {Q : ℕ} (hQ : 1 ≤ Q)
    (active : PositiveLevel Q)
    (chi : {χ : DirichletCharacter ℂ active.val // χ.IsPrimitive})
    (N : ℕ) (b : ℝ) (w : ℕ → ℂ) : ℂ :=
  offDivisorFiniteCompanion active (oneLevel hQ) N w -
    offDivisorActiveRadialAmplitude active N w *
      (powerWeight b N : ℂ) * chi.val (N : ZMod active.val)

/-- Exact two-channel decomposition of the actual amplitude-aware adjusted
factor.  Positivity is not claimed for either channel. -/
theorem amplitudeAdjustedFactor_eq_divisorLocalized_add_offDivisor
    {Q : ℕ} (hQ : 1 ≤ Q)
    (active : PositiveLevel Q)
    (chi : {χ : DirichletCharacter ℂ active.val // χ.IsPrimitive})
    (N : ℕ) (b : ℝ) (w : ℕ → ℂ) :
    amplitudeAdjustedFactor hQ active chi N b w =
      divisorLocalizedAdjustedFactor hQ active chi N b w +
        offDivisorAdjustedFactor hQ active chi N b w := by
  unfold amplitudeAdjustedFactor divisorLocalizedAdjustedFactor
    offDivisorAdjustedFactor
  rw [finiteCompanion_eq_divisorLocalized_add_offDivisor,
    activeRadialAmplitude_eq_divisorLocalized_add_offDivisor]
  ring

end GoldbachCircleMethodActiveConductorDivisorLocalizationV18290
