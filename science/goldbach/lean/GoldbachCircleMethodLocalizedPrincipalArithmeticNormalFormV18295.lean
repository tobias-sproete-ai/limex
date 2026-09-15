import GoldbachCircleMethodLocalizedActiveCompanionCollapseV18294

/-!
# Goldbach V1.8.295: localized principal arithmetic normal form

For a target coprime to the active conductor, every denominator localized by
`l ∣ active` also sees a unit target.  The Ramanujan character sum therefore
equals the Moebius value, turning the principal localized companion into an
explicit finite Moebius-square sum.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodLocalizedPrincipalArithmeticNormalFormV18295

open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodFiniteResiduePrefixV1866
open GoldbachCircleMethodPrincipalWindowBoundaryV18121
open GoldbachCircleMethodGeneralCoprimeCharacterV1868
open GoldbachCircleMethodActiveConductorDivisorLocalizationV18290

/-- The explicit arithmetic term left after evaluating the coprime Ramanujan
sum in the localized principal companion. -/
noncomputable def localizedPrincipalArithmeticTerm
    (l : ℕ) (w : ℕ → ℂ) : ℂ :=
  (((ArithmeticFunction.moebius l : ℤ) : ℂ) ^ 2 /
      (l.totient : ℂ)) * w l

/-- Exact arithmetic normal form for the localized principal companion.
No positivity or analytic estimate is used. -/
theorem divisorLocalizedFiniteCompanion_oneLevel_eq_arithmeticSum
    {Q : ℕ} (hQ : 1 ≤ Q) (active : PositiveLevel Q)
    (N : ℕ) (hN : Nat.Coprime N active.val) (w : ℕ → ℂ) :
    divisorLocalizedFiniteCompanion active (oneLevel hQ) N w =
      ∑ l : PositiveLevel Q,
        if l.val ∣ active.val then
          localizedPrincipalArithmeticTerm l.val w
        else 0 := by
  unfold divisorLocalizedFiniteCompanion
  apply Finset.sum_congr rfl
  intro l _hl
  by_cases hdiv : l.val ∣ active.val
  · have hlQ : l.val ≤ Q := (Finset.mem_Icc.mp l.property).2
    have hlpos : 0 < l.val := (Finset.mem_Icc.mp l.property).1
    let _ : NeZero l.val := ⟨Nat.ne_of_gt hlpos⟩
    have hgate :
        (oneLevel hQ).val * l.val ≤ Q ∧
          Nat.Coprime (oneLevel hQ).val l.val ∧ l.val ∣ active.val := by
      simpa [oneLevel] using And.intro hlQ (And.intro (Nat.coprime_one_left l.val) hdiv)
    have hNl : Nat.Coprime N l.val := hN.of_dvd_right hdiv
    have hunit : IsUnit (N : ZMod l.val) :=
      (ZMod.isUnit_iff_coprime N l.val).mpr hNl
    rw [if_pos hgate, if_pos hdiv]
    unfold companionKernelTerm localizedPrincipalArithmeticTerm
    rw [unitCharacterSum_eq_moebius l.val (N : ZMod l.val) hunit]
    simp only [oneLevel, one_mul]
    ring
  · simp [hdiv]

end GoldbachCircleMethodLocalizedPrincipalArithmeticNormalFormV18295

