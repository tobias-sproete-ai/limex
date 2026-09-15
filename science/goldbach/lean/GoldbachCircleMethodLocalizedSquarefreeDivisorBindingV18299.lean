import GoldbachCircleMethodEvenConductorCoprimeBranchObstructionV18298
import GoldbachCircleMethodRadicalLocalCoefficientV18201

/-!
# Goldbach V1.8.299: localized squarefree-divisor binding

The actual localized principal companion is rewritten on its exact
squarefree-divisor carrier.  Non-squarefree denominators vanish because of
the literal Moebius coefficient; no denominator is removed heuristically.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodLocalizedSquarefreeDivisorBindingV18299

open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodFiniteResiduePrefixV1866
open GoldbachCircleMethodPrincipalWindowBoundaryV18121
open GoldbachCircleMethodActualCoupledCutoffAdapterV18199
open GoldbachCircleMethodActiveConductorDivisorLocalizationV18290

/-- The exact squarefree-divisor form on the original positive-level
carrier. -/
noncomputable def localizedSquarefreeDivisorSum {Q : ℕ}
    (active : PositiveLevel Q) (N : ℕ) (w : ℕ → ℂ) : ℂ :=
  ∑ l : PositiveLevel Q,
    if Squarefree l.val ∧ l.val ∣ active.val then
      squarefreeCompanionCoefficient l.val N * w l.val
    else 0

/-- Exact binding of the literal localized principal companion to its
squarefree-divisor carrier. -/
theorem divisorLocalizedFiniteCompanion_oneLevel_eq_squarefreeDivisorSum
    {Q : ℕ} (hQ : 1 ≤ Q) (active : PositiveLevel Q)
    (N : ℕ) (w : ℕ → ℂ) :
    divisorLocalizedFiniteCompanion active (oneLevel hQ) N w =
      localizedSquarefreeDivisorSum active N w := by
  unfold divisorLocalizedFiniteCompanion localizedSquarefreeDivisorSum
  apply Finset.sum_congr rfl
  intro l _hl
  have hlQ : l.val ≤ Q := (Finset.mem_Icc.mp l.property).2
  have hlpos : 0 < l.val := (Finset.mem_Icc.mp l.property).1
  let _ : NeZero l.val := ⟨Nat.ne_of_gt hlpos⟩
  by_cases hdiv : l.val ∣ active.val
  · have hgate :
        (oneLevel hQ).val * l.val ≤ Q ∧
          Nat.Coprime (oneLevel hQ).val l.val ∧ l.val ∣ active.val := by
      simpa [oneLevel] using And.intro hlQ (And.intro (Nat.coprime_one_left l.val) hdiv)
    rw [if_pos hgate]
    by_cases hsq : Squarefree l.val
    · rw [if_pos ⟨hsq, hdiv⟩]
      unfold companionKernelTerm
      simp only [oneLevel, one_mul]
      rw [squarefreeCompanionCoefficient_eq_actual l.val N hsq]
    · rw [if_neg (by exact fun h => hsq h.1)]
      unfold companionKernelTerm
      rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq]
      norm_num
  · have hnot :
        ¬ ((oneLevel hQ).val * l.val ≤ Q ∧
          Nat.Coprime (oneLevel hQ).val l.val ∧ l.val ∣ active.val) := by
      exact fun h => hdiv h.2.2
    rw [if_neg hnot, if_neg]
    exact fun h => hdiv h.2

end GoldbachCircleMethodLocalizedSquarefreeDivisorBindingV18299

