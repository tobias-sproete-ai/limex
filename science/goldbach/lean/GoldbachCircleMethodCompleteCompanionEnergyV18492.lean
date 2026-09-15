import GoldbachCircleMethodRealWeightCompanionReflectionV18491
import GoldbachCircleMethodActualCompanionCompleteDiagonalV18204

/-!
# Goldbach V1.8.492: complete-period companion energy

The conjugation adapter from V1.8.491 is composed with the already audited
mixed Ramanujan orthogonality.  The result is an exact complete-period energy
identity for the original finite companion.  No incomplete-block estimate or
asymptotic saving is claimed here.
-/

set_option autoImplicit false

open scoped BigOperators Classical ComplexConjugate

namespace GoldbachCircleMethodCompleteCompanionEnergyV18492

open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodFiniteCompanionBindingV18118
open GoldbachCircleMethodFiniteResiduePrefixV1866
open GoldbachCircleMethodActualCompanionPeriodicLiftV18202
open GoldbachCircleMethodActualCompanionCompleteDiagonalV18204
open GoldbachCircleMethodRealWeightCompanionReflectionV18491

/-- The literal coefficient is real whenever the original weight is real. -/
theorem star_literalCoefficient
    {Q : ℕ} (r l : PositiveLevel Q) (w : ℕ → ℂ)
    (hw : ∀ n : ℕ, star (w n) = w n) :
    star (literalCoefficient r l w) = literalCoefficient r l w := by
  unfold literalCoefficient
  by_cases hsupport : r.val * l.val ≤ Q ∧ Nat.Coprime r.val l.val
  · rw [if_pos hsupport, star_mul, hw, star_div₀]
    norm_num [Complex.star_def]
    ring
  · simp [hsupport]

/-- On a declared common period, conjugating the actual companion is exactly
the modular reflection `x ↦ -x`. -/
theorem star_periodicCompanion
    {Q K : ℕ} [NeZero K]
    (hK : ∀ l : PositiveLevel Q, l.val ∣ K)
    (r : PositiveLevel Q) (w : ℕ → ℂ)
    (hw : ∀ n : ℕ, star (w n) = w n) (x : ZMod K) :
    star (periodicCompanion r w x) = periodicCompanion r w (-x) := by
  rw [periodicCompanion_expansion hK, periodicCompanion_expansion hK]
  simp_rw [star_sum]
  apply Finset.sum_congr rfl
  intro l _hl
  rw [star_mul, star_unitCharacterSum, star_literalCoefficient r l w hw]
  rw [map_neg]
  ring

private theorem star_mul_eq_norm_sq (z : ℂ) :
    star z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, ← Complex.sq_norm]

/-- Exact energy identity over one complete common period.  The right-hand
side retains the literal diagonal coefficients and the genuine Ramanujan
factor at zero frequency. -/
theorem complete_period_companion_energy_complex
    {Q K : ℕ} [NeZero K]
    (hK : ∀ l : PositiveLevel Q, l.val ∣ K)
    (r : PositiveLevel Q) (w : ℕ → ℂ)
    (hw : ∀ n : ℕ, star (w n) = w n) :
    (∑ x : ZMod K, ((‖periodicCompanion r w x‖ ^ 2 : ℝ) : ℂ)) =
      (K : ℂ) * ∑ l : PositiveLevel Q,
        literalCoefficient r l w * literalCoefficient r l w *
          unitCharacterSum l.val 0 := by
  have hdiag :
      (∑ x : ZMod K,
        periodicCompanion r w ((0 : ZMod K) - x) * periodicCompanion r w x) =
        (K : ℂ) * ∑ l : PositiveLevel Q,
          literalCoefficient r l w * literalCoefficient r l w *
            unitCharacterSum l.val 0 := by
    simpa only [map_zero] using
      (actual_companion_complete_diagonal hK r r w w (0 : ZMod K))
  rw [← hdiag]
  apply Finset.sum_congr rfl
  intro x _hx
  rw [zero_sub, ← star_periodicCompanion hK r w hw x]
  exact (star_mul_eq_norm_sq (periodicCompanion r w x)).symm

end GoldbachCircleMethodCompleteCompanionEnergyV18492
