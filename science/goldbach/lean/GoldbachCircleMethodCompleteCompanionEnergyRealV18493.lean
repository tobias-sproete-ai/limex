import GoldbachCircleMethodCompleteCompanionEnergyV18492

/-!
# Goldbach V1.8.493: real complete-period coefficient energy

The complex diagonal from V1.8.492 is normalized into an exact real identity.
The zero-frequency Ramanujan factor is evaluated as Euler's totient and the
literal coefficients are converted to squared norms.  No incomplete-period
or asymptotic claim is made.
-/

set_option autoImplicit false

open scoped BigOperators Classical ComplexConjugate

namespace GoldbachCircleMethodCompleteCompanionEnergyRealV18493

open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodFiniteResiduePrefixV1866
open GoldbachCircleMethodActualCompanionPeriodicLiftV18202
open GoldbachCircleMethodActualCompanionCompleteDiagonalV18204
open GoldbachCircleMethodFiniteRamanujanEnergyV18131
open GoldbachCircleMethodCompleteCompanionEnergyV18492

/-- Zero frequency counts the reduced residue classes exactly. -/
theorem unitCharacterSum_zero_eq_totient (q : ℕ) [NeZero q] :
    unitCharacterSum q 0 = (q.totient : ℂ) := by
  unfold unitCharacterSum
  simp only [zero_mul]
  rw [← Finset.sum_filter]
  simp [unit_residue_card]

private theorem star_mul_eq_norm_sq (z : ℂ) :
    star z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, ← Complex.sq_norm]

/-- A real literal coefficient squares to its real squared norm. -/
theorem literalCoefficient_sq_eq_norm_sq
    {Q : ℕ} (r l : PositiveLevel Q) (w : ℕ → ℂ)
    (hw : ∀ n : ℕ, star (w n) = w n) :
    literalCoefficient r l w * literalCoefficient r l w =
      ((‖literalCoefficient r l w‖ ^ 2 : ℝ) : ℂ) := by
  calc
    _ = star (literalCoefficient r l w) * literalCoefficient r l w := by
      rw [star_literalCoefficient r l w hw]
    _ = _ := star_mul_eq_norm_sq (literalCoefficient r l w)

/-- Exact real Parseval-type identity for the original finite companion over
one complete common period. -/
theorem complete_period_companion_energy_real
    {Q K : ℕ} [NeZero K]
    (hK : ∀ l : PositiveLevel Q, l.val ∣ K)
    (r : PositiveLevel Q) (w : ℕ → ℂ)
    (hw : ∀ n : ℕ, star (w n) = w n) :
    (∑ x : ZMod K, ‖periodicCompanion r w x‖ ^ 2) =
      (K : ℝ) * ∑ l : PositiveLevel Q,
        ‖literalCoefficient r l w‖ ^ 2 * (l.val.totient : ℝ) := by
  have h := complete_period_companion_energy_complex hK r w hw
  simp_rw [literalCoefficient_sq_eq_norm_sq r _ w hw,
    unitCharacterSum_zero_eq_totient] at h
  exact_mod_cast h

end GoldbachCircleMethodCompleteCompanionEnergyRealV18493
