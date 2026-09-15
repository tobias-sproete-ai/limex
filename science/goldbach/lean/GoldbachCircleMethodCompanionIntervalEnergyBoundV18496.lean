import GoldbachCircleMethodCompanionIntervalEnergyDeviationV18495

/-!
# Goldbach V1.8.496: real incomplete companion-energy bound

The complex deviation inequality from V1.8.495 is converted into the real
upper bound consumed by coefficient-moment estimates.  The diagonal and the
quartic endpoint cost remain explicit.
-/

set_option autoImplicit false

open scoped BigOperators Classical ComplexConjugate

namespace GoldbachCircleMethodCompanionIntervalEnergyBoundV18496

open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodFiniteCompanionBindingV18118
open GoldbachCircleMethodActualCompanionCompleteDiagonalV18204
open GoldbachCircleMethodCompleteCompanionEnergyV18492
open GoldbachCircleMethodCompleteCompanionEnergyRealV18493
open GoldbachCircleMethodCompanionIntervalEnergyDeviationV18495

/-- Real upper bound on one incomplete natural interval. -/
theorem finiteCompanion_interval_energy_le
    {Q : ℕ} (r : PositiveLevel Q) (w : ℕ → ℂ)
    (hwReal : ∀ n : ℕ, star (w n) = w n)
    (A T : ℕ) (V : ℝ) (hV : 0 ≤ V)
    (hwBound : ∀ q : PositiveLevel Q,
      r.val * q.val ≤ Q ∧ Nat.Coprime r.val q.val →
        ‖w (r.val * q.val)‖ ≤ V) :
    (∑ i ∈ Finset.range T, ‖finiteCompanion r (A + i) w‖ ^ 2) ≤
      (T : ℝ) * (∑ q : PositiveLevel Q,
        ‖literalCoefficient r q w‖ ^ 2 * (q.val.totient : ℝ)) +
        2 * (Q : ℝ) ^ 4 * V * V := by
  have h := finiteCompanion_interval_energy_deviation_le
    r w hwReal A T V hV hwBound
  have hsum :
      (∑ i ∈ Finset.range T,
        ((‖finiteCompanion r (A + i) w‖ ^ 2 : ℝ) : ℂ)) =
      (((∑ i ∈ Finset.range T,
        ‖finiteCompanion r (A + i) w‖ ^ 2) : ℝ) : ℂ) := by
    push_cast
    rfl
  have hdiag :
      (∑ q : PositiveLevel Q,
        literalCoefficient r q w * literalCoefficient r q w *
          GoldbachCircleMethodFiniteResiduePrefixV1866.unitCharacterSum q.val 0) =
      (((∑ q : PositiveLevel Q,
        ‖literalCoefficient r q w‖ ^ 2 * (q.val.totient : ℝ)) : ℝ) : ℂ) := by
    push_cast
    apply Finset.sum_congr rfl
    intro q _hq
    rw [literalCoefficient_sq_eq_norm_sq r q w hwReal,
      unitCharacterSum_zero_eq_totient]
    push_cast
    ring
  rw [hsum, hdiag] at h
  have habs :
      ‖((∑ i ∈ Finset.range T, ‖finiteCompanion r (A + i) w‖ ^ 2) -
        (T : ℝ) * (∑ q : PositiveLevel Q,
          ‖literalCoefficient r q w‖ ^ 2 * (q.val.totient : ℝ)))‖ ≤
        2 * (Q : ℝ) ^ 4 * V * V := by
    simpa only [← Complex.ofReal_natCast, ← Complex.ofReal_mul,
      ← Complex.ofReal_sub, Complex.norm_real] using h
  have hdiff :
      (∑ i ∈ Finset.range T, ‖finiteCompanion r (A + i) w‖ ^ 2) -
        (T : ℝ) * (∑ q : PositiveLevel Q,
          ‖literalCoefficient r q w‖ ^ 2 * (q.val.totient : ℝ)) ≤
        2 * (Q : ℝ) ^ 4 * V * V := by
    apply (le_abs_self _).trans
    simpa only [Real.norm_eq_abs] using habs
  linarith

end GoldbachCircleMethodCompanionIntervalEnergyBoundV18496
