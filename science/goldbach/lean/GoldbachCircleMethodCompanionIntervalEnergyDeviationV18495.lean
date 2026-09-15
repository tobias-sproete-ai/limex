import GoldbachCircleMethodCommonReflectionPointV18494
import GoldbachCircleMethodCoupledCompanionRemainderBoundV18207

/-!
# Goldbach V1.8.495: incomplete companion-energy deviation

The canonical reflection point converts the existing pairwise-period
convolution estimate into a genuine squared-energy statement on an arbitrary
natural interval.  The explicit quartic endpoint cost is retained; this module
does not call that cost small.
-/

set_option autoImplicit false

open scoped BigOperators Classical ComplexConjugate

namespace GoldbachCircleMethodCompanionIntervalEnergyDeviationV18495

open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodFiniteCompanionBindingV18118
open GoldbachCircleMethodFiniteResiduePrefixV1866
open GoldbachCircleMethodActualCompanionCompleteDiagonalV18204
open GoldbachCircleMethodCoupledCompanionRemainderBoundV18207
open GoldbachCircleMethodCommonReflectionPointV18494

private theorem star_mul_eq_norm_sq (z : ℂ) :
    star z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, ← Complex.sq_norm]

/-- An arbitrary finite interval differs from its exact diagonal by at most
the already proved pairwise-period quartic endpoint budget. -/
theorem finiteCompanion_interval_energy_deviation_le
    {Q : ℕ} (r : PositiveLevel Q) (w : ℕ → ℂ)
    (hwReal : ∀ n : ℕ, star (w n) = w n)
    (A T : ℕ) (V : ℝ) (hV : 0 ≤ V)
    (hwBound : ∀ q : PositiveLevel Q,
      r.val * q.val ≤ Q ∧ Nat.Coprime r.val q.val →
        ‖w (r.val * q.val)‖ ≤ V) :
    ‖(∑ i ∈ Finset.range T,
        ((‖finiteCompanion r (A + i) w‖ ^ 2 : ℝ) : ℂ)) -
      (T : ℂ) * (∑ q : PositiveLevel Q,
        literalCoefficient r q w * literalCoefficient r q w *
          unitCharacterSum q.val 0)‖ ≤
      2 * (Q : ℝ) ^ 4 * V * V := by
  let Nstar := commonReflectionPoint Q A T
  have hend : A + T ≤ Nstar + 1 := by
    dsimp only [Nstar]
    exact (interval_le_commonReflectionPoint Q A T).trans (Nat.le_succ _)
  have h := actual_companion_interval_quartic_bound
    r r w w Nstar A T hend V V hV hV hwBound hwBound
  have hconv :
      (∑ i ∈ Finset.range T,
        finiteCompanion r (Nstar - (A + i)) w *
          finiteCompanion r (A + i) w) =
      ∑ i ∈ Finset.range T,
        ((‖finiteCompanion r (A + i) w‖ ^ 2 : ℝ) : ℂ) := by
    apply Finset.sum_congr rfl
    intro i hi
    have hiT : i < T := Finset.mem_range.mp hi
    have hn : A + i ≤ A + T := by omega
    rw [show Nstar = commonReflectionPoint Q A T by rfl]
    rw [finiteCompanion_reflectionPoint_sub_eq_star A T r w hwReal (A + i) hn]
    exact star_mul_eq_norm_sq (finiteCompanion r (A + i) w)
  have hzero (q : PositiveLevel Q) :
      (Nstar : ZMod q.val) = 0 := by
    apply (ZMod.natCast_eq_zero_iff Nstar q.val).mpr
    exact level_dvd_commonReflectionPoint Q A T q
  rw [hconv] at h
  simp_rw [hzero] at h
  exact h

end GoldbachCircleMethodCompanionIntervalEnergyDeviationV18495
