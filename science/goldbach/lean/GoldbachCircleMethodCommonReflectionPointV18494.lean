import GoldbachCircleMethodCompleteCompanionEnergyRealV18493

/-!
# Goldbach V1.8.494: finite-companion reflection at a common multiple

This module supplies the exact natural-number reflection needed to turn an
incomplete interval convolution into a squared-energy sum.  The factorial
witness is used only as an algebraic common multiple; no bound depends on its
size.
-/

set_option autoImplicit false

open scoped BigOperators Classical ComplexConjugate

namespace GoldbachCircleMethodCommonReflectionPointV18494

open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodFiniteCompanionBindingV18118
open GoldbachCircleMethodFiniteResiduePrefixV1866
open GoldbachCircleMethodRealWeightCompanionReflectionV18491

/-- Reflection around a common multiple converts the original companion into
its complex conjugate, provided truncated subtraction is legitimate. -/
theorem finiteCompanion_commonMultiple_sub_eq_star
    {Q K : ℕ}
    (hK : ∀ l : PositiveLevel Q, l.val ∣ K)
    (r : PositiveLevel Q) (w : ℕ → ℂ)
    (hw : ∀ m : ℕ, star (w m) = w m)
    (n : ℕ) (hn : n ≤ K) :
    finiteCompanion r (K - n) w = star (finiteCompanion r n w) := by
  rw [star_finiteCompanion r n w hw]
  unfold finiteCompanion
  apply Finset.sum_congr rfl
  intro l _hl
  by_cases hsupport : r.val * l.val ≤ Q ∧ Nat.Coprime r.val l.val
  · rw [if_pos hsupport, if_pos hsupport]
    have hzero : (K : ZMod l.val) = 0 :=
      (ZMod.natCast_eq_zero_iff K l.val).mpr (hK l)
    rw [Nat.cast_sub hn, hzero, zero_sub]
  · simp [hsupport]

/-- A canonical reflection point for an interval `[A,A+T)`. -/
def commonReflectionPoint (Q A T : ℕ) : ℕ :=
  Q.factorial * (A + T + 1)

theorem level_dvd_commonReflectionPoint
    (Q A T : ℕ) (l : PositiveLevel Q) :
    l.val ∣ commonReflectionPoint Q A T := by
  unfold commonReflectionPoint
  exact dvd_mul_of_dvd_left
    (Nat.dvd_factorial (Nat.pos_of_ne_zero (NeZero.ne l.val))
      (Finset.mem_Icc.mp l.property).2) _

theorem interval_le_commonReflectionPoint (Q A T : ℕ) :
    A + T ≤ commonReflectionPoint Q A T := by
  unfold commonReflectionPoint
  have hfac : 1 ≤ Q.factorial := Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero Q)
  nlinarith

/-- Pointwise specialization on the canonical reflection point. -/
theorem finiteCompanion_reflectionPoint_sub_eq_star
    {Q : ℕ} (A T : ℕ)
    (r : PositiveLevel Q) (w : ℕ → ℂ)
    (hw : ∀ m : ℕ, star (w m) = w m)
    (n : ℕ) (hn : n ≤ A + T) :
    finiteCompanion r (commonReflectionPoint Q A T - n) w =
      star (finiteCompanion r n w) := by
  exact finiteCompanion_commonMultiple_sub_eq_star
    (level_dvd_commonReflectionPoint Q A T) r w hw n
    (hn.trans (interval_le_commonReflectionPoint Q A T))

end GoldbachCircleMethodCommonReflectionPointV18494
