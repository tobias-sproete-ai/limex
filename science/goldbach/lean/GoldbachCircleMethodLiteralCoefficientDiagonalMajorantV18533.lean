import GoldbachCircleMethodCanonicalUniformSharpSourceCapV18532

/-!
# Goldbach V1.8.533: support-preserving literal-coefficient majorant

The literal companion coefficient is bounded without discarding its coupled
support `r*q <= Q` or the coprimality gate.  On the active carrier, the exact
totient weight in the complete-period diagonal cancels one denominator and
leaves `V^2 / phi(q)`.  Off the carrier, both sides are definitionally zero.

This closes only the coefficient-normalization step.  It does not estimate the
remaining coupled conductor sum or the pairwise-period endpoint remainder.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodLiteralCoefficientDiagonalMajorantV18533

open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodActualCompanionCompleteDiagonalV18204

/-- The exact support-preserving real majorant for one literal diagonal term. -/
noncomputable def literalCoefficientDiagonalMajorant {Q : ℕ}
    (r q : PositiveLevel Q) (V : ℝ) : ℝ :=
  if r.val * q.val ≤ Q ∧ Nat.Coprime r.val q.val then
    V ^ 2 / (q.val.totient : ℝ)
  else 0

/-- On the active carrier, one literal coefficient retains the full reciprocal
totient denominator. -/
theorem literalCoefficient_norm_le_div_totient
    {Q : ℕ} (r q : PositiveLevel Q) (w : ℕ → ℂ)
    (V : ℝ)
    (hwBound : r.val * q.val ≤ Q ∧ Nat.Coprime r.val q.val →
      ‖w (r.val * q.val)‖ ≤ V) :
    ‖literalCoefficient r q w‖ ≤
      if r.val * q.val ≤ Q ∧ Nat.Coprime r.val q.val then
        V / (q.val.totient : ℝ)
      else 0 := by
  by_cases hactive : r.val * q.val ≤ Q ∧ Nat.Coprime r.val q.val
  · rw [if_pos hactive]
    unfold literalCoefficient
    rw [if_pos hactive, norm_mul, norm_div, Complex.norm_natCast]
    have hmu : ‖((ArithmeticFunction.moebius q.val : ℤ) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_intCast]
      exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := q.val))
    have hphi : 0 < (q.val.totient : ℝ) := by
      exact_mod_cast Nat.totient_pos.mpr
        (Nat.pos_of_ne_zero (NeZero.ne q.val))
    have hdiv :
        ‖((ArithmeticFunction.moebius q.val : ℤ) : ℂ)‖ /
            (q.val.totient : ℝ) ≤
          1 / (q.val.totient : ℝ) := by
      exact div_le_div_of_nonneg_right hmu hphi.le
    calc
      _ ≤ (1 / (q.val.totient : ℝ)) * V :=
        mul_le_mul hdiv (hwBound hactive) (norm_nonneg _) (by positivity)
      _ = V / (q.val.totient : ℝ) := by ring
  · simp [literalCoefficient, hactive]

/-- Multiplication by the Parseval totient weight leaves exactly one reciprocal
totient in the support-preserving majorant. -/
theorem literalCoefficient_sq_mul_totient_le_majorant
    {Q : ℕ} (r q : PositiveLevel Q) (w : ℕ → ℂ)
    (V : ℝ)
    (hwBound : r.val * q.val ≤ Q ∧ Nat.Coprime r.val q.val →
      ‖w (r.val * q.val)‖ ≤ V) :
    ‖literalCoefficient r q w‖ ^ 2 * (q.val.totient : ℝ) ≤
      literalCoefficientDiagonalMajorant r q V := by
  by_cases hactive : r.val * q.val ≤ Q ∧ Nat.Coprime r.val q.val
  · have hphi : 0 < (q.val.totient : ℝ) := by
      exact_mod_cast Nat.totient_pos.mpr
        (Nat.pos_of_ne_zero (NeZero.ne q.val))
    have hnorm : ‖literalCoefficient r q w‖ ≤
        V / (q.val.totient : ℝ) := by
      have hraw :=
        literalCoefficient_norm_le_div_totient r q w V hwBound
      rw [if_pos hactive] at hraw
      exact hraw
    have hsq : ‖literalCoefficient r q w‖ ^ 2 ≤
        (V / (q.val.totient : ℝ)) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    unfold literalCoefficientDiagonalMajorant
    rw [if_pos hactive]
    calc
      _ ≤ (V / (q.val.totient : ℝ)) ^ 2 *
          (q.val.totient : ℝ) :=
        mul_le_mul_of_nonneg_right hsq hphi.le
      _ = V ^ 2 / (q.val.totient : ℝ) := by
        field_simp [ne_of_gt hphi]
  · simp [literalCoefficient, literalCoefficientDiagonalMajorant, hactive]

/-- The entire literal diagonal sum is bounded termwise while retaining the
actual coupled support. -/
theorem literalCoefficient_diagonal_sum_le_majorant_sum
    {Q : ℕ} (r : PositiveLevel Q) (w : ℕ → ℂ)
    (V : ℝ)
    (hwBound : ∀ q : PositiveLevel Q,
      r.val * q.val ≤ Q ∧ Nat.Coprime r.val q.val →
        ‖w (r.val * q.val)‖ ≤ V) :
    (∑ q : PositiveLevel Q,
      ‖literalCoefficient r q w‖ ^ 2 * (q.val.totient : ℝ)) ≤
      ∑ q : PositiveLevel Q, literalCoefficientDiagonalMajorant r q V := by
  exact Finset.sum_le_sum
    (fun q _hq => literalCoefficient_sq_mul_totient_le_majorant
      r q w V (hwBound q))

end GoldbachCircleMethodLiteralCoefficientDiagonalMajorantV18533
