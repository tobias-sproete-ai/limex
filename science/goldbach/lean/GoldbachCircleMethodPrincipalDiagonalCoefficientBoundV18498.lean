import GoldbachCircleMethodPrincipalBlockCoefficientBoundV18497
import GoldbachCircleMethodActualPrincipalTwistCrossDiagonalV18210
import GoldbachCircleMethodRemovedConvolutionNormV18123

/-!
# Goldbach V1.8.498: principal diagonal coefficient bound

The literal conductor-one diagonal is bounded by the number of positive
levels when the retained scalar weight has norm at most one.  This is the
finite arithmetic input required by the sparse principal-block estimate;
no analytic cancellation is asserted here.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodPrincipalDiagonalCoefficientBoundV18498

open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodFiniteCompanionBindingV18118
open GoldbachCircleMethodLogCutoffPresieveBindingV18120
open GoldbachCircleMethodPrincipalWindowBoundaryV18121
open GoldbachCircleMethodActualCompanionCompleteDiagonalV18204
open GoldbachCircleMethodActualPrincipalTwistCrossDiagonalV18210
open GoldbachCircleMethodRemovedConvolutionNormV18123

/-- Every conductor-one diagonal summand costs at most one after the
Möbius/totient normalization. -/
theorem principal_diagonal_summand_le_one {Q : ℕ} (hQ : 1 ≤ Q)
    (w : ℕ → ℂ) (hw : ∀ n : ℕ, ‖w n‖ ≤ 1) (q : PositiveLevel Q) :
    ‖literalCoefficient (oneLevel hQ) q w‖ ^ 2 *
        (q.val.totient : ℝ) ≤ 1 := by
  rw [principal_literalCoefficient hQ]
  have hmu : ‖((ArithmeticFunction.moebius q.val : ℤ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_intCast]
    exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := q.val))
  have hphi : (1 : ℝ) ≤ q.val.totient := by
    exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q.val))
  have hphi_pos : 0 < (q.val.totient : ℝ) := lt_of_lt_of_le zero_lt_one hphi
  have hscalar :
      ‖((ArithmeticFunction.moebius q.val : ℤ) : ℂ) /
          (q.val.totient : ℂ)‖ ≤ 1 / (q.val.totient : ℝ) := by
    rw [norm_div, Complex.norm_natCast]
    exact div_le_div_of_nonneg_right hmu (le_of_lt hphi_pos)
  have hcoeff :
      ‖((ArithmeticFunction.moebius q.val : ℤ) : ℂ) /
          (q.val.totient : ℂ) * w q.val‖ ≤
        1 / (q.val.totient : ℝ) := by
    rw [norm_mul]
    calc
      _ ≤ (1 / (q.val.totient : ℝ)) * 1 :=
        mul_le_mul hscalar (hw q.val) (norm_nonneg _) (by positivity)
      _ = _ := by ring
  have hsq := pow_le_pow_left₀ (norm_nonneg _) hcoeff 2
  calc
    _ ≤ (1 / (q.val.totient : ℝ)) ^ 2 * (q.val.totient : ℝ) :=
      mul_le_mul_of_nonneg_right hsq (by positivity)
    _ = 1 / (q.val.totient : ℝ) := by
      field_simp [ne_of_gt hphi_pos]
    _ ≤ 1 := (div_le_one hphi_pos).mpr hphi

/-- The complete principal diagonal coefficient energy has linear cutoff
cost, not a full character-family cardinality. -/
theorem principal_diagonal_sum_le_cutoff (Q : ℕ) (hQ : 1 ≤ Q)
    (w : ℕ → ℂ) (hw : ∀ n : ℕ, ‖w n‖ ≤ 1) :
    (∑ q : PositiveLevel Q,
      ‖literalCoefficient (oneLevel hQ) q w‖ ^ 2 *
        (q.val.totient : ℝ)) ≤ (Q : ℝ) := by
  calc
    _ ≤ ∑ _q : PositiveLevel Q, (1 : ℝ) := by
      exact Finset.sum_le_sum (fun q _ => principal_diagonal_summand_le_one hQ w hw q)
    _ = (Q : ℝ) := by simp

end GoldbachCircleMethodPrincipalDiagonalCoefficientBoundV18498
