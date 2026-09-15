import GoldbachCircleMethodActualQ3PairFourierFactorizationV18743

/-!
# V1.8.744: exact two-mode q=3 spectral budget

V1.8.743 reduces the complete raw q=3 pair transform to one-variable
odd-Lambda Fourier modes.  Since the only units modulo three are `1` and `2`,
this append-only successor enumerates the finite unit sum and proves a sharp
two-mode square-norm majorant.  The majorant is sign-sensitive at the source:
it measures only nonzero additive Fourier modes, not total Lambda mass.

No estimate for either arithmetic mode is imported or asserted.  No
incomplete-prefix, minor-arc, exceptional-set, or Goldbach conclusion is
proved.  `proof_status = NO_PROOF`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

open scoped BigOperators Classical ArithmeticFunction.vonMangoldt

namespace GoldbachCircleMethodActualQ3UnitModeSquareBudgetV18744

open GoldbachCircleMethodActualQ3PairFourierFactorizationV18743
open GoldbachCircleMethodActualQ3WeightedFiberPullbackV18742

/-- Exact enumeration of the two unit frequencies modulo three. -/
theorem actualQ3RawPairTransform_eq_two_unit_modes (M n : Nat) :
    actualQ3RawPairTransform M n =
      ZMod.stdAddChar
          (((-2 * (n : Int) : Int) : ZMod 3) * (1 : ZMod 3)) *
        (oddLambdaQ3Mode M (1 : ZMod 3)) ^ 2 +
      ZMod.stdAddChar
          (((-2 * (n : Int) : Int) : ZMod 3) * (2 : ZMod 3)) *
        (oddLambdaQ3Mode M (2 : ZMod 3)) ^ 2 := by
  rw [actualQ3RawPairTransform_eq_sum_unit_modeSquares]
  have huniv : (Finset.univ : Finset (ZMod 3)) = {0, 1, 2} := by decide
  rw [huniv]
  have h01 : (0 : ZMod 3) ∉ ({1, 2} : Finset (ZMod 3)) := by decide
  have h12 : (1 : ZMod 3) ∉ ({2} : Finset (ZMod 3)) := by decide
  rw [Finset.sum_insert h01, Finset.sum_insert h12,
    Finset.sum_singleton]
  simp only [show ¬ IsUnit (0 : ZMod 3) by decide, if_false,
    show IsUnit (1 : ZMod 3) by decide, if_true,
    show IsUnit (2 : ZMod 3) by decide, zero_add]

/-- The source-bound spectral budget for the complete q=3 endpoint. -/
noncomputable def actualQ3UnitModeSquareBudget (M : Nat) : Real :=
  ‖oddLambdaQ3Mode M (1 : ZMod 3)‖ ^ 2 +
    ‖oddLambdaQ3Mode M (2 : ZMod 3)‖ ^ 2

theorem actualQ3UnitModeSquareBudget_nonneg (M : Nat) :
    0 ≤ actualQ3UnitModeSquareBudget M := by
  unfold actualQ3UnitModeSquareBudget
  positivity

/-- Each additive character phase has unit norm. -/
theorem norm_q3_targetPhase_eq_one (n : Nat) (xi : ZMod 3) :
    ‖ZMod.stdAddChar
        (((-2 * (n : Int) : Int) : ZMod 3) * xi)‖ = 1 := by
  simp

/-- The complete raw pair transform is controlled by precisely the two
nonzero q=3 arithmetic mode squares. -/
theorem actualQ3RawPairTransform_norm_le_unitModeSquareBudget (M n : Nat) :
    ‖actualQ3RawPairTransform M n‖ ≤ actualQ3UnitModeSquareBudget M := by
  rw [actualQ3RawPairTransform_eq_two_unit_modes]
  unfold actualQ3UnitModeSquareBudget
  calc
    _ ≤ ‖ZMod.stdAddChar
          (((-2 * (n : Int) : Int) : ZMod 3) * (1 : ZMod 3)) *
            (oddLambdaQ3Mode M (1 : ZMod 3)) ^ 2‖ +
        ‖ZMod.stdAddChar
          (((-2 * (n : Int) : Int) : ZMod 3) * (2 : ZMod 3)) *
            (oddLambdaQ3Mode M (2 : ZMod 3)) ^ 2‖ := norm_add_le _ _
    _ = ‖oddLambdaQ3Mode M (1 : ZMod 3)‖ ^ 2 +
        ‖oddLambdaQ3Mode M (2 : ZMod 3)‖ ^ 2 := by
      simp only [norm_mul, norm_pow, norm_q3_targetPhase_eq_one, one_mul]

end GoldbachCircleMethodActualQ3UnitModeSquareBudgetV18744
