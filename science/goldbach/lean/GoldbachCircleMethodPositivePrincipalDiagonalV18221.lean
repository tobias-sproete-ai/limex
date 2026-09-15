import GoldbachCircleMethodCanonicalBumpPrincipalFloorV18220
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# V1.8.221: strict positivity of the actual principal diagonal

V1.8.220 produced an exact lower floor for the real part of the literal
V1.8.213 principal diagonal.  This module verifies that the displayed floor
is strictly positive and hence closes positivity of that finite principal
component for the explicit canonical smooth weight.

No sign claim is made for the remaining nonprincipal or residual terms of the
complete frozen model.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodPositivePrincipalDiagonalV18221

open GoldbachCircleMethodFiniteResiduePrefixV1866
open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodLogCutoffPresieveBindingV18120
open GoldbachCircleMethodActualFrozenModelCompleteDiagonalV18213
open GoldbachCircleMethodCanonicalBumpPrincipalFloorV18220

/-- A deliberately coarse rational comparison is sufficient: `pi < 4`
places `pi^2/24` below `2/3`, while Mathlib's certified decimal bound places
`2/3` below `log 2`. -/
theorem pi_sq_div_twentyFour_lt_log_two :
    Real.pi ^ 2 / 24 < Real.log 2 := by
  have hpiSq : Real.pi ^ 2 < 16 := by
    nlinarith [Real.pi_pos, Real.pi_lt_four]
  have hfrac : Real.pi ^ 2 / 24 < (2 : ℝ) / 3 := by
    nlinarith
  have hdecimal : (2 : ℝ) / 3 < 0.6931471803 := by
    norm_num
  exact hfrac.trans (hdecimal.trans Real.log_two_gt_d9)

/-- The exact finite floor inherited from V1.8.38 is strictly positive. -/
theorem two_sub_exp_pi_sq_div_twentyFour_pos :
    0 < 2 - Real.exp (Real.pi ^ 2 / 24) := by
  have hexp : Real.exp (Real.pi ^ 2 / 24) < 2 := by
    calc
      Real.exp (Real.pi ^ 2 / 24) < Real.exp (Real.log 2) :=
        Real.exp_lt_exp.mpr pi_sq_div_twentyFour_lt_log_two
      _ = 2 := Real.exp_log (by norm_num)
  linarith

/-- Strict positivity of the real part of the actual finite principal
diagonal for every even target, with the explicit V1.8.220 smooth weight. -/
theorem actual_principalDiagonal_canonicalLogBump_pos
    {K N : ℕ} [NeZero K]
    (R : ℝ) (hR : 1 < R)
    (hK : ∀ q : PositiveLevel ⌊R ^ 2⌋₊, q.val ∣ K)
    (hEven : Even N) :
    0 <
      (principalDiagonal hK
        (logWeight R canonicalLogBump)
        (logWeight R canonicalLogBump) (N : ZMod K)).re :=
  two_sub_exp_pi_sq_div_twentyFour_pos.trans_le
    (actual_principalDiagonal_canonicalLogBump_floor R hR hK hEven)

end GoldbachCircleMethodPositivePrincipalDiagonalV18221

