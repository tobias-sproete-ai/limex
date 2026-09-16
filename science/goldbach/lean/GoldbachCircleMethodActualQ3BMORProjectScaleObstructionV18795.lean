import GoldbachCircleMethodActualQ3FullPsiSourceTransferV18794
import GoldbachCircleMethodActualQ3ScaleProjectAbsorptionV18766

/-!
# V1.8.795: source-strength obstruction for the absolute BMOR route

The conservative BMOR q=3 estimate has size `2*C*x/log x` after the two
reduced residue classes are combined.  The existing project normalization
charges a factor of order `log(x)^21` before division by the linear reserve.
The resulting literal absolute-value majorant is therefore
`2*C*log(x)^21/log(x)`, which is eventually `2*C*log(x)^20` and diverges.

This is a no-go theorem only for this absolute-majorant composition.  It is
not a lower bound for the actual signed correlation, not a counterexample to
Goldbach, and not a claim that a sharper source theorem or sign-sensitive
argument cannot close the gate.  `proof_status = NO_PROOF`.
-/

set_option autoImplicit false

open Filter Topology

namespace GoldbachCircleMethodActualQ3BMORProjectScaleObstructionV18795

/-- The dimensionless term obtained by inserting the literal `x/log x`
source envelope into the existing `log^21` absolute project composition. -/
noncomputable def bmorQ3AbsoluteProjectNormalizedMajorant
    (M : Nat) (C : Real) : Real :=
  2 * C * Real.log (M : Real) ^ 21 / Real.log (M : Real)

/-- Away from the single logarithmic zero, the normalized majorant is exactly
a positive constant times the twentieth power of the logarithm. -/
theorem bmorQ3AbsoluteProjectNormalizedMajorant_eq
    (M : Nat) (C : Real)
    (hlog : Real.log (M : Real) ≠ 0) :
    bmorQ3AbsoluteProjectNormalizedMajorant M C =
      2 * C * Real.log (M : Real) ^ 20 := by
  unfold bmorQ3AbsoluteProjectNormalizedMajorant
  field_simp

/-- Method-specific negative witness: for every positive source constant,
this literal absolute-value project majorant diverges rather than tending to
zero. -/
theorem bmorQ3AbsoluteProjectNormalizedMajorant_tendsto_atTop
    (C : Real) (hC : 0 < C) :
    Tendsto
      (fun M : Nat => bmorQ3AbsoluteProjectNormalizedMajorant M C)
      atTop atTop := by
  have hlog : Tendsto (fun M : Nat => Real.log (M : Real)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hpow : Tendsto
      (fun M : Nat => Real.log (M : Real) ^ 20) atTop atTop :=
    (tendsto_pow_atTop (by norm_num : (20 : Nat) ≠ 0)).comp hlog
  have hscaled : Tendsto
      (fun M : Nat => 2 * C * Real.log (M : Real) ^ 20) atTop atTop :=
    hpow.const_mul_atTop (mul_pos (by norm_num) hC)
  apply hscaled.congr'
  filter_upwards [eventually_gt_atTop (1 : Nat)] with M hM
  symm
  apply bmorQ3AbsoluteProjectNormalizedMajorant_eq
  exact Real.log_ne_zero_of_pos_of_ne_one (by positivity)
    (by exact_mod_cast hM.ne')

/-- In particular, the literal source-majorant composition eventually
exceeds every fixed reserve fraction. -/
theorem bmorQ3AbsoluteProjectNormalizedMajorant_eventually_gt
    (C T : Real) (hC : 0 < C) :
    ∀ᶠ M : Nat in atTop,
      T < bmorQ3AbsoluteProjectNormalizedMajorant M C :=
  (bmorQ3AbsoluteProjectNormalizedMajorant_tendsto_atTop C hC).eventually_gt_atTop T

/-- Specialization to the conservative published q=3 constant `1/840`.
Even this small positive constant cannot compensate for the twentieth
remaining logarithmic power in the absolute-value route. -/
theorem conservativeBMORQ3AbsoluteProjectMajorant_tendsto_atTop :
    Tendsto
      (fun M : Nat =>
        bmorQ3AbsoluteProjectNormalizedMajorant M (1 / 840))
      atTop atTop := by
  exact bmorQ3AbsoluteProjectNormalizedMajorant_tendsto_atTop
    (1 / 840) (by norm_num)

end GoldbachCircleMethodActualQ3BMORProjectScaleObstructionV18795
