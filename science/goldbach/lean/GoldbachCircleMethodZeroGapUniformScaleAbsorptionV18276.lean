import GoldbachCircleMethodSinglePeriodVariableWeightPositivityV18275
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Goldbach V1.8.276: zero-gap-uniform scale absorption

The V1.8.275 budget is split at `gap * log B = 1`.  Since the spatial error
contains the same zero-gap factor as the small-gap reserve, the gap cancels in
that regime.  A single conductor-to-block inequality suffices in both cases.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodZeroGapUniformScaleAbsorptionV18276

open GoldbachCircleMethodStructurallyAdmissibleActiveSlotV18258
open GoldbachCircleMethodExceptionalZeroGapAttestationRepairV18263
open GoldbachCircleMethodZeroGapReserveScaleV18266
open GoldbachCircleMethodVariableWeightIntervalDiscrepancyV18272
open GoldbachCircleMethodSinglePeriodVariableWeightPositivityV18275

/-- For `B >= 4`, the single scale inequality `48*r^2 < B` absorbs the
single-period variation cost for every gap in `(0,1)`.  This does not create a
gap-independent reserve: both the reserve and the small-gap error still tend
to zero, but their ratio is controlled uniformly. -/
theorem zero_gap_budget_of_conductor_square_lt_block
    (gap : ℝ) (r B : ℕ)
    (hgap0 : 0 < gap) (hgap1 : gap < 1) (hr0 : r ≠ 0) (hB : 4 ≤ B)
    (hscale : 48*(r : ℝ)^2 < (B : ℝ)) :
    48*gap*(r : ℝ)^2 <
      (B : ℝ) * zeroGapReserveScale gap B := by
  have hBreal : 0 < (B : ℝ) := by positivity
  have hexp : Real.exp 1 < (B : ℝ) := by
    have he := Real.exp_one_lt_d9
    have hfour : (2.9 : ℝ) < 4 := by norm_num
    have hcast : (4 : ℝ) ≤ (B : ℝ) := by exact_mod_cast hB
    linarith
  have hlog : 1 < Real.log (B : ℝ) :=
    (Real.lt_log_iff_exp_lt hBreal).2 hexp
  unfold zeroGapReserveScale
  by_cases hsmall : gap * Real.log B ≤ 1
  · rw [min_eq_right hsmall]
    have hscaled : 48*gap*(r : ℝ)^2 < gap*(B : ℝ) := by
      nlinarith
    have hlogscaled : gap*(B : ℝ) <
        (B : ℝ) * (gap * Real.log B) := by
      have hglog : gap < gap * Real.log B := by
        nlinarith [mul_lt_mul_of_pos_left hlog hgap0]
      calc
        gap * (B : ℝ) = (B : ℝ) * gap := by ring
        _ < (B : ℝ) * (gap * Real.log B) :=
          mul_lt_mul_of_pos_left hglog hBreal
    exact hscaled.trans hlogscaled
  · have hlarge : 1 < gap * Real.log B := lt_of_not_ge hsmall
    rw [min_eq_left hlarge.le]
    have hrpos : 0 < (r : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hr0
    have hfactor : 0 < 48*(r : ℝ)^2 := by positivity
    have hscaled : 48*gap*(r : ℝ)^2 < 48*(r : ℝ)^2 := by
      have := mul_lt_mul_of_pos_right hgap1 hfactor
      nlinarith
    nlinarith

/-- The actual variable-weight interval over one complete conductor period is
positive under the gap-free scale condition `48*r^2 < B`.  The proof still
uses the proof-carrying zero gap; only the *scale requirement* is uniform in
that gap. -/
theorem attested_variable_single_period_pos_of_uniform_scale
    {Q : ℕ}
    {ExceptionalZeroAt : StructurallyAdmissibleActiveSlot Q → ℝ → Prop}
    (d : ExceptionalZeroGapAttestation Q ExceptionalZeroAt)
    (N A B : ℕ)
    (hr3 : 3 < d.slot.val.1.val) (hEven : Even N)
    (hB : 4 ≤ B) (hAN : A ≤ N)
    (hend : A + d.slot.val.1.val ≤ N + 1)
    (hA : A ∈ GoldbachCircleMethodLogCutoffPresieveBindingV18120.blockCarrier B)
    (hNA : N-A ∈ GoldbachCircleMethodLogCutoffPresieveBindingV18120.blockCarrier B)
    (hleft : ∀ i ∈ Finset.range d.slot.val.1.val,
      A+i ∈ GoldbachCircleMethodLogCutoffPresieveBindingV18120.blockCarrier B)
    (hright : ∀ i ∈ Finset.range d.slot.val.1.val,
      N-(A+i) ∈ GoldbachCircleMethodLogCutoffPresieveBindingV18120.blockCarrier B)
    (hscale : 48*(d.slot.val.1.val : ℝ)^2 < (B : ℝ)) :
    0 < (variableUnitPairInterval d.slot.val.1.val N A d.slot.val.1.val
      d.slot.val.2.val d.zeroGap).re := by
  apply attested_variable_single_period_pos_of_budget d N A B
    hr3 hEven hB hAN hend hA hNA hleft hright
  exact zero_gap_budget_of_conductor_square_lt_block
    d.zeroGap d.slot.val.1.val B (zeroGap_pos d) (zeroGap_lt_one d)
      (by omega) hB hscale

end GoldbachCircleMethodZeroGapUniformScaleAbsorptionV18276
