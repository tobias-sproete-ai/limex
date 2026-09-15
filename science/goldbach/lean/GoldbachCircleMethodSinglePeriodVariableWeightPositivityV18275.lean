import GoldbachCircleMethodAttestedVariableWeightIntervalReserveV18274
import GoldbachCircleMethodActualUnitPairPrimePowerV18197

/-!
# Goldbach V1.8.275: single-period variable-weight positivity gate

The explicit costs of V1.8.274 are absorbed on one literal conductor period.
The analytic price is not hidden: positivity requires the displayed
zero-gap-dependent budget inequality.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodSinglePeriodVariableWeightPositivityV18275

open GoldbachCircleMethodStructurallyAdmissibleActiveSlotV18258
open GoldbachCircleMethodExceptionalZeroGapAttestationRepairV18263
open GoldbachCircleMethodZeroGapReserveScaleV18266
open GoldbachCircleMethodActualUnitPairArithmeticV18194
open GoldbachCircleMethodActualUnitPairPrimePowerV18197
open GoldbachCircleMethodVariableWeightIntervalDiscrepancyV18272
open GoldbachCircleMethodAttestedVariableWeightIntervalReserveV18274

/-- On one complete conductor period the terminal vanishes.  The actual
variable-weight interval is strictly positive once its spatial variation cost
is smaller than the minimal one-unit-pair reserve.  The sufficient budget is
kept in multiplication form to avoid an untracked division by the block scale.
-/
theorem attested_variable_single_period_pos_of_budget
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
    (hbudget :
      48*d.zeroGap*(d.slot.val.1.val : ℝ)^2 <
        (B : ℝ) * zeroGapReserveScale d.zeroGap B) :
    0 < (variableUnitPairInterval d.slot.val.1.val N A d.slot.val.1.val
      d.slot.val.2.val d.zeroGap).re := by
  let r := d.slot.val.1.val
  have hr0 : r ≠ 0 := by omega
  have hBreal : 0 < (B : ℝ) := by positivity
  have htheta : 0 < zeroGapReserveScale d.zeroGap B :=
    attestedZeroGapReserveScale_pos d B (by omega)
  have hcountNat :
      0 < @unitPairCount r ⟨hr0⟩ (N : ℤ) :=
    unitPairCount_pos_of_even r N hr0 hEven
  have hcount :
      (1 : ℝ) ≤ (@unitPairCount r ⟨hr0⟩ (N : ℤ) : ℝ) := by
    exact_mod_cast hcountNat
  have hcost :
      8*d.zeroGap*(r : ℝ)^2/(B : ℝ) <
        zeroGapReserveScale d.zeroGap B / 6 := by
    apply (div_lt_iff₀ hBreal).2
    dsimp only [r] at hbudget ⊢
    nlinarith
  have hreserve := attested_variable_weight_full_periods_reserve
    d N A r B hr3 hEven hB hAN hend (dvd_refl r) hA hNA hleft hright
  have hmain :
      zeroGapReserveScale d.zeroGap B / 6 ≤
        (@unitPairCount r ⟨hr0⟩ (N : ℤ) : ℝ) *
          zeroGapReserveScale d.zeroGap B / 6 := by
    have hmul := mul_le_mul_of_nonneg_right hcount htheta.le
    nlinarith
  dsimp only [r] at hreserve ⊢
  rw [Nat.div_self (by omega : 0 < r)] at hreserve
  norm_num at hreserve
  linarith

end GoldbachCircleMethodSinglePeriodVariableWeightPositivityV18275
