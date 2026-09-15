import GoldbachCircleMethodFrozenUnitPairPeriodDecompositionV18273
import GoldbachCircleMethodAttestedUnitPairZeroGapReserveV18271

/-!
# Goldbach V1.8.274: attested variable-weight interval reserve

This is the first composition of the proof-carrying zero-gap residue reserve,
the actual spatial power-weight discrepancy, and the literal incomplete-period
terminal.  Every loss remains visible in the conclusion.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodAttestedVariableWeightIntervalReserveV18274

open GoldbachCircleMethodStructurallyAdmissibleActiveSlotV18258
open GoldbachCircleMethodExceptionalZeroGapAttestationRepairV18263
open GoldbachCircleMethodZeroGapReserveScaleV18266
open GoldbachCircleMethodExceptionalWeightBoundaryV18128
open GoldbachCircleMethodActualUnitPairArithmeticV18194
open GoldbachCircleMethodAttestedUnitPairZeroGapReserveV18271
open GoldbachCircleMethodVariableWeightIntervalDiscrepancyV18272
open GoldbachCircleMethodFrozenUnitPairPeriodDecompositionV18273

/-- The actual variable-weight interval inherits the complete-period reserve
after subtracting both costs that were previously kept separate:

* the literal terminal of length `T mod r`;
* the spatial freezing error `8 * gap * T^2 / B`.

No assertion is made that the right-hand side is positive. -/
theorem attested_variable_weight_interval_reserve_with_costs
    {Q : ℕ}
    {ExceptionalZeroAt : StructurallyAdmissibleActiveSlot Q → ℝ → Prop}
    (d : ExceptionalZeroGapAttestation Q ExceptionalZeroAt)
    (N A T B : ℕ)
    (hr3 : 3 < d.slot.val.1.val) (hEven : Even N)
    (hB : 4 ≤ B) (hAN : A ≤ N) (hend : A+T ≤ N+1)
    (hA : A ∈ GoldbachCircleMethodLogCutoffPresieveBindingV18120.blockCarrier B)
    (hNA : N-A ∈ GoldbachCircleMethodLogCutoffPresieveBindingV18120.blockCarrier B)
    (hleft : ∀ i ∈ Finset.range T,
      A+i ∈ GoldbachCircleMethodLogCutoffPresieveBindingV18120.blockCarrier B)
    (hright : ∀ i ∈ Finset.range T,
      N-(A+i) ∈ GoldbachCircleMethodLogCutoffPresieveBindingV18120.blockCarrier B) :
    ((T/d.slot.val.1.val : ℕ) : ℝ) *
          ((unitPairCount d.slot.val.1.val (N : ℤ) : ℝ) *
            zeroGapReserveScale d.zeroGap B / 6) -
        4*((T % d.slot.val.1.val : ℕ) : ℝ) -
        8*d.zeroGap*(T : ℝ)^2/(B : ℝ) ≤
      (variableUnitPairInterval d.slot.val.1.val N A T
        d.slot.val.2.val d.zeroGap).re := by
  let r := d.slot.val.1.val
  let chi := d.slot.val.2.val
  have hB2 : 2 ≤ B := by omega
  have hgap : 0 ≤ d.zeroGap := (zeroGap_pos d).le
  have hperiod :
      (unitPairCount r (N : ℤ) : ℝ) * zeroGapReserveScale d.zeroGap B / 6 ≤
        (frozenUnitPairPeriod r N A chi d.zeroGap).re := by
    simpa [r, chi, frozenUnitPairPeriod, powerWeight] using
      attested_actual_block_power_unit_pair_reserve d N B A (N-A)
        hr3 hEven hB hA hNA
  have hterminal := frozen_unit_pair_terminal_norm_le
    r N A T B chi d.zeroGap hgap hA hNA
  have hterminalRe :
      -(4*((T % r : ℕ) : ℝ)) ≤
        (frozenUnitPairTerminal r N A T chi d.zeroGap).re := by
    have habs := Complex.abs_re_le_norm
      (frozenUnitPairTerminal r N A T chi d.zeroGap)
    have hneg := neg_abs_le
      (frozenUnitPairTerminal r N A T chi d.zeroGap).re
    linarith
  have hdecomp := frozen_unit_pair_interval_period_decomposition
    r N A T chi d.zeroGap
  have hdecompRe := congrArg Complex.re hdecomp
  simp only [Complex.add_re, Complex.mul_re, Complex.natCast_re,
    Complex.natCast_im, zero_mul, sub_zero] at hdecompRe
  have hperiodScaled :
      ((T/r : ℕ) : ℝ) *
          ((unitPairCount r (N : ℤ) : ℝ) * zeroGapReserveScale d.zeroGap B / 6) ≤
        ((T/r : ℕ) : ℝ) * (frozenUnitPairPeriod r N A chi d.zeroGap).re :=
    mul_le_mul_of_nonneg_left hperiod (Nat.cast_nonneg _)
  have hfrozenLower :
      ((T/r : ℕ) : ℝ) *
          ((unitPairCount r (N : ℤ) : ℝ) * zeroGapReserveScale d.zeroGap B / 6) -
        4*((T % r : ℕ) : ℝ) ≤
      (frozenUnitPairInterval r N A T chi d.zeroGap).re := by
    linarith
  have hdisc := variable_unit_pair_interval_discrepancy
    r N A T B chi d.zeroGap hB2 hgap hAN hend hA hNA hleft hright
  have habsDiff := (Complex.abs_re_le_norm
    (variableUnitPairInterval r N A T chi d.zeroGap -
      frozenUnitPairInterval r N A T chi d.zeroGap)).trans hdisc
  have hdiffLower :
      -(8*d.zeroGap*(T : ℝ)^2/(B : ℝ)) ≤
        (variableUnitPairInterval r N A T chi d.zeroGap -
          frozenUnitPairInterval r N A T chi d.zeroGap).re := by
    have hneg := neg_le_abs
      (variableUnitPairInterval r N A T chi d.zeroGap -
        frozenUnitPairInterval r N A T chi d.zeroGap).re
    linarith
  dsimp only [r, chi] at *
  simp only [Complex.sub_re] at hdiffLower
  linarith

/-- If the interval length is an exact conductor multiple, only the spatial
variation cost remains. -/
theorem attested_variable_weight_full_periods_reserve
    {Q : ℕ}
    {ExceptionalZeroAt : StructurallyAdmissibleActiveSlot Q → ℝ → Prop}
    (d : ExceptionalZeroGapAttestation Q ExceptionalZeroAt)
    (N A T B : ℕ)
    (hr3 : 3 < d.slot.val.1.val) (hEven : Even N)
    (hB : 4 ≤ B) (hAN : A ≤ N) (hend : A+T ≤ N+1)
    (hT : d.slot.val.1.val ∣ T)
    (hA : A ∈ GoldbachCircleMethodLogCutoffPresieveBindingV18120.blockCarrier B)
    (hNA : N-A ∈ GoldbachCircleMethodLogCutoffPresieveBindingV18120.blockCarrier B)
    (hleft : ∀ i ∈ Finset.range T,
      A+i ∈ GoldbachCircleMethodLogCutoffPresieveBindingV18120.blockCarrier B)
    (hright : ∀ i ∈ Finset.range T,
      N-(A+i) ∈ GoldbachCircleMethodLogCutoffPresieveBindingV18120.blockCarrier B) :
    ((T/d.slot.val.1.val : ℕ) : ℝ) *
          ((unitPairCount d.slot.val.1.val (N : ℤ) : ℝ) *
            zeroGapReserveScale d.zeroGap B / 6) -
        8*d.zeroGap*(T : ℝ)^2/(B : ℝ) ≤
      (variableUnitPairInterval d.slot.val.1.val N A T
        d.slot.val.2.val d.zeroGap).re := by
  have h := attested_variable_weight_interval_reserve_with_costs d N A T B
    hr3 hEven hB hAN hend hA hNA hleft hright
  rw [Nat.mod_eq_zero_of_dvd hT] at h
  norm_num at h ⊢
  exact h

end GoldbachCircleMethodAttestedVariableWeightIntervalReserveV18274
