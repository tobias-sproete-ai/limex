import GoldbachCircleMethodVariableUnitPairDeficitUpperV18342
import GoldbachCircleMethodPositivePrincipalDiagonalV18221

/-!
# V1.8.343: attested adjusted-model deficit absorption

The exact combined gate of V1.8.341 is specialized to a proof-carrying active
exceptional-zero record.  V1.8.342 supplies the unit-pair deficit upper bound,
and the existing canonical coupled-diagonal floor supplies the sign needed to
multiply that bound safely.

The sole remaining quantitative premise is displayed as a scalar budget in
terms of the explicit zero-gap loss.  It is not discharged here.  Thus this
module removes neither the zero-free analytic obligation nor the global
Goldbach obstruction.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodAttestedAdjustedDeficitAbsorptionV18343

open GoldbachCircleMethodActualFrozenModelCompleteDiagonalV18213
open GoldbachCircleMethodActualUnitPairArithmeticV18194
open GoldbachCircleMethodActiveExceptionalCenteringV18129
open GoldbachCircleMethodActiveResidualExactDecompositionV18251
open GoldbachCircleMethodBlockPairCarrierV18227
open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodCanonicalAdjustedDeficitAbsorptionV18341
open GoldbachCircleMethodCanonicalBumpPrincipalFloorV18220
open GoldbachCircleMethodExceptionalZeroGapAttestationRepairV18263
open GoldbachCircleMethodLogCutoffPresieveBindingV18120
open GoldbachCircleMethodPositivePrincipalDiagonalV18221
open GoldbachCircleMethodPrincipalWindowBoundaryV18121
open GoldbachCircleMethodResidualScaleAdmissionV18196
open GoldbachCircleMethodStructurallyAdmissibleActiveSlotV18258
open GoldbachCircleMethodVariableMeanCombinedReserveV18340
open GoldbachCircleMethodVariableUnitPairDeficitUpperV18342
open GoldbachCircleMethodZeroGapReserveScaleV18266

/-- The coupled diagonal used by an attested active slot is nonnegative for
the canonical logarithmic bump and every even target. -/
theorem attested_canonical_coupledDiagonal_re_nonneg
    {Q K N : ℕ} [NeZero K]
    {ExceptionalZeroAt : StructurallyAdmissibleActiveSlot Q → ℝ → Prop}
    (d : ExceptionalZeroGapAttestation Q ExceptionalZeroAt)
    (R : ℝ) (hR : 1 < R)
    (hK : ∀ q : PositiveLevel Q, q.val ∣ K)
    (hCutoff : Q = ⌊R ^ 2⌋₊) (hEven : Even N) :
    0 ≤ (coupledDiagonal hK d.slot.val.1
      (logWeight R canonicalLogBump)
      (logWeight R canonicalLogBump) (N : ZMod K)).re := by
  subst Q
  have hFloor := actual_canonicalLogBump_coupled_floor R hR hK
    d.slot.val.1 hEven
  have hKappa : 0 ≤ 2 - Real.exp (Real.pi ^ 2 / 24) :=
    (two_sub_exp_pi_sq_div_twentyFour_pos).le
  have hWeight : 0 ≤
      (canonicalLogBump
        (Real.log (d.slot.val.1.val : ℝ) / Real.log R)) ^ 2 := sq_nonneg _
  exact (mul_nonneg hKappa hWeight).trans hFloor

/-- Full composition of the pairwise `Q^4` boundary theorem with the existing
attested zero-gap unit-pair reserve.  The displayed budget is the exact
remaining scalar interface; no common LCM occurs. -/
theorem canonicalAdjustedModelAt_re_gt_of_attested_zeroGap_budget
    (B N : ℕ) (rho : ℝ)
    {ExceptionalZeroAt :
      StructurallyAdmissibleActiveSlot ⌊((B : ℝ) ^ rho) ^ 2⌋₊ → ℝ → Prop}
    (d : ExceptionalZeroGapAttestation ⌊((B : ℝ) ^ rho) ^ 2⌋₊ ExceptionalZeroAt)
    (K : ℕ) [NeZero K]
    (hK : ∀ q : PositiveLevel ⌊((B : ℝ) ^ rho) ^ 2⌋₊, q.val ∣ K)
    (hr3 : 3 < d.slot.val.1.val) (hEven : Even N)
    (hB4 : 4 ≤ B) (hB2 : 2 ≤ B) (hBN : B ≤ N)
    (hInterval : blockPairLower B N ≤ blockPairUpper B N)
    (hrho : 0 < rho) (hrhoUpper : rho ≤ (1 : ℝ) / 10000)
    (hScale : blockThreshold rho ≤ B)
    (hleft : ∀ i ∈ Finset.range
        (blockPairUpper B N - blockPairLower B N + 1),
      blockPairLower B N + i ∈ blockCarrier B)
    (hright : ∀ i ∈ Finset.range
        (blockPairUpper B N - blockPairLower B N + 1),
      N - (blockPairLower B N + i) ∈ blockCarrier B)
    (hBudget :
      ((d.slot.val.1.val : ℝ) /
          (d.slot.val.1.val.totient : ℝ) ^ 2) *
          (coupledDiagonal hK d.slot.val.1
            (logWeight ((B : ℝ) ^ rho) canonicalLogBump)
            (logWeight ((B : ℝ) ^ rho) canonicalLogBump)
            (N : ZMod K)).re *
          (((blockPairUpper B N - blockPairLower B N + 1 : ℕ) : ℝ) *
            (unitPairCount d.slot.val.1.val (N : ℤ) : ℝ) *
            (1 - zeroGapReserveScale d.zeroGap B / 6)) ≤
        ((blockPairUpper B N - blockPairLower B N + 1 : ℕ) : ℝ) *
            (principalDiagonal hK
              (logWeight ((B : ℝ) ^ rho) canonicalLogBump)
              (logWeight ((B : ℝ) ^ rho) canonicalLogBump)
              (N : ZMod K)).re -
          (B : ℝ) / 28) :
    (B : ℝ) / 56 <
      (canonicalAdjustedModelAt B rho d.zeroGap d.slot.val (N : ℤ)).re := by
  have hR : 1 < (B : ℝ) ^ rho :=
    one_lt_power_of_admitted rho hrho hrhoUpper B hScale
  have hCoupled0 : 0 ≤
      (coupledDiagonal hK d.slot.val.1
        (logWeight ((B : ℝ) ^ rho) canonicalLogBump)
        (logWeight ((B : ℝ) ^ rho) canonicalLogBump)
        (N : ZMod K)).re :=
    attested_canonical_coupledDiagonal_re_nonneg d ((B : ℝ) ^ rho) hR
      hK rfl hEven
  have hCoeff0 : 0 ≤
      ((d.slot.val.1.val : ℝ) /
          (d.slot.val.1.val.totient : ℝ) ^ 2) *
        (coupledDiagonal hK d.slot.val.1
          (logWeight ((B : ℝ) ^ rho) canonicalLogBump)
          (logWeight ((B : ℝ) ^ rho) canonicalLogBump)
          (N : ZMod K)).re := by
    positivity
  have hDeficitUpper := variableUnitPairDeficit_le_zeroGap_loss d N
    (blockPairLower B N)
    (blockPairUpper B N - blockPairLower B N + 1) B
    hr3 hEven hB4 hleft hright
  have hScaledDeficit := mul_le_mul_of_nonneg_left hDeficitUpper hCoeff0
  apply canonicalAdjustedModelAt_re_gt_of_deficit_absorbed B N rho d.zeroGap
    d.slot.val K hK (admissible_character_self_inverse d.slot)
    (zeroGap_nonneg d) (zeroGap_le_one d) hB2 hBN hInterval
    hrho hrhoUpper hScale
  exact hScaledDeficit.trans hBudget

end GoldbachCircleMethodAttestedAdjustedDeficitAbsorptionV18343
