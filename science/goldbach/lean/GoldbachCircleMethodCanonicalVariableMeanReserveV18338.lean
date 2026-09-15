import GoldbachCircleMethodVariableMeanScalarReserveGateV18337
import GoldbachCircleMethodCanonicalBumpPrincipalFloorV18220

/-!
# Goldbach V1.8.338: canonical variable-mean reserve

This module inserts the existing canonical coupled-diagonal floor and the
variable unit-pair bracket floor into the exact scalar normal form from
V1.8.337.  The signed diagonal residual is retained as an explicit premise;
no sign is inferred for it.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodCanonicalVariableMeanReserveV18338

open GoldbachCircleMethodActualFrozenModelCompleteDiagonalV18213
open GoldbachCircleMethodActualUnitPairArithmeticV18194
open GoldbachCircleMethodActualUnitPairSignedResidualV18214
open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodCanonicalBumpPrincipalFloorV18220
open GoldbachCircleMethodExceptionalZeroGapAttestationRepairV18263
open GoldbachCircleMethodLogCutoffPresieveBindingV18120
open GoldbachCircleMethodPositivePrincipalDiagonalV18221
open GoldbachCircleMethodPrincipalWindowBoundaryV18121
open GoldbachCircleMethodPowerWeightAbelIntervalV18331
open GoldbachCircleMethodStructurallyAdmissibleActiveSlotV18258
open GoldbachCircleMethodVariableMeanScalarReserveGateV18337
open GoldbachCircleMethodVariableMeanUnitPairNormalFormV18335
open GoldbachCircleMethodVariableUnitPairBracketReserveV18336
open GoldbachCircleMethodZeroGapReserveScaleV18266

/-- The canonical arithmetic floors give an explicit lower bound for the
variable mean once, and only once, the signed diagonal residual is proved
nonnegative.  This theorem does not discharge that remaining sign gate. -/
theorem canonical_powerPairwiseVariableMean_re_lower
    {K B N : ℕ} [NeZero K] (rho : ℝ)
    {ExceptionalZeroAt :
      StructurallyAdmissibleActiveSlot ⌊((B : ℝ) ^ rho) ^ 2⌋₊ → ℝ → Prop}
    (d : ExceptionalZeroGapAttestation
      ⌊((B : ℝ) ^ rho) ^ 2⌋₊ ExceptionalZeroAt)
    (hR : 1 < (B : ℝ) ^ rho)
    (hK : ∀ q : PositiveLevel ⌊((B : ℝ) ^ rho) ^ 2⌋₊, q.val ∣ K)
    (A T : ℕ) (hEven : Even N) (hB : 4 ≤ B)
    (hleft : ∀ i ∈ Finset.range T, A + i ∈ blockCarrier B)
    (hright : ∀ i ∈ Finset.range T, N - (A + i) ∈ blockCarrier B)
    (hr3 : 3 < d.slot.val.1.val)
    (hResidual :
      0 ≤ (signedDiagonalResidual hK d.slot.val.1
        (logWeight ((B : ℝ) ^ rho) canonicalLogBump)
        (logWeight ((B : ℝ) ^ rho) canonicalLogBump)
        (N : ZMod K)).re) :
    ((d.slot.val.1.val : ℝ) /
          (d.slot.val.1.val.totient : ℝ) ^ 2) *
        ((2 - Real.exp (Real.pi ^ 2 / 24)) *
          (canonicalLogBump
            (Real.log (d.slot.val.1.val : ℝ) /
              Real.log ((B : ℝ) ^ rho))) ^ 2) *
        ((T : ℝ) *
          ((unitPairCount d.slot.val.1.val (N : ℤ) : ℝ) *
            zeroGapReserveScale d.zeroGap B / 6)) ≤
      (powerPairwiseVariableMean
        (log_cutoff_contains_one ((B : ℝ) ^ rho) hR)
        d.slot.val.1 d.slot.val.2
        (logWeight ((B : ℝ) ^ rho) canonicalLogBump)
        (logWeight ((B : ℝ) ^ rho) canonicalLogBump)
        d.zeroGap N A T).re := by
  let C : ℝ :=
    (2 - Real.exp (Real.pi ^ 2 / 24)) *
      (canonicalLogBump
        (Real.log (d.slot.val.1.val : ℝ) /
          Real.log ((B : ℝ) ^ rho))) ^ 2
  let D : ℝ :=
    (T : ℝ) *
      ((unitPairCount d.slot.val.1.val (N : ℤ) : ℝ) *
        zeroGapReserveScale d.zeroGap B / 6)
  have hC : C ≤
      (coupledDiagonal hK d.slot.val.1
        (logWeight ((B : ℝ) ^ rho) canonicalLogBump)
        (logWeight ((B : ℝ) ^ rho) canonicalLogBump)
        (N : ZMod K)).re := by
    exact actual_canonicalLogBump_coupled_floor
      ((B : ℝ) ^ rho) hR hK d.slot.val.1 hEven
  have hC0 : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg (le_of_lt two_sub_exp_pi_sq_div_twentyFour_pos)
      (sq_nonneg _)
  have hD : D ≤
      (variableUnitPairBracketSum d.slot.val.1.val N A T
        d.slot.val.2.val d.zeroGap).re := by
    exact variableUnitPairBracketSum_re_lower
      d N A T B hr3 hEven hB hleft hright
  have hD0 : 0 ≤ D := by
    dsimp [D]
    have hgap0 : 0 ≤ zeroGapReserveScale d.zeroGap B :=
      zeroGapReserveScale_nonneg d.zeroGap B (zeroGap_pos d).le (by omega)
    positivity
  simpa only [C, D] using
    powerPairwiseVariableMean_re_lower_of_scalar_floors
      (log_cutoff_contains_one ((B : ℝ) ^ rho) hR) hK
      d.slot.val.1 d.slot.val.2 d.slot.property.2
      (logWeight ((B : ℝ) ^ rho) canonicalLogBump)
      (logWeight ((B : ℝ) ^ rho) canonicalLogBump)
      d.zeroGap N A T C D hResidual hC0 hC hD0 hD

end GoldbachCircleMethodCanonicalVariableMeanReserveV18338
