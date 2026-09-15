import GoldbachCircleMethodVariableMeanCombinedReserveV18340

/-!
# V1.8.341: canonical adjusted-model deficit absorption

The pairwise Abel theorem V1.8.333 places the actual canonical adjusted model
within `B/56` of its variable arithmetic mean.  V1.8.340 identifies the exact
remaining arithmetic loss in that mean.  This module composes the two facts:
if the weighted unit-pair deficit fits inside the principal budget above
`B/28`, then the actual adjusted model has real part strictly above `B/56`.

The deficit inequality remains an explicit premise.  No analytic estimate of
it and no Goldbach conclusion is asserted.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodCanonicalAdjustedDeficitAbsorptionV18341

open GoldbachCircleMethodActiveExceptionalCenteringV18129
open GoldbachCircleMethodActiveResidualExactDecompositionV18251
open GoldbachCircleMethodActualFrozenModelCompleteDiagonalV18213
open GoldbachCircleMethodActualUnitPairArithmeticV18194
open GoldbachCircleMethodAdmittedCanonicalAbelAbsorptionV18333
open GoldbachCircleMethodBlockPairCarrierV18227
open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodCanonicalBumpPrincipalFloorV18220
open GoldbachCircleMethodLogCutoffPresieveBindingV18120
open GoldbachCircleMethodPowerWeightAbelIntervalV18331
open GoldbachCircleMethodPrincipalWindowBoundaryV18121
open GoldbachCircleMethodResidualScaleAdmissionV18196
open GoldbachCircleMethodVariableMeanCombinedReserveV18340

/-- A norm-close complex quantity inherits the real lower reserve of its
reference quantity, minus the norm error. -/
theorem real_part_gt_of_sub_norm_lt
    {z mean : ℂ} {L eps : ℝ}
    (hMean : L ≤ mean.re) (hClose : ‖z - mean‖ < eps) :
    L - eps < z.re := by
  have hAbsLe : |(z - mean).re| ≤ ‖z - mean‖ :=
    Complex.abs_re_le_norm (z - mean)
  have hAbsLt : |(z - mean).re| < eps := hAbsLe.trans_lt hClose
  have hNeg : -|(z - mean).re| ≤ (z - mean).re := neg_abs_le _
  simp only [Complex.sub_re] at hAbsLt hNeg
  linarith

/-- Canonical composition of the exact deficit gate with the pairwise `Q^4`
boundary absorption.  This is a conditional reserve theorem with one visible
arithmetic premise, not a discharge of that premise. -/
theorem canonicalAdjustedModelAt_re_gt_of_deficit_absorbed
    (B N : ℕ) (rho b : ℝ)
    (e : CharacterSlot ⌊((B : ℝ) ^ rho) ^ 2⌋₊)
    (K : ℕ) [NeZero K]
    (hK : ∀ q : PositiveLevel ⌊((B : ℝ) ^ rho) ^ 2⌋₊, q.val ∣ K)
    (hInv : e.2.val⁻¹ = e.2.val)
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (hB2 : 2 ≤ B) (hBN : B ≤ N)
    (hInterval : blockPairLower B N ≤ blockPairUpper B N)
    (hrho : 0 < rho) (hrhoUpper : rho ≤ (1 : ℝ) / 10000)
    (hScale : blockThreshold rho ≤ B)
    (hDeficit :
      ((e.1.val : ℝ) / (e.1.val.totient : ℝ) ^ 2) *
          (coupledDiagonal hK e.1
            (logWeight ((B : ℝ) ^ rho) canonicalLogBump)
            (logWeight ((B : ℝ) ^ rho) canonicalLogBump)
            (N : ZMod K)).re *
          variableUnitPairDeficit e.1.val N (blockPairLower B N)
            (blockPairUpper B N - blockPairLower B N + 1) e.2.val b ≤
        ((blockPairUpper B N - blockPairLower B N + 1 : ℕ) : ℝ) *
            (principalDiagonal hK
              (logWeight ((B : ℝ) ^ rho) canonicalLogBump)
              (logWeight ((B : ℝ) ^ rho) canonicalLogBump)
              (N : ZMod K)).re -
          (B : ℝ) / 28) :
    (B : ℝ) / 56 <
      (canonicalAdjustedModelAt B rho b e (N : ℤ)).re := by
  let hQ : 1 ≤ ⌊((B : ℝ) ^ rho) ^ 2⌋₊ :=
    log_cutoff_contains_one ((B : ℝ) ^ rho)
      (one_lt_power_of_admitted rho hrho hrhoUpper B hScale)
  let A := blockPairLower B N
  let T := blockPairUpper B N - blockPairLower B N + 1
  let mean : ℂ :=
    powerPairwiseVariableMean hQ e.1 e.2
      (logWeight ((B : ℝ) ^ rho) canonicalLogBump)
      (logWeight ((B : ℝ) ^ rho) canonicalLogBump)
      b N A T
  have hMean : (B : ℝ) / 28 ≤ mean.re := by
    apply (powerPairwiseVariableMean_re_ge_iff_deficit_absorbed
      hQ hK e.1 e.2 hInv
      (logWeight ((B : ℝ) ^ rho) canonicalLogBump)
      (logWeight ((B : ℝ) ^ rho) canonicalLogBump)
      b N A T ((B : ℝ) / 28)).2
    simpa only [A, T] using hDeficit
  have hClose :
      ‖canonicalAdjustedModelAt B rho b e (N : ℤ) - mean‖ <
        (B : ℝ) / 56 := by
    simpa only [mean, A, T, hQ] using
      canonicalAdjustedModelAt_sub_variableMean_norm_lt_half_reserve
        B N rho b e hInv hb0 hb1 hB2 hBN hInterval
        hrho hrhoUpper hScale
  have hTransfer := real_part_gt_of_sub_norm_lt hMean hClose
  have hArith : (B : ℝ) / 28 - (B : ℝ) / 56 = (B : ℝ) / 56 := by
    ring
  rwa [hArith] at hTransfer

end GoldbachCircleMethodCanonicalAdjustedDeficitAbsorptionV18341
