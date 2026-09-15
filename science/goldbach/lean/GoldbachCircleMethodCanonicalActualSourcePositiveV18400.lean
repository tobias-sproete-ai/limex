import GoldbachCircleMethodCanonicalSourceMeanPositiveV18399
import GoldbachCircleMethodAdmittedCanonicalAbelAbsorptionV18333

/-!
# Goldbach V1.8.400: canonical actual-source aggregate positivity

The complete-period source mean of V1.8.399 is re-attached to the literal
incomplete adjusted block convolution.  The principal aggregate is first
given a stronger explicit rational reserve.  Two independent pairwise-period
`Q^4` budgets are then paid: the source-variable arithmetic correction and
the interval-to-mean boundary cost.  A strictly positive real aggregate
remains over the canonical even-target sweep.

This is an aggregate theorem for one structurally admissible active slot.  It
does not imply positivity at any individual target, does not identify the
adjusted model with the von-Mangoldt source, and does not prove Goldbach.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodCanonicalActualSourcePositiveV18400

open GoldbachCircleMethodActiveExceptionalCenteringV18129
open GoldbachCircleMethodActiveResidualExactDecompositionV18251
open GoldbachCircleMethodActualFrozenModelCompleteDiagonalV18213
open GoldbachCircleMethodAdmittedCanonicalAbelAbsorptionV18333
open GoldbachCircleMethodAdmittedSourceVariableCorrectionBudgetV18397
open GoldbachCircleMethodBlockPairCarrierV18227
open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodCanonicalBumpPrincipalFloorV18220
open GoldbachCircleMethodCanonicalSourceMeanPositiveV18399
open GoldbachCircleMethodCanonicalTargetWeightPiecewiseGeometryV18368
open GoldbachCircleMethodLogCutoffPresieveBindingV18120
open GoldbachCircleMethodPositivePrincipalDiagonalV18221
open GoldbachCircleMethodPowerWeightAbelIntervalV18331
open GoldbachCircleMethodPrincipalWindowBoundaryV18121
open GoldbachCircleMethodSourceRealCorrectionBindingV18398
open GoldbachCircleMethodSourceBoundVariableCoupledCorrectionV18396
open GoldbachCircleMethodStructurallyAdmissibleActiveSlotV18258

/-- A rational reserve strong enough to pay both later `Q^4` budgets. -/
theorem one_third_lt_principal_floor :
    (1 : ℝ) / 3 < 2 - Real.exp (Real.pi ^ 2 / 24) := by
  have hpiSq : Real.pi ^ 2 < ((63 : ℝ) / 20) ^ 2 := by
    nlinarith [Real.pi_pos, Real.pi_lt_d2]
  have harg : Real.pi ^ 2 / 24 < (1 : ℝ) / 2 := by
    nlinarith
  have hexpMono :
      Real.exp (Real.pi ^ 2 / 24) < Real.exp ((1 : ℝ) / 2) :=
    Real.exp_lt_exp.mpr harg
  have hexpHalf := Real.exp_bound'
    (x := (1 : ℝ) / 2) (by norm_num) (by norm_num)
    (n := 3) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at hexpHalf
  nlinarith

/-- The principal target aggregate exceeds `B^2/24`, with `B = 4m`. -/
theorem canonical_principal_target_sum_gt_twenty_fourth_budget
    {K : ℕ} [NeZero K] (m : ℕ) (hm : 1 ≤ m)
    (rho : ℝ) (hR : 1 < ((4 * m : ℕ) : ℝ) ^ rho)
    (hK : ∀ q : PositiveLevel ⌊(((4 * m : ℕ) : ℝ) ^ rho) ^ 2⌋₊,
      q.val ∣ K) :
    ((4 * m : ℕ) : ℝ) ^ 2 / 24 <
      canonicalPrincipalRealTargetSum hK
        (logWeight (((4 * m : ℕ) : ℝ) ^ rho) canonicalLogBump)
        (logWeight (((4 * m : ℕ) : ℝ) ^ rho) canonicalLogBump) m := by
  let kappa : ℝ := 2 - Real.exp (Real.pi ^ 2 / 24)
  let wt : ℕ → ℂ :=
    logWeight (((4 * m : ℕ) : ℝ) ^ rho) canonicalLogBump
  have hterm (i : ℕ) (hi : i ∈ Finset.range (2 * m)) :
      kappa *
          (canonicalPairMultiplicity (4 * m) (4 * m + 2 + 2 * i) : ℝ) ≤
        (canonicalPairMultiplicity (4 * m) (4 * m + 2 + 2 * i) : ℝ) *
          (principalDiagonal hK wt wt
            ((4 * m + 2 + 2 * i : ℕ) : ZMod K)).re := by
    have hEven : Even (4 * m + 2 + 2 * i) := by
      exact ⟨2 * m + 1 + i, by omega⟩
    have hfloor := actual_principalDiagonal_canonicalLogBump_floor
      (((4 * m : ℕ) : ℝ) ^ rho) hR hK hEven
    have hmul := mul_le_mul_of_nonneg_left hfloor
      (Nat.cast_nonneg
        (canonicalPairMultiplicity (4 * m) (4 * m + 2 + 2 * i)))
    simpa only [kappa, wt, mul_comm] using hmul
  have hsum :
      kappa *
          (∑ i ∈ Finset.range (2 * m),
            (canonicalPairMultiplicity (4 * m) (4 * m + 2 + 2 * i) : ℝ)) ≤
        canonicalPrincipalRealTargetSum hK wt wt m := by
    unfold canonicalPrincipalRealTargetSum
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum hterm
  have hmassNat := canonical_even_target_pair_multiplicity_sum m hm
  have hmassReal :
      (∑ i ∈ Finset.range (2 * m),
        (canonicalPairMultiplicity (4 * m) (4 * m + 2 + 2 * i) : ℝ)) =
          2 * (m : ℝ) ^ 2 := by
    exact_mod_cast hmassNat
  rw [hmassReal] at hsum
  have hkappa : (1 : ℝ) / 3 < kappa := one_third_lt_principal_floor
  have hmpos : 0 < (m : ℝ) := by
    exact_mod_cast (Nat.zero_lt_of_lt hm)
  have hstrict :
      ((4 * m : ℕ) : ℝ) ^ 2 / 24 < kappa * (2 * (m : ℝ) ^ 2) := by
    push_cast
    nlinarith [sq_pos_of_pos hmpos]
  exact hstrict.trans_le hsum

/-- Quantitative strengthening of V1.8.399: after the variable arithmetic
correction, the complete-period source mean retains more than `B^2/42`. -/
theorem admitted_canonical_source_variable_mean_gt_one_forty_second
    {K : ℕ} [NeZero K]
    (m : ℕ) (hm : 1 ≤ m) (rho b : ℝ)
    (e : StructurallyAdmissibleActiveSlot
      ⌊(((4 * m : ℕ) : ℝ) ^ rho) ^ 2⌋₊)
    (hK : ∀ q : PositiveLevel ⌊(((4 * m : ℕ) : ℝ) ^ rho) ^ 2⌋₊,
      q.val ∣ K)
    (hrho : 0 < rho) (hrhoUpper : rho ≤ (1 : ℝ) / 10000)
    (hScale : GoldbachCircleMethodResidualScaleAdmissionV18196.blockThreshold rho ≤ 4 * m)
    (hb : 0 ≤ b) (hb1 : b ≤ 1)
    (hR : 1 < ((4 * m : ℕ) : ℝ) ^ rho) :
    ((4 * m : ℕ) : ℝ) ^ 2 / 42 <
      canonicalSourceVariableMeanTargetSum
        (log_cutoff_contains_one (((4 * m : ℕ) : ℝ) ^ rho) hR)
        hK e
        (logWeight (((4 * m : ℕ) : ℝ) ^ rho) canonicalLogBump)
        (logWeight (((4 * m : ℕ) : ℝ) ^ rho) canonicalLogBump)
        m b := by
  let wt : ℕ → ℂ :=
    logWeight (((4 * m : ℕ) : ℝ) ^ rho) canonicalLogBump
  have hprincipal := canonical_principal_target_sum_gt_twenty_fourth_budget
    m hm rho hR hK
  have hAeven : Even (4 * m + 2) := ⟨2 * m + 1, by omega⟩
  have hcorrNorm := admitted_source_variable_correction_norm_lt_quadratic_budget
    (B := 4 * m) (A := 4 * m + 2) (Kgrow := m) (S := m)
    (rho := rho) (b := b) e K hK hrho hrhoUpper hScale hb hb1
      hAeven (by omega) (by omega) (by omega) hm
      (by simp [blockPairTurningTarget]; omega) hm
      (by simp [blockPairTurningTarget]; omega) (by omega)
  have hcorrRe :
      ‖(sourceNormalizedActualVariableCorrectionTargetSum hK e wt wt
        (4 * m) (4 * m + 2) (2 * m) b).re‖ <
          ((4 * m : ℕ) : ℝ) ^ 2 / 56 := by
    exact (Complex.abs_re_le_norm _).trans_lt
      (by simpa only [wt, two_mul] using hcorrNorm)
  have hcorrLower :
      -(((4 * m : ℕ) : ℝ) ^ 2 / 56) <
        sourceRealActualVariableCorrectionTargetSum hK e wt wt
          (4 * m) (4 * m + 2) (2 * m) b := by
    have hre := sourceNormalizedActualVariableCorrectionTargetSum_re_eq_sourceReal
      hK e (((4 * m : ℕ) : ℝ) ^ rho) (4 * m) (4 * m + 2) (2 * m) b
    rw [← hre]
    exact (abs_lt.mp hcorrRe).1
  rw [canonical_source_variable_mean_eq_principal_add_correction]
  dsimp only [wt] at hcorrLower
  nlinarith

/-- Literal real aggregate of the incomplete adjusted block convolutions over
the same canonical even-target sweep. -/
noncomputable def canonicalAdjustedSourceTargetSum
    (m : ℕ) (rho b : ℝ)
    (e : StructurallyAdmissibleActiveSlot
      ⌊(((4 * m : ℕ) : ℝ) ^ rho) ^ 2⌋₊) : ℝ :=
  ∑ i ∈ Finset.range (2 * m),
    (canonicalAdjustedModelAt (4 * m) rho b e.val
      ((4 * m + 2 + 2 * i : ℕ) : ℤ)).re

/-- The total interval-to-mean boundary cost over all `2m` targets is at most
`B^2/112`; no common LCM is introduced. -/
theorem canonical_adjusted_source_target_sum_sub_mean_abs_le_boundary
    {K : ℕ} [NeZero K]
    (m : ℕ) (hm : 1 ≤ m) (rho b : ℝ)
    (e : StructurallyAdmissibleActiveSlot
      ⌊(((4 * m : ℕ) : ℝ) ^ rho) ^ 2⌋₊)
    (hK : ∀ q : PositiveLevel ⌊(((4 * m : ℕ) : ℝ) ^ rho) ^ 2⌋₊,
      q.val ∣ K)
    (hrho : 0 < rho) (hrhoUpper : rho ≤ (1 : ℝ) / 10000)
    (hScale : GoldbachCircleMethodResidualScaleAdmissionV18196.blockThreshold rho ≤ 4 * m)
    (hb : 0 ≤ b) (hb1 : b ≤ 1)
    (hR : 1 < ((4 * m : ℕ) : ℝ) ^ rho) :
    |canonicalAdjustedSourceTargetSum m rho b e -
      canonicalSourceVariableMeanTargetSum
        (log_cutoff_contains_one (((4 * m : ℕ) : ℝ) ^ rho) hR)
        hK e
        (logWeight (((4 * m : ℕ) : ℝ) ^ rho) canonicalLogBump)
        (logWeight (((4 * m : ℕ) : ℝ) ^ rho) canonicalLogBump)
        m b| ≤ ((4 * m : ℕ) : ℝ) ^ 2 / 112 := by
  let hQ : 1 ≤ ⌊(((4 * m : ℕ) : ℝ) ^ rho) ^ 2⌋₊ :=
    log_cutoff_contains_one (((4 * m : ℕ) : ℝ) ^ rho) hR
  let wt : ℕ → ℂ :=
    logWeight (((4 * m : ℕ) : ℝ) ^ rho) canonicalLogBump
  have hpoint (i : ℕ) (hi : i ∈ Finset.range (2 * m)) :
      |(canonicalAdjustedModelAt (4 * m) rho b e.val
          ((4 * m + 2 + 2 * i : ℕ) : ℤ)).re -
        (powerPairwiseVariableMean hQ e.val.1 e.val.2 wt wt b
          (4 * m + 2 + 2 * i)
          (blockPairLower (4 * m) (4 * m + 2 + 2 * i))
          (canonicalPairMultiplicity (4 * m) (4 * m + 2 + 2 * i))).re| ≤
        ((4 * m : ℕ) : ℝ) / 56 := by
    have hi' : i < 2 * m := Finset.mem_range.mp hi
    have hBN : 4 * m ≤ 4 * m + 2 + 2 * i := by omega
    have hInterval :
        blockPairLower (4 * m) (4 * m + 2 + 2 * i) ≤
          blockPairUpper (4 * m) (4 * m + 2 + 2 * i) := by
      simp only [blockPairLower, blockPairUpper, max_le_iff, le_min_iff]
      omega
    have hnorm := canonicalAdjustedModelAt_sub_variableMean_norm_lt_half_reserve
      (4 * m) (4 * m + 2 + 2 * i) rho b e.val e.property.2 hb hb1
      (by omega) hBN hInterval hrho hrhoUpper hScale
    calc
      _ = |(canonicalAdjustedModelAt (4 * m) rho b e.val
              ((4 * m + 2 + 2 * i : ℕ) : ℤ) -
            powerPairwiseVariableMean hQ e.val.1 e.val.2 wt wt b
              (4 * m + 2 + 2 * i)
              (blockPairLower (4 * m) (4 * m + 2 + 2 * i))
              (canonicalPairMultiplicity (4 * m) (4 * m + 2 + 2 * i))).re| := by
        rw [Complex.sub_re]
      _ ≤ ‖canonicalAdjustedModelAt (4 * m) rho b e.val
              ((4 * m + 2 + 2 * i : ℕ) : ℤ) -
            powerPairwiseVariableMean hQ e.val.1 e.val.2 wt wt b
              (4 * m + 2 + 2 * i)
              (blockPairLower (4 * m) (4 * m + 2 + 2 * i))
              (canonicalPairMultiplicity (4 * m) (4 * m + 2 + 2 * i))‖ :=
        Complex.abs_re_le_norm _
      _ ≤ ((4 * m : ℕ) : ℝ) / 56 := by
        exact le_of_lt (by simpa only [hQ, wt, canonicalPairMultiplicity] using hnorm)
  unfold canonicalAdjustedSourceTargetSum canonicalSourceVariableMeanTargetSum
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ i ∈ Finset.range (2 * m),
        ((canonicalAdjustedModelAt (4 * m) rho b e.val
          ((4 * m + 2 + 2 * i : ℕ) : ℤ)).re -
        (powerPairwiseVariableMean hQ e.val.1 e.val.2 wt wt b
          (4 * m + 2 + 2 * i)
          (blockPairLower (4 * m) (4 * m + 2 + 2 * i))
          (canonicalPairMultiplicity (4 * m) (4 * m + 2 + 2 * i))).re)| ≤
        ∑ i ∈ Finset.range (2 * m),
          |(canonicalAdjustedModelAt (4 * m) rho b e.val
              ((4 * m + 2 + 2 * i : ℕ) : ℤ)).re -
            (powerPairwiseVariableMean hQ e.val.1 e.val.2 wt wt b
              (4 * m + 2 + 2 * i)
              (blockPairLower (4 * m) (4 * m + 2 + 2 * i))
              (canonicalPairMultiplicity (4 * m) (4 * m + 2 + 2 * i))).re| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ Finset.range (2 * m),
          ((4 * m : ℕ) : ℝ) / 56 := Finset.sum_le_sum hpoint
    _ = ((4 * m : ℕ) : ℝ) ^ 2 / 112 := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      push_cast
      ring

/-- Substantive endpoint: after paying both independent `Q^4` budgets, the
real aggregate of the literal incomplete adjusted convolutions is positive. -/
theorem admitted_canonical_adjusted_source_target_sum_pos
    {K : ℕ} [NeZero K]
    (m : ℕ) (hm : 1 ≤ m) (rho b : ℝ)
    (e : StructurallyAdmissibleActiveSlot
      ⌊(((4 * m : ℕ) : ℝ) ^ rho) ^ 2⌋₊)
    (hK : ∀ q : PositiveLevel ⌊(((4 * m : ℕ) : ℝ) ^ rho) ^ 2⌋₊,
      q.val ∣ K)
    (hrho : 0 < rho) (hrhoUpper : rho ≤ (1 : ℝ) / 10000)
    (hScale : GoldbachCircleMethodResidualScaleAdmissionV18196.blockThreshold rho ≤ 4 * m)
    (hb : 0 ≤ b) (hb1 : b ≤ 1)
    (hR : 1 < ((4 * m : ℕ) : ℝ) ^ rho) :
    0 < canonicalAdjustedSourceTargetSum m rho b e := by
  let mean : ℝ := canonicalSourceVariableMeanTargetSum
    (log_cutoff_contains_one (((4 * m : ℕ) : ℝ) ^ rho) hR)
    hK e
    (logWeight (((4 * m : ℕ) : ℝ) ^ rho) canonicalLogBump)
    (logWeight (((4 * m : ℕ) : ℝ) ^ rho) canonicalLogBump)
    m b
  have hmean := admitted_canonical_source_variable_mean_gt_one_forty_second
    m hm rho b e hK hrho hrhoUpper hScale hb hb1 hR
  have hboundary :=
    canonical_adjusted_source_target_sum_sub_mean_abs_le_boundary
      m hm rho b e hK hrho hrhoUpper hScale hb hb1 hR
  have hlower : -(((4 * m : ℕ) : ℝ) ^ 2 / 112) ≤
      canonicalAdjustedSourceTargetSum m rho b e - mean :=
    (abs_le.mp (by simpa only [mean] using hboundary)).1
  have hBpos : 0 < ((4 * m : ℕ) : ℝ) := by
    positivity
  have hmean' : ((4 * m : ℕ) : ℝ) ^ 2 / 42 < mean := by
    simpa only [mean] using hmean
  nlinarith [sq_pos_of_pos hBpos]

end GoldbachCircleMethodCanonicalActualSourcePositiveV18400
