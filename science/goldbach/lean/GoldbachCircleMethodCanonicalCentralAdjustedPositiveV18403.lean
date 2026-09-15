import GoldbachCircleMethodCanonicalActiveResidualAggregateV18402

/-!
# Goldbach V1.8.403: canonical central adjusted-source positivity

The V1.8.400 sweep is narrowed to the exact target band on which the existing
adjusted centered-correction theorem is stated.  At `B=8m`, the targets
`10m,10m+2,...,14m` lie in `[5B/4,7B/4]`.  Their pair multiplicity is computed
exactly, and the principal reserve pays both pairwise-period `Q^4` costs while
retaining a strict `B^2/224` adjusted-source aggregate.

No source residual or centered-error estimate is used here.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodCanonicalCentralAdjustedPositiveV18403

open GoldbachCircleMethodActiveResidualExactDecompositionV18251
open GoldbachCircleMethodActualFrozenModelCompleteDiagonalV18213
open GoldbachCircleMethodAdmittedCanonicalAbelAbsorptionV18333
open GoldbachCircleMethodAdmittedSourceVariableCorrectionBudgetV18397
open GoldbachCircleMethodBlockPairCarrierV18227
open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodCanonicalActualSourcePositiveV18400
open GoldbachCircleMethodCanonicalBumpPrincipalFloorV18220
open GoldbachCircleMethodCanonicalSourceMeanPositiveV18399
open GoldbachCircleMethodCanonicalTargetWeightPiecewiseGeometryV18368
open GoldbachCircleMethodLogCutoffPresieveBindingV18120
open GoldbachCircleMethodPositivePrincipalDiagonalV18221
open GoldbachCircleMethodPowerWeightAbelIntervalV18331
open GoldbachCircleMethodPrincipalWindowBoundaryV18121
open GoldbachCircleMethodSourceBoundVariableCoupledCorrectionV18396
open GoldbachCircleMethodSourceRealCorrectionBindingV18398
open GoldbachCircleMethodStructurallyAdmissibleActiveSlotV18258
open GoldbachCircleMethodVariableMeanCombinedReserveV18340
open GoldbachCircleMethodVariableUnitPairExactCorrectionV18344

/-- Central target at index `i` for block size `B=8m`. -/
def centralTargetNat (m i : ℕ) : ℕ := 10 * m + 2 * i

theorem central_pair_multiplicity_growing
    (m i : ℕ) (hm : 1 ≤ m) (hi : i < m + 1) :
    canonicalPairMultiplicity (8 * m) (centralTargetNat m i) =
      2 * m + 2 * i - 1 := by
  have hBN : 8 * m ≤ centralTargetNat m i := by
    simp only [centralTargetNat]
    omega
  have hTurn :
      centralTargetNat m i ≤ blockPairTurningTarget (8 * m) := by
    simp only [centralTargetNat, blockPairTurningTarget]
    omega
  unfold canonicalPairMultiplicity
  rw [blockPairLower_eq_fixed_of_le_turn _ _ hBN hTurn,
    blockPairUpper_eq_moving_of_le_turn _ _ hTurn]
  simp only [centralTargetNat]
  omega

theorem central_pair_multiplicity_shrinking
    (m j : ℕ) (hm : 1 ≤ m) (hj : j < m) :
    canonicalPairMultiplicity (8 * m)
        (centralTargetNat m (m + 1 + j)) =
      4 * m - 2 * j - 1 := by
  have hTurn :
      blockPairTurningTarget (8 * m) ≤
        centralTargetNat m (m + 1 + j) := by
    simp only [centralTargetNat, blockPairTurningTarget]
    omega
  unfold canonicalPairMultiplicity
  rw [blockPairLower_eq_moving_of_turn_le _ _ hTurn,
    blockPairUpper_eq_fixed_of_turn_le _ _ hTurn]
  simp only [centralTargetNat]
  omega

theorem central_growing_multiplicity_sum
    (m : ℕ) (hm : 1 ≤ m) :
    (∑ i ∈ Finset.range (m + 1),
      canonicalPairMultiplicity (8 * m) (centralTargetNat m i)) =
        3 * m ^ 2 + 2 * m - 1 := by
  calc
    _ = ∑ i ∈ Finset.range (m + 1), (2 * m + 2 * i - 1) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact central_pair_multiplicity_growing m i hm
        (Finset.mem_range.mp hi)
    _ = (∑ i ∈ Finset.range m, (2 * m + (2 * i + 1))) +
        (2 * m - 1) := by
      rw [Finset.sum_range_succ']
      apply congrArg (fun x => x + (2 * m - 1))
      apply Finset.sum_congr rfl
      intro i hi
      have him : i < m := Finset.mem_range.mp hi
      omega
    _ = 3 * m ^ 2 + 2 * m - 1 := by
      rw [Finset.sum_add_distrib]
      rw [show (∑ _i ∈ Finset.range m, 2 * m) = m * (2 * m) by simp]
      rw [sum_first_odd]
      rw [show m * (2 * m) = 2 * m ^ 2 by ring]
      omega

theorem central_shrinking_multiplicity_sum
    (m : ℕ) (hm : 1 ≤ m) :
    (∑ j ∈ Finset.range m,
      canonicalPairMultiplicity (8 * m)
        (centralTargetNat m (m + 1 + j))) = 3 * m ^ 2 := by
  calc
    _ = ∑ j ∈ Finset.range m, (4 * m - 2 * j - 1) := by
      apply Finset.sum_congr rfl
      intro j hj
      exact central_pair_multiplicity_shrinking m j hm
        (Finset.mem_range.mp hj)
    _ = ∑ j ∈ Finset.range m, (2 * m + (2 * (m - j) - 1)) := by
      apply Finset.sum_congr rfl
      intro j hj
      have hjm : j < m := Finset.mem_range.mp hj
      omega
    _ = 3 * m ^ 2 := by
      rw [Finset.sum_add_distrib]
      rw [show (∑ _j ∈ Finset.range m, 2 * m) = m * (2 * m) by simp]
      rw [sum_descending_odd]
      ring

/-- Exact pair mass on the whole central sweep. -/
theorem central_target_pair_multiplicity_sum
    (m : ℕ) (hm : 1 ≤ m) :
    (∑ i ∈ Finset.range (2 * m + 1),
      canonicalPairMultiplicity (8 * m) (centralTargetNat m i)) =
        6 * m ^ 2 + 2 * m - 1 := by
  rw [show 2 * m + 1 = (m + 1) + m by omega, Finset.sum_range_add]
  rw [central_growing_multiplicity_sum m hm]
  rw [central_shrinking_multiplicity_sum m hm]
  omega

noncomputable def centralPrincipalRealTargetSum
    {Q K : ℕ} [NeZero K]
    (hK : ∀ q : PositiveLevel Q, q.val ∣ K)
    (v w : ℕ → ℂ) (m : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (2 * m + 1),
    (canonicalPairMultiplicity (8 * m) (centralTargetNat m i) : ℝ) *
      (principalDiagonal hK v w ((centralTargetNat m i : ℕ) : ZMod K)).re

/-- The central principal aggregate has a strict `B^2/32` reserve. -/
theorem central_principal_target_sum_gt_thirty_second
    {K : ℕ} [NeZero K] (m : ℕ) (hm : 1 ≤ m)
    (rho : ℝ) (hR : 1 < ((8 * m : ℕ) : ℝ) ^ rho)
    (hK : ∀ q : PositiveLevel ⌊(((8 * m : ℕ) : ℝ) ^ rho) ^ 2⌋₊,
      q.val ∣ K) :
    ((8 * m : ℕ) : ℝ) ^ 2 / 32 <
      centralPrincipalRealTargetSum hK
        (logWeight (((8 * m : ℕ) : ℝ) ^ rho) canonicalLogBump)
        (logWeight (((8 * m : ℕ) : ℝ) ^ rho) canonicalLogBump) m := by
  let kappa : ℝ := 2 - Real.exp (Real.pi ^ 2 / 24)
  let wt : ℕ → ℂ :=
    logWeight (((8 * m : ℕ) : ℝ) ^ rho) canonicalLogBump
  have hterm (i : ℕ) (hi : i ∈ Finset.range (2 * m + 1)) :
      kappa * (canonicalPairMultiplicity (8 * m)
          (centralTargetNat m i) : ℝ) ≤
        (canonicalPairMultiplicity (8 * m) (centralTargetNat m i) : ℝ) *
          (principalDiagonal hK wt wt
            ((centralTargetNat m i : ℕ) : ZMod K)).re := by
    have hEven : Even (centralTargetNat m i) := by
      refine ⟨5 * m + i, ?_⟩
      simp only [centralTargetNat]
      omega
    have hfloor := actual_principalDiagonal_canonicalLogBump_floor
      (((8 * m : ℕ) : ℝ) ^ rho) hR hK hEven
    have hmul := mul_le_mul_of_nonneg_left hfloor
      (Nat.cast_nonneg
        (canonicalPairMultiplicity (8 * m) (centralTargetNat m i)))
    simpa only [kappa, wt, mul_comm] using hmul
  have hsum :
      kappa *
          (∑ i ∈ Finset.range (2 * m + 1),
            (canonicalPairMultiplicity (8 * m)
              (centralTargetNat m i) : ℝ)) ≤
        centralPrincipalRealTargetSum hK wt wt m := by
    unfold centralPrincipalRealTargetSum
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum hterm
  have hmassNat := central_target_pair_multiplicity_sum m hm
  have hmassReal :
      (∑ i ∈ Finset.range (2 * m + 1),
        (canonicalPairMultiplicity (8 * m)
          (centralTargetNat m i) : ℝ)) =
          (6 * m ^ 2 + 2 * m - 1 : ℕ) := by
    exact_mod_cast hmassNat
  rw [hmassReal] at hsum
  have hkappa : (1 : ℝ) / 3 < kappa := one_third_lt_principal_floor
  have hmpos : 0 < (m : ℝ) := by exact_mod_cast Nat.zero_lt_of_lt hm
  have hmass : 6 * (m : ℝ) ^ 2 <
      (6 * m ^ 2 + 2 * m - 1 : ℕ) := by
    exact_mod_cast (show 6 * m ^ 2 < 6 * m ^ 2 + 2 * m - 1 by omega)
  have hstrict :
      ((8 * m : ℕ) : ℝ) ^ 2 / 32 <
        kappa * (6 * m ^ 2 + 2 * m - 1 : ℕ) := by
    push_cast
    nlinarith [sq_pos_of_pos hmpos]
  exact hstrict.trans_le hsum

noncomputable def centralSourceVariableMeanTargetSum
    {Q K : ℕ} [NeZero K] (hQ : 1 ≤ Q)
    (_hK : ∀ q : PositiveLevel Q, q.val ∣ K)
    (e : StructurallyAdmissibleActiveSlot Q)
    (v w : ℕ → ℂ) (m : ℕ) (b : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (2 * m + 1),
    (powerPairwiseVariableMean hQ e.val.1 e.val.2 v w b
      (centralTargetNat m i)
      (blockPairLower (8 * m) (centralTargetNat m i))
      (canonicalPairMultiplicity (8 * m) (centralTargetNat m i))).re

theorem central_source_variable_mean_eq_principal_add_correction
    {Q K : ℕ} [NeZero K] (hQ : 1 ≤ Q)
    (hK : ∀ q : PositiveLevel Q, q.val ∣ K)
    (e : StructurallyAdmissibleActiveSlot Q)
    (v w : ℕ → ℂ) (m : ℕ) (b : ℝ) :
    centralSourceVariableMeanTargetSum hQ hK e v w m b =
      centralPrincipalRealTargetSum hK v w m +
        sourceRealActualVariableCorrectionTargetSum hK e v w
          (8 * m) (10 * m) (2 * m + 1) b := by
  unfold centralSourceVariableMeanTargetSum centralPrincipalRealTargetSum
    sourceRealActualVariableCorrectionTargetSum canonicalPairMultiplicity
    centralTargetNat
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [powerPairwiseVariableMean_re_eq_principal_sub_deficit
    hQ hK e.val.1 e.val.2 e.property.2 v w b]
  rw [variableUnitPairDeficit_eq_exactCorrection_re
    e.val.1.val (10 * m + 2 * i)
    (blockPairLower (8 * m) (10 * m + 2 * i))
    (blockPairUpper (8 * m) (10 * m + 2 * i) -
      blockPairLower (8 * m) (10 * m + 2 * i) + 1)
    e.val.2.val e.val.2.property e.property.2 b]
  ring

theorem admitted_central_source_variable_mean_gt_three_over_224
    {K : ℕ} [NeZero K]
    (m : ℕ) (hm : 1 ≤ m) (rho b : ℝ)
    (e : StructurallyAdmissibleActiveSlot
      ⌊(((8 * m : ℕ) : ℝ) ^ rho) ^ 2⌋₊)
    (hK : ∀ q : PositiveLevel ⌊(((8 * m : ℕ) : ℝ) ^ rho) ^ 2⌋₊,
      q.val ∣ K)
    (hrho : 0 < rho) (hrhoUpper : rho ≤ (1 : ℝ) / 10000)
    (hScale : GoldbachCircleMethodResidualScaleAdmissionV18196.blockThreshold rho ≤ 8 * m)
    (hb : 0 ≤ b) (hb1 : b ≤ 1)
    (hR : 1 < ((8 * m : ℕ) : ℝ) ^ rho) :
    3 * ((8 * m : ℕ) : ℝ) ^ 2 / 224 <
      centralSourceVariableMeanTargetSum
        (log_cutoff_contains_one (((8 * m : ℕ) : ℝ) ^ rho) hR)
        hK e
        (logWeight (((8 * m : ℕ) : ℝ) ^ rho) canonicalLogBump)
        (logWeight (((8 * m : ℕ) : ℝ) ^ rho) canonicalLogBump)
        m b := by
  let wt : ℕ → ℂ :=
    logWeight (((8 * m : ℕ) : ℝ) ^ rho) canonicalLogBump
  have hprincipal := central_principal_target_sum_gt_thirty_second
    m hm rho hR hK
  have hAeven : Even (10 * m) := ⟨5 * m, by omega⟩
  have hcorrNorm := admitted_source_variable_correction_norm_lt_quadratic_budget
    (B := 8 * m) (A := 10 * m) (Kgrow := m + 1) (S := m)
    (rho := rho) (b := b) e K hK hrho hrhoUpper hScale hb hb1
      hAeven (by omega) (by omega) (by omega) (by omega)
      (by simp [blockPairTurningTarget]; omega) hm
      (by simp [blockPairTurningTarget]; omega) (by omega)
  have hcorrRe :
      ‖(sourceNormalizedActualVariableCorrectionTargetSum hK e wt wt
        (8 * m) (10 * m) (2 * m + 1) b).re‖ <
          ((8 * m : ℕ) : ℝ) ^ 2 / 56 := by
    exact (Complex.abs_re_le_norm _).trans_lt
      (by simpa only [wt, show m + 1 + m = 2 * m + 1 by omega]
        using hcorrNorm)
  have hcorrLower :
      -(((8 * m : ℕ) : ℝ) ^ 2 / 56) <
        sourceRealActualVariableCorrectionTargetSum hK e wt wt
          (8 * m) (10 * m) (2 * m + 1) b := by
    have hre := sourceNormalizedActualVariableCorrectionTargetSum_re_eq_sourceReal
      hK e (((8 * m : ℕ) : ℝ) ^ rho) (8 * m) (10 * m) (2 * m + 1) b
    rw [← hre]
    exact (abs_lt.mp hcorrRe).1
  rw [central_source_variable_mean_eq_principal_add_correction]
  dsimp only [wt] at hcorrLower
  nlinarith

noncomputable def centralAdjustedSourceTargetSum
    (m : ℕ) (rho b : ℝ)
    (e : StructurallyAdmissibleActiveSlot
      ⌊(((8 * m : ℕ) : ℝ) ^ rho) ^ 2⌋₊) : ℝ :=
  ∑ i ∈ Finset.range (2 * m + 1),
    (canonicalAdjustedModelAt (8 * m) rho b e.val
      ((centralTargetNat m i : ℕ) : ℤ)).re

theorem central_adjusted_source_sub_mean_abs_le_boundary
    {K : ℕ} [NeZero K]
    (m : ℕ) (hm : 1 ≤ m) (rho b : ℝ)
    (e : StructurallyAdmissibleActiveSlot
      ⌊(((8 * m : ℕ) : ℝ) ^ rho) ^ 2⌋₊)
    (hK : ∀ q : PositiveLevel ⌊(((8 * m : ℕ) : ℝ) ^ rho) ^ 2⌋₊,
      q.val ∣ K)
    (hrho : 0 < rho) (hrhoUpper : rho ≤ (1 : ℝ) / 10000)
    (hScale : GoldbachCircleMethodResidualScaleAdmissionV18196.blockThreshold rho ≤ 8 * m)
    (hb : 0 ≤ b) (hb1 : b ≤ 1)
    (hR : 1 < ((8 * m : ℕ) : ℝ) ^ rho) :
    |centralAdjustedSourceTargetSum m rho b e -
      centralSourceVariableMeanTargetSum
        (log_cutoff_contains_one (((8 * m : ℕ) : ℝ) ^ rho) hR)
        hK e
        (logWeight (((8 * m : ℕ) : ℝ) ^ rho) canonicalLogBump)
        (logWeight (((8 * m : ℕ) : ℝ) ^ rho) canonicalLogBump)
        m b| ≤ ((8 * m : ℕ) : ℝ) ^ 2 / 112 := by
  let hQ : 1 ≤ ⌊(((8 * m : ℕ) : ℝ) ^ rho) ^ 2⌋₊ :=
    log_cutoff_contains_one (((8 * m : ℕ) : ℝ) ^ rho) hR
  let wt : ℕ → ℂ :=
    logWeight (((8 * m : ℕ) : ℝ) ^ rho) canonicalLogBump
  have hpoint (i : ℕ) (hi : i ∈ Finset.range (2 * m + 1)) :
      |(canonicalAdjustedModelAt (8 * m) rho b e.val
          ((centralTargetNat m i : ℕ) : ℤ)).re -
        (powerPairwiseVariableMean hQ e.val.1 e.val.2 wt wt b
          (centralTargetNat m i)
          (blockPairLower (8 * m) (centralTargetNat m i))
          (canonicalPairMultiplicity (8 * m) (centralTargetNat m i))).re| ≤
        ((8 * m : ℕ) : ℝ) / 56 := by
    have hi' : i < 2 * m + 1 := Finset.mem_range.mp hi
    have hBN : 8 * m ≤ centralTargetNat m i := by
      simp only [centralTargetNat]
      omega
    have hInterval :
        blockPairLower (8 * m) (centralTargetNat m i) ≤
          blockPairUpper (8 * m) (centralTargetNat m i) := by
      simp only [blockPairLower, blockPairUpper, max_le_iff, le_min_iff,
        centralTargetNat]
      omega
    have hnorm := canonicalAdjustedModelAt_sub_variableMean_norm_lt_half_reserve
      (8 * m) (centralTargetNat m i) rho b e.val e.property.2 hb hb1
      (by omega) hBN hInterval hrho hrhoUpper hScale
    calc
      _ = |(canonicalAdjustedModelAt (8 * m) rho b e.val
              ((centralTargetNat m i : ℕ) : ℤ) -
            powerPairwiseVariableMean hQ e.val.1 e.val.2 wt wt b
              (centralTargetNat m i)
              (blockPairLower (8 * m) (centralTargetNat m i))
              (canonicalPairMultiplicity (8 * m)
                (centralTargetNat m i))).re| := by
        rw [Complex.sub_re]
      _ ≤ ‖canonicalAdjustedModelAt (8 * m) rho b e.val
              ((centralTargetNat m i : ℕ) : ℤ) -
            powerPairwiseVariableMean hQ e.val.1 e.val.2 wt wt b
              (centralTargetNat m i)
              (blockPairLower (8 * m) (centralTargetNat m i))
              (canonicalPairMultiplicity (8 * m)
                (centralTargetNat m i))‖ := Complex.abs_re_le_norm _
      _ ≤ ((8 * m : ℕ) : ℝ) / 56 := by
        exact le_of_lt (by simpa only [hQ, wt, canonicalPairMultiplicity]
          using hnorm)
  unfold centralAdjustedSourceTargetSum centralSourceVariableMeanTargetSum
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ i ∈ Finset.range (2 * m + 1),
        ((canonicalAdjustedModelAt (8 * m) rho b e.val
          ((centralTargetNat m i : ℕ) : ℤ)).re -
        (powerPairwiseVariableMean hQ e.val.1 e.val.2 wt wt b
          (centralTargetNat m i)
          (blockPairLower (8 * m) (centralTargetNat m i))
          (canonicalPairMultiplicity (8 * m)
            (centralTargetNat m i))).re)| ≤
        ∑ i ∈ Finset.range (2 * m + 1),
          |(canonicalAdjustedModelAt (8 * m) rho b e.val
              ((centralTargetNat m i : ℕ) : ℤ)).re -
            (powerPairwiseVariableMean hQ e.val.1 e.val.2 wt wt b
              (centralTargetNat m i)
              (blockPairLower (8 * m) (centralTargetNat m i))
              (canonicalPairMultiplicity (8 * m)
                (centralTargetNat m i))).re| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ Finset.range (2 * m + 1),
          ((8 * m : ℕ) : ℝ) / 56 := Finset.sum_le_sum hpoint
    _ ≤ ((8 * m : ℕ) : ℝ) ^ 2 / 112 := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      push_cast
      have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
      nlinarith

/-- After both pairwise-period costs, the exact central adjusted aggregate
retains the explicit `B^2/224` source-side reserve. -/
theorem admitted_central_adjusted_source_target_sum_gt_one_over_224
    {K : ℕ} [NeZero K]
    (m : ℕ) (hm : 1 ≤ m) (rho b : ℝ)
    (e : StructurallyAdmissibleActiveSlot
      ⌊(((8 * m : ℕ) : ℝ) ^ rho) ^ 2⌋₊)
    (hK : ∀ q : PositiveLevel ⌊(((8 * m : ℕ) : ℝ) ^ rho) ^ 2⌋₊,
      q.val ∣ K)
    (hrho : 0 < rho) (hrhoUpper : rho ≤ (1 : ℝ) / 10000)
    (hScale : GoldbachCircleMethodResidualScaleAdmissionV18196.blockThreshold rho ≤ 8 * m)
    (hb : 0 ≤ b) (hb1 : b ≤ 1)
    (hR : 1 < ((8 * m : ℕ) : ℝ) ^ rho) :
    ((8 * m : ℕ) : ℝ) ^ 2 / 224 <
      centralAdjustedSourceTargetSum m rho b e := by
  let mean : ℝ := centralSourceVariableMeanTargetSum
    (log_cutoff_contains_one (((8 * m : ℕ) : ℝ) ^ rho) hR)
    hK e
    (logWeight (((8 * m : ℕ) : ℝ) ^ rho) canonicalLogBump)
    (logWeight (((8 * m : ℕ) : ℝ) ^ rho) canonicalLogBump)
    m b
  have hmean := admitted_central_source_variable_mean_gt_three_over_224
    m hm rho b e hK hrho hrhoUpper hScale hb hb1 hR
  have hboundary := central_adjusted_source_sub_mean_abs_le_boundary
    m hm rho b e hK hrho hrhoUpper hScale hb hb1 hR
  have hlower : -(((8 * m : ℕ) : ℝ) ^ 2 / 112) ≤
      centralAdjustedSourceTargetSum m rho b e - mean :=
    (abs_le.mp (by simpa only [mean] using hboundary)).1
  have hmean' : 3 * ((8 * m : ℕ) : ℝ) ^ 2 / 224 < mean := by
    simpa only [mean] using hmean
  nlinarith

end GoldbachCircleMethodCanonicalCentralAdjustedPositiveV18403
