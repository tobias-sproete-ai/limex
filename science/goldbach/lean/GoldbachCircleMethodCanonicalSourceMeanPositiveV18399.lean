import GoldbachCircleMethodSourceRealCorrectionBindingV18398
import GoldbachCircleMethodPositivePrincipalDiagonalV18221

/-!
# Goldbach V1.8.399: canonical source-mean positivity

This module performs the first source-side recombination after the pairwise
`Q^4` correction audit.  On the canonical block `B = 4m`, the complete even
target sweep has exact pair multiplicity `2m^2 = B^2/8`.  A certified
rational lower bound for the principal floor then dominates the admitted
source-real correction budget from V1.8.397.

The conclusion concerns the aggregate complete-period variable mean.  It is
not yet the literal incomplete adjusted convolution, an exceptional-set
bound, or Goldbach.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodCanonicalSourceMeanPositiveV18399

open GoldbachCircleMethodActualFrozenModelCompleteDiagonalV18213
open GoldbachCircleMethodAdmittedSourceVariableCorrectionBudgetV18397
open GoldbachCircleMethodBlockPairCarrierV18227
open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodCanonicalBumpPrincipalFloorV18220
open GoldbachCircleMethodCanonicalTargetWeightPiecewiseGeometryV18368
open GoldbachCircleMethodLogCutoffPresieveBindingV18120
open GoldbachCircleMethodPositivePrincipalDiagonalV18221
open GoldbachCircleMethodPowerWeightAbelIntervalV18331
open GoldbachCircleMethodPrincipalWindowBoundaryV18121
open GoldbachCircleMethodSourceBoundVariableCoupledCorrectionV18396
open GoldbachCircleMethodSourceRealCorrectionBindingV18398
open GoldbachCircleMethodStructurallyAdmissibleActiveSlotV18258
open GoldbachCircleMethodVariableMeanCombinedReserveV18340
open GoldbachCircleMethodVariableMeanUnitPairNormalFormV18335
open GoldbachCircleMethodVariableUnitPairExactCorrectionV18344

/-- A fully certified rational margin for the finite principal floor. -/
theorem one_seventh_lt_principal_floor :
    (1 : ℝ) / 7 < 2 - Real.exp (Real.pi ^ 2 / 24) := by
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

/-- Literal number of source pairs at one target. -/
def canonicalPairMultiplicity (B N : ℕ) : ℕ :=
  blockPairUpper B N - blockPairLower B N + 1

theorem canonicalPairMultiplicity_growing_four_mul
    (m i : ℕ) (_hm : 1 ≤ m) (hi : i < m) :
    canonicalPairMultiplicity (4 * m) (4 * m + 2 + 2 * i) = 2 * i + 1 := by
  have hBN : 4 * m ≤ 4 * m + 2 + 2 * i := by omega
  have hTurn : 4 * m + 2 + 2 * i ≤ blockPairTurningTarget (4 * m) := by
    simp [blockPairTurningTarget]
    omega
  unfold canonicalPairMultiplicity
  rw [blockPairLower_eq_fixed_of_le_turn _ _ hBN hTurn,
    blockPairUpper_eq_moving_of_le_turn _ _ hTurn]
  omega

theorem canonicalPairMultiplicity_shrinking_four_mul
    (m i : ℕ) (_hm : 1 ≤ m) (hi : i < m) :
    canonicalPairMultiplicity (4 * m) (4 * m + 2 + 2 * (m + i)) =
      2 * (m - i) - 1 := by
  have hTurn : blockPairTurningTarget (4 * m) ≤
      4 * m + 2 + 2 * (m + i) := by
    rw [show blockPairTurningTarget (4 * m) = 6 * m + 1 by
      simp [blockPairTurningTarget]
      omega]
    omega
  unfold canonicalPairMultiplicity
  rw [blockPairLower_eq_moving_of_turn_le _ _ hTurn,
    blockPairUpper_eq_fixed_of_turn_le _ _ hTurn]
  omega

theorem sum_first_odd (m : ℕ) :
    ∑ i ∈ Finset.range m, (2 * i + 1) = m ^ 2 := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ, ih]
      ring

theorem sum_descending_odd (m : ℕ) :
    ∑ i ∈ Finset.range m, (2 * (m - i) - 1) = m ^ 2 := by
  calc
    (∑ i ∈ Finset.range m, (2 * (m - i) - 1)) =
        ∑ i ∈ Finset.range m, (2 * (m - 1 - i) + 1) := by
      apply Finset.sum_congr rfl
      intro i hi
      have him : i < m := Finset.mem_range.mp hi
      omega
    _ = ∑ i ∈ Finset.range m, (2 * i + 1) := by
      exact Finset.sum_range_reflect (fun i => 2 * i + 1) m
    _ = m ^ 2 := sum_first_odd m

/-- Exact pair multiplicity of the canonical complete even-target sweep. -/
theorem canonical_even_target_pair_multiplicity_sum
    (m : ℕ) (hm : 1 ≤ m) :
    (∑ i ∈ Finset.range (2 * m),
      canonicalPairMultiplicity (4 * m) (4 * m + 2 + 2 * i)) =
        2 * m ^ 2 := by
  rw [show 2 * m = m + m by omega, Finset.sum_range_add]
  have hgrow :
      (∑ i ∈ Finset.range m,
        canonicalPairMultiplicity (4 * m) (4 * m + 2 + 2 * i)) = m ^ 2 := by
    calc
      _ = ∑ i ∈ Finset.range m, (2 * i + 1) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact canonicalPairMultiplicity_growing_four_mul m i hm
          (Finset.mem_range.mp hi)
      _ = m ^ 2 := sum_first_odd m
  have hshrink :
      (∑ i ∈ Finset.range m,
        canonicalPairMultiplicity (4 * m) (4 * m + 2 + 2 * (m + i))) =
          m ^ 2 := by
    calc
      _ = ∑ i ∈ Finset.range m, (2 * (m - i) - 1) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact canonicalPairMultiplicity_shrinking_four_mul m i hm
          (Finset.mem_range.mp hi)
      _ = m ^ 2 := sum_descending_odd m
  rw [hgrow]
  convert congrArg (fun x => m ^ 2 + x) hshrink using 1
  ring

/-- Aggregate principal contribution on the canonical even-target sweep. -/
noncomputable def canonicalPrincipalRealTargetSum
    {Q K : ℕ} [NeZero K]
    (hK : ∀ q : PositiveLevel Q, q.val ∣ K)
    (v w : ℕ → ℂ) (m : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (2 * m),
    (canonicalPairMultiplicity (4 * m) (4 * m + 2 + 2 * i) : ℝ) *
      (principalDiagonal hK v w
        ((4 * m + 2 + 2 * i : ℕ) : ZMod K)).re

/-- The canonical principal aggregate strictly exceeds `B^2/56`. -/
theorem canonical_principal_target_sum_gt_quadratic_budget
    {K : ℕ} [NeZero K] (m : ℕ) (hm : 1 ≤ m)
    (rho : ℝ) (hR : 1 < ((4 * m : ℕ) : ℝ) ^ rho)
    (hK : ∀ q : PositiveLevel ⌊(((4 * m : ℕ) : ℝ) ^ rho) ^ 2⌋₊,
      q.val ∣ K) :
    ((4 * m : ℕ) : ℝ) ^ 2 / 56 <
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
  have hkappa : (1 : ℝ) / 7 < kappa := by
    exact one_seventh_lt_principal_floor
  have hmpos : 0 < (m : ℝ) := by
    exact_mod_cast (Nat.zero_lt_of_lt hm)
  have hstrict :
      ((4 * m : ℕ) : ℝ) ^ 2 / 56 < kappa * (2 * (m : ℝ) ^ 2) := by
    push_cast
    nlinarith [sq_pos_of_pos hmpos]
  exact hstrict.trans_le hsum

/-- Actual aggregate complete-period variable mean over the canonical target
sweep. -/
noncomputable def canonicalSourceVariableMeanTargetSum
    {Q K : ℕ} [NeZero K] (hQ : 1 ≤ Q)
    (_hK : ∀ q : PositiveLevel Q, q.val ∣ K)
    (e : StructurallyAdmissibleActiveSlot Q)
    (v w : ℕ → ℂ) (m : ℕ) (b : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (2 * m),
    (powerPairwiseVariableMean hQ e.val.1 e.val.2 v w b
      (4 * m + 2 + 2 * i)
      (blockPairLower (4 * m) (4 * m + 2 + 2 * i))
      (canonicalPairMultiplicity (4 * m) (4 * m + 2 + 2 * i))).re

/-- Exact source decomposition of the aggregate variable mean into its
principal mass and the source-real correction. -/
theorem canonical_source_variable_mean_eq_principal_add_correction
    {Q K : ℕ} [NeZero K] (hQ : 1 ≤ Q)
    (hK : ∀ q : PositiveLevel Q, q.val ∣ K)
    (e : StructurallyAdmissibleActiveSlot Q)
    (v w : ℕ → ℂ) (m : ℕ) (b : ℝ) :
    canonicalSourceVariableMeanTargetSum hQ hK e v w m b =
      canonicalPrincipalRealTargetSum hK v w m +
        sourceRealActualVariableCorrectionTargetSum hK e v w
          (4 * m) (4 * m + 2) (2 * m) b := by
  unfold canonicalSourceVariableMeanTargetSum canonicalPrincipalRealTargetSum
    sourceRealActualVariableCorrectionTargetSum canonicalPairMultiplicity
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [powerPairwiseVariableMean_re_eq_principal_sub_deficit
    hQ hK e.val.1 e.val.2 e.property.2 v w b]
  rw [variableUnitPairDeficit_eq_exactCorrection_re
    e.val.1.val (4 * m + 2 + 2 * i)
    (blockPairLower (4 * m) (4 * m + 2 + 2 * i))
    (blockPairUpper (4 * m) (4 * m + 2 + 2 * i) -
      blockPairLower (4 * m) (4 * m + 2 + 2 * i) + 1)
    e.val.2.val e.val.2.property e.property.2 b]
  ring

/-- At the admitted canonical scale, the source aggregate complete-period
variable mean is strictly positive. -/
theorem admitted_canonical_source_variable_mean_target_sum_pos
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
    0 < canonicalSourceVariableMeanTargetSum
      (log_cutoff_contains_one (((4 * m : ℕ) : ℝ) ^ rho) hR)
      hK e
      (logWeight (((4 * m : ℕ) : ℝ) ^ rho) canonicalLogBump)
      (logWeight (((4 * m : ℕ) : ℝ) ^ rho) canonicalLogBump)
      m b := by
  let wt : ℕ → ℂ :=
    logWeight (((4 * m : ℕ) : ℝ) ^ rho) canonicalLogBump
  have hprincipal := canonical_principal_target_sum_gt_quadratic_budget
    m hm rho hR hK
  have hhalf : (4 * m) / 2 = 2 * m := by omega
  have hAeven : Even (4 * m + 2) := by
    exact ⟨2 * m + 1, by omega⟩
  have hBtwo : 2 ≤ 4 * m := by omega
  have hBA : 4 * m ≤ 4 * m + 2 := by omega
  have hNonempty : 2 * ((4 * m) / 2 + 1) ≤ 4 * m + 2 := by omega
  have hKgrow : 1 ≤ m := hm
  have hGrowingLast :
      4 * m + 2 + 2 * (m - 1) ≤ blockPairTurningTarget (4 * m) := by
    simp [blockPairTurningTarget, hhalf]
    omega
  have hS : 1 ≤ m := hm
  have hShrinkingFirst :
      blockPairTurningTarget (4 * m) ≤ 4 * m + 2 + 2 * m := by
    simp [blockPairTurningTarget, hhalf]
  have hFinal :
      4 * m + 2 + 2 * m + 2 * (m - 1) ≤ 2 * (4 * m) := by omega
  have hcorrNorm := admitted_source_variable_correction_norm_lt_quadratic_budget
    (B := 4 * m) (A := 4 * m + 2) (Kgrow := m) (S := m)
    (rho := rho) (b := b) e K hK hrho hrhoUpper hScale hb hb1
      hAeven hBtwo hBA hNonempty hKgrow hGrowingLast hS hShrinkingFirst hFinal
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

end GoldbachCircleMethodCanonicalSourceMeanPositiveV18399
