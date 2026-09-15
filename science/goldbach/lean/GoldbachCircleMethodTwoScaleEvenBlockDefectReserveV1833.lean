import GoldbachCircleMethodTwoScaleDefectTransferV1832
import GoldbachPrimePowerDefectBoundV161

/-!
# Even target block and effective prime-power reserve, V1.8.33
Only the existing defect estimate is absorbed. Major and moment estimates
remain explicit inputs for the unchanged fixed-scale operator.
-/
set_option autoImplicit false

namespace GoldbachCircleMethodTwoScaleEvenBlockDefectReserveV1833

open scoped Classical
open GoldbachPurePrimeAdequacyV15 GoldbachVonMangoldtDecompositionV16
open GoldbachPrimePowerDefectBoundV161
open GoldbachCircleMethodTwoScaleIntegralPartitionV1831
open GoldbachCircleMethodExceptionalTransferV1823
open GoldbachCircleMethodTwoScaleDefectTransferV1832

/-- Exact integer block: ceil(M/2) <= N <= M, even N, N >= 4. -/
def evenTargetBlock (M : Nat) : Finset Nat :=
  (Finset.Icc 4 M).filter (fun N => Even N ∧ M ≤ 2 * N)

theorem mem_evenTargetBlock_iff (M N : Nat) :
    N ∈ evenTargetBlock M ↔ 4 ≤ N ∧ N ≤ M ∧ Even N ∧ M ≤ 2 * N := by
  simp [evenTargetBlock, and_assoc]

theorem upperEndpoint_mem_iff (M : Nat) :
    M ∈ evenTargetBlock M ↔ 4 ≤ M ∧ Even M := by
  rw [mem_evenTargetBlock_iff]
  constructor
  · intro h
    exact ⟨h.1, h.2.2.1⟩
  · rintro ⟨h4, hEven⟩
    exact ⟨h4, le_rfl, hEven, by omega⟩

/-- Uniformly raise the old N-dependent defect ceiling to the fixed scale M. -/
theorem primePowerDefect_le_scale_ceiling
    (M N : Nat) (hN : 1 ≤ N) (hNM : N ≤ M) :
    primePowerDefect N ≤ 4 * Real.sqrt (M : Real) * (Real.log (M : Real)) ^ 2 := by
  have hNPos : (0 : Real) < N := by exact_mod_cast (show 0 < N by omega)
  have hMPos : (0 : Real) < M := by exact_mod_cast (show 0 < M by omega)
  have hCast : (N : Real) ≤ M := by exact_mod_cast hNM
  have hLog := (Real.log_le_log_iff hNPos hMPos).2 hCast
  have hSq : (Real.log (N : Real)) ^ 2 ≤ (Real.log (M : Real)) ^ 2 := by
    nlinarith [Real.log_natCast_nonneg N, Real.log_natCast_nonneg M]
  exact (primePowerDefect_le_four_sqrt_mul_log_sq hN).trans
    (mul_le_mul (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hCast) (by norm_num))
      hSq (sq_nonneg _) (by positivity))

theorem scale_ceiling_le_M_div_28
    (M : Nat)
    (hScale : 112 * (Real.log (M : Real)) ^ 2 ≤ Real.sqrt (M : Real)) :
    4 * Real.sqrt (M : Real) * (Real.log (M : Real)) ^ 2 ≤ (M : Real) / 28 := by
  have h := mul_le_mul_of_nonneg_left hScale (Real.sqrt_nonneg (M : Real))
  have hs := Real.sq_sqrt (Nat.cast_nonneg M : (0 : Real) ≤ M)
  nlinarith

theorem primePowerDefect_le_M_div_28
    (M N : Nat) (hN : 1 ≤ N) (hNM : N ≤ M)
    (hScale : 112 * (Real.log (M : Real)) ^ 2 ≤ Real.sqrt (M : Real)) :
    primePowerDefect N ≤ (M : Real) / 28 :=
  (primePowerDefect_le_scale_ceiling M N hN hNM).trans (scale_ceiling_le_M_div_28 M hScale)

/-- Conservative effective scale threshold; no optimality or finite check is claimed. -/
noncomputable def defectScaleThreshold : Nat := ⌈Real.exp 40⌉₊

theorem log_sq_gate_of_exp40_le
    (M : Nat) (hLarge : Real.exp 40 ≤ (M : Real)) :
    112 * (Real.log (M : Real)) ^ 2 ≤ Real.sqrt (M : Real) := by
  have hMPos : (0 : Real) < M := (Real.exp_pos 40).trans_le hLarge
  have ht : (40 : Real) ≤ Real.log (M : Real) := by
    simpa using Real.log_le_log (Real.exp_pos 40) hLarge
  have hQuarter : (10 : Real) ≤ Real.log (M : Real) / 4 := by linarith
  have hExp10 : (3584 : Real) ≤ Real.exp 10 := by
    have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : Real) ≤ 10) 8
    norm_num [Finset.sum_range_succ] at h
    linarith
  have hBig : (3584 : Real) ≤ Real.exp (Real.log (M : Real) / 4) :=
    hExp10.trans (Real.exp_le_exp.mpr hQuarter)
  have hQuadratic := Real.pow_div_factorial_le_exp (Real.log (M : Real) / 4)
    (show 0 ≤ Real.log (M : Real) / 4 by linarith) 2
  norm_num at hQuadratic
  have hProduct := mul_le_mul hBig hQuadratic (by positivity)
    (Real.exp_nonneg (Real.log (M : Real) / 4))
  have hHalf :
      Real.exp (Real.log (M : Real) / 4) * Real.exp (Real.log (M : Real) / 4) =
        Real.sqrt (M : Real) := by
    rw [← Real.exp_add]
    rw [show Real.log (M : Real) / 4 + Real.log (M : Real) / 4 =
      Real.log (M : Real) / 2 by ring, Real.exp_half, Real.exp_log hMPos]
  rw [hHalf] at hProduct
  nlinarith

theorem log_sq_gate_of_threshold_le
    (M : Nat) (hLarge : defectScaleThreshold ≤ M) :
    112 * (Real.log (M : Real)) ^ 2 ≤ Real.sqrt (M : Real) := by
  apply log_sq_gate_of_exp40_le
  exact (Nat.le_ceil (Real.exp 40)).trans (by exact_mod_cast hLarge)

/-- Defect reserve supplied on every target of the actual even block. -/
theorem evenBlock_defect_reserve
    (M : Nat) (hScale : 112 * (Real.log (M : Real)) ^ 2 ≤ Real.sqrt (M : Real)) :
    ∀ N ∈ evenTargetBlock M, primePowerDefect N ≤ (M : Real) / 28 := by
  intro N hN
  rcases (mem_evenTargetBlock_iff M N).1 hN with ⟨h4, hNM, _, _⟩
  exact primePowerDefect_le_M_div_28 M N (by omega) hNM hScale

/-- Defect is subtracted from, not added to, the assumed raw Major reserve. -/
theorem evenBlock_net_reserve
    (M P R0 N : Nat) (hN : N ∈ evenTargetBlock M)
    (hScale : 112 * (Real.log (M : Real)) ^ 2 ≤ Real.sqrt (M : Real))
    (hMajor : (M : Real) / 14 ≤ twoScaleMajorIntegralReal M P R0 N) :
    (M : Real) / 28 ≤ twoScaleMajorIntegralReal M P R0 N - primePowerDefect N := by
  have hDefect := evenBlock_defect_reserve M hScale N hN
  linarith

/-- No independent defect premise remains; scale, Major and moment inputs are visible. -/
theorem evenBlock_exceptions_card_le_3136_of_scale_gate
    (M P R0 : Nat) (B : Real) (hM : 0 < M)
    (hScale : 112 * (Real.log (M : Real)) ^ 2 ≤ Real.sqrt (M : Real))
    (hMajor : ∀ N ∈ evenTargetBlock M,
      (M : Real) / 14 ≤ twoScaleMajorIntegralReal M P R0 N)
    (hMoment : negativePartSquaredMoment (evenTargetBlock M)
      (twoScaleMinorIntegralReal M P R0) ≤ 4 * (M : Real) ^ 2 * B) :
    (((evenTargetBlock M).filter (fun N => ¬ GoldbachAt N)).card : Real) ≤ 3136 * B := by
  apply twoScaleExceptions_card_le_3136_of_moment M P R0 (evenTargetBlock M) B hM
  · intro N hN
    exact ((mem_evenTargetBlock_iff M N).1 hN).2.1
  · exact hMajor
  · exact evenBlock_defect_reserve M hScale
  · exact hMoment

/-- Effective threshold version. Neither analytic hypothesis nor small targets are proved. -/
theorem evenBlock_exceptions_card_le_3136_of_threshold
    (M P R0 : Nat) (B : Real) (hLarge : defectScaleThreshold ≤ M)
    (hMajor : ∀ N ∈ evenTargetBlock M,
      (M : Real) / 14 ≤ twoScaleMajorIntegralReal M P R0 N)
    (hMoment : negativePartSquaredMoment (evenTargetBlock M)
      (twoScaleMinorIntegralReal M P R0) ≤ 4 * (M : Real) ^ 2 * B) :
    (((evenTargetBlock M).filter (fun N => ¬ GoldbachAt N)).card : Real) ≤ 3136 * B := by
  have hExp : Real.exp 40 ≤ (M : Real) :=
    (Nat.le_ceil (Real.exp 40)).trans (by exact_mod_cast hLarge)
  have hM : 0 < M := by exact_mod_cast (Real.exp_pos 40).trans_le hExp
  exact evenBlock_exceptions_card_le_3136_of_scale_gate M P R0 B hM
    (log_sq_gate_of_threshold_le M hLarge) hMajor hMoment

end GoldbachCircleMethodTwoScaleEvenBlockDefectReserveV1833
