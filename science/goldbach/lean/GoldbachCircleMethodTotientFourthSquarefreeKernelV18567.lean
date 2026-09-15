import GoldbachCircleMethodTotientFourthPrefixKernelReductionV18566

/-!
# Goldbach V1.8.567: squarefree reciprocal kernel

This append-only sharpening retains the squarefree information carried by the
V1.8.564 divisor image throughout the incidence transposition.  Consequently
the reciprocal kernel has the exact normal form `30^omega(d) / d^2` on its
support.  No uniform bound for the kernel sum is asserted here.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodTotientFourthSquarefreeKernelV18567

open GoldbachCircleMethodCollisionTotientFourthMomentTransferV18560
open GoldbachCircleMethodCollisionTotientRatioEnvelopeV18556
open GoldbachCircleMethodTotientFourthDivisorReindexV18564
open GoldbachCircleMethodDivisorIncidenceTranspositionV18565
open GoldbachCircleMethodTotientFourthPrefixKernelReductionV18566

noncomputable def squarefreeReciprocalTotientFourthKernel (d : ℕ) : ℝ :=
  if Squarefree d then reciprocalTotientFourthDivisorKernel d else 0

theorem squarefreeReciprocalTotientFourthKernel_nonneg (d : ℕ) :
    0 ≤ squarefreeReciprocalTotientFourthKernel d := by
  unfold squarefreeReciprocalTotientFourthKernel
  split
  · exact reciprocalTotientFourthDivisorKernel_nonneg d
  · exact le_rfl

theorem totientFourthDivisorCarrier_mem_squarefree
    {n d : ℕ} (hd : d ∈ totientFourthDivisorCarrier n) : Squarefree d := by
  rw [totientFourthDivisorCarrier, Finset.mem_image] at hd
  rcases hd with ⟨t, ht, rfl⟩
  exact totientFourthSubsetDivisor_squarefree (Finset.mem_powerset.mp ht)

theorem levelTotientRatio_pow_four_le_squarefree_divisor_incidence
    {Q n : ℕ} (hn : n ∈ Finset.Icc 1 Q) :
    levelTotientRatio n ^ 4 ≤
      ∑ d ∈ Finset.Icc 1 Q,
        if d ∣ n then
          if Squarefree d then totientFourthDivisorMajorant d else 0
        else 0 := by
  have hn0 : n ≠ 0 :=
    Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hn).1)
  calc
    levelTotientRatio n ^ 4 ≤
        ∑ d ∈ totientFourthDivisorCarrier n,
          totientFourthDivisorMajorant d :=
      levelTotientRatio_pow_four_le_divisorCarrier_sum n hn0
    _ = ∑ d ∈ totientFourthDivisorCarrier n,
          if d ∣ n then
            if Squarefree d then totientFourthDivisorMajorant d else 0
          else 0 := by
      apply Finset.sum_congr rfl
      intro d hd
      simp [totientFourthDivisorCarrier_mem_dvd hd,
        totientFourthDivisorCarrier_mem_squarefree hd]
    _ ≤ ∑ d ∈ Finset.Icc 1 Q,
          if d ∣ n then
            if Squarefree d then totientFourthDivisorMajorant d else 0
          else 0 := by
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (totientFourthDivisorCarrier_subset_Icc hn)
        (fun d _hd _hnot => by
          by_cases hdiv : d ∣ n
          · by_cases hsq : Squarefree d
            · simp [hdiv, hsq, totientFourthDivisorMajorant_nonneg d]
            · simp [hdiv, hsq]
          · simp [hdiv])

theorem totientRatioFourthMoment_le_squarefree_floor_prefix (Q : ℕ) :
    totientRatioFourthMoment Q ≤
      ∑ d ∈ Finset.Icc 1 Q,
        ((Q / d : ℕ) : ℝ) *
          (if Squarefree d then totientFourthDivisorMajorant d else 0) := by
  calc
    totientRatioFourthMoment Q =
        ∑ n ∈ Finset.Icc 1 Q, levelTotientRatio n ^ 4 := rfl
    _ ≤ ∑ n ∈ Finset.Icc 1 Q,
          ∑ d ∈ Finset.Icc 1 Q,
            if d ∣ n then
              if Squarefree d then totientFourthDivisorMajorant d else 0
            else 0 := by
      exact Finset.sum_le_sum fun n hn =>
        levelTotientRatio_pow_four_le_squarefree_divisor_incidence hn
    _ = ∑ d ∈ Finset.Icc 1 Q,
          ((Q / d : ℕ) : ℝ) *
            (if Squarefree d then totientFourthDivisorMajorant d else 0) :=
      weighted_positive_divisor_incidence_eq Q
        (fun d => if Squarefree d then totientFourthDivisorMajorant d else 0)

theorem squarefree_floor_prefix_le_Q_mul_kernel (Q : ℕ) :
    (∑ d ∈ Finset.Icc 1 Q,
      ((Q / d : ℕ) : ℝ) *
        (if Squarefree d then totientFourthDivisorMajorant d else 0)) ≤
      (Q : ℝ) *
        ∑ d ∈ Finset.Icc 1 Q,
          squarefreeReciprocalTotientFourthKernel d := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro d hd
  have hdpos : 0 < d :=
    lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hd).1
  have hfloor : ((Q / d : ℕ) : ℝ) ≤ (Q : ℝ) / (d : ℝ) :=
    Nat.cast_div_le
  by_cases hsq : Squarefree d
  · simp only [hsq, if_true]
    have hmajorant : 0 ≤ totientFourthDivisorMajorant d :=
      totientFourthDivisorMajorant_nonneg d
    calc
      ((Q / d : ℕ) : ℝ) * totientFourthDivisorMajorant d ≤
          ((Q : ℝ) / (d : ℝ)) * totientFourthDivisorMajorant d :=
        mul_le_mul_of_nonneg_right hfloor hmajorant
      _ = (Q : ℝ) * squarefreeReciprocalTotientFourthKernel d := by
        simp only [squarefreeReciprocalTotientFourthKernel, hsq, if_true,
          reciprocalTotientFourthDivisorKernel]
        ring
  · simp [squarefreeReciprocalTotientFourthKernel, hsq]

theorem squarefreeReciprocalTotientFourthKernel_eq_pow_div_sq
    {d : ℕ} (hsq : Squarefree d) :
    squarefreeReciprocalTotientFourthKernel d =
      (30 : ℝ) ^ d.primeFactors.card / (d : ℝ) ^ 2 := by
  simp only [squarefreeReciprocalTotientFourthKernel, hsq, if_true,
    reciprocalTotientFourthDivisorKernel]
  rw [totientFourthDivisorMajorant_eq_pow_div hsq]
  ring

theorem totientRatioFourthMoment_le_Q_mul_squarefree_kernel (Q : ℕ) :
    totientRatioFourthMoment Q ≤
      (Q : ℝ) *
        ∑ d ∈ Finset.Icc 1 Q,
          squarefreeReciprocalTotientFourthKernel d := by
  exact (totientRatioFourthMoment_le_squarefree_floor_prefix Q).trans
    (squarefree_floor_prefix_le_Q_mul_kernel Q)

end GoldbachCircleMethodTotientFourthSquarefreeKernelV18567
