import GoldbachCircleMethodDivisorIncidenceTranspositionV18565

/-!
# Goldbach V1.8.566: reduction of the fourth totient moment to a reciprocal divisor kernel

The exact incidence identity from V1.8.565 is applied to the V1.8.564
divisor majorant.  The full fourth totient moment is bounded by `Q` times a
finite reciprocal-divisor kernel prefix.  Uniform boundedness of that kernel
prefix remains a separate open gate.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodTotientFourthPrefixKernelReductionV18566

open GoldbachCircleMethodCollisionTotientRatioEnvelopeV18556
open GoldbachCircleMethodCollisionTotientFourthMomentTransferV18560
open GoldbachCircleMethodTotientFourthDivisorReindexV18564
open GoldbachCircleMethodDivisorIncidenceTranspositionV18565

noncomputable def reciprocalTotientFourthDivisorKernel (d : ℕ) : ℝ :=
  totientFourthDivisorMajorant d / (d : ℝ)

theorem reciprocalTotientFourthDivisorKernel_nonneg (d : ℕ) :
    0 ≤ reciprocalTotientFourthDivisorKernel d := by
  unfold reciprocalTotientFourthDivisorKernel
  exact div_nonneg (totientFourthDivisorMajorant_nonneg d)
    (Nat.cast_nonneg d)

/-- The pointwise V1.8.564 divisor carrier embeds into the full divisor
incidence relation on the same positive prefix. -/
theorem levelTotientRatio_pow_four_le_full_divisor_incidence
    {Q n : ℕ} (hn : n ∈ Finset.Icc 1 Q) :
    levelTotientRatio n ^ 4 ≤
      ∑ d ∈ Finset.Icc 1 Q,
        if d ∣ n then totientFourthDivisorMajorant d else 0 := by
  have hn0 : n ≠ 0 :=
    Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hn).1)
  calc
    levelTotientRatio n ^ 4 ≤
        ∑ d ∈ totientFourthDivisorCarrier n,
          totientFourthDivisorMajorant d :=
      levelTotientRatio_pow_four_le_divisorCarrier_sum n hn0
    _ = ∑ d ∈ totientFourthDivisorCarrier n,
          if d ∣ n then totientFourthDivisorMajorant d else 0 := by
      apply Finset.sum_congr rfl
      intro d hd
      simp [totientFourthDivisorCarrier_mem_dvd hd]
    _ ≤ ∑ d ∈ Finset.Icc 1 Q,
          if d ∣ n then totientFourthDivisorMajorant d else 0 := by
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (totientFourthDivisorCarrier_subset_Icc hn)
        (fun d _hd _hnot => by
          by_cases hdiv : d ∣ n
          · simp [hdiv, totientFourthDivisorMajorant_nonneg d]
          · simp [hdiv])

/-- Exact finite reduction of the fourth totient moment to the floor-weighted
divisor prefix. -/
theorem totientRatioFourthMoment_le_floor_divisor_prefix (Q : ℕ) :
    totientRatioFourthMoment Q ≤
      ∑ d ∈ Finset.Icc 1 Q,
        ((Q / d : ℕ) : ℝ) * totientFourthDivisorMajorant d := by
  calc
    totientRatioFourthMoment Q =
        ∑ n ∈ Finset.Icc 1 Q, levelTotientRatio n ^ 4 := rfl
    _ ≤ ∑ n ∈ Finset.Icc 1 Q,
          ∑ d ∈ Finset.Icc 1 Q,
            if d ∣ n then totientFourthDivisorMajorant d else 0 := by
      exact Finset.sum_le_sum fun n hn =>
        levelTotientRatio_pow_four_le_full_divisor_incidence hn
    _ = ∑ d ∈ Finset.Icc 1 Q,
          ((Q / d : ℕ) : ℝ) * totientFourthDivisorMajorant d :=
      weighted_positive_divisor_incidence_eq Q totientFourthDivisorMajorant

/-- The floor multiplicity is bounded by the real quotient, exposing the
reciprocal divisor kernel with no asymptotic notation. -/
theorem floor_divisor_prefix_le_Q_mul_reciprocal_kernel (Q : ℕ) :
    (∑ d ∈ Finset.Icc 1 Q,
      ((Q / d : ℕ) : ℝ) * totientFourthDivisorMajorant d) ≤
      (Q : ℝ) *
        ∑ d ∈ Finset.Icc 1 Q, reciprocalTotientFourthDivisorKernel d := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro d hd
  have hdpos : 0 < d :=
    lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hd).1
  have hfloor : ((Q / d : ℕ) : ℝ) ≤ (Q : ℝ) / (d : ℝ) :=
    Nat.cast_div_le
  have hmajorant : 0 ≤ totientFourthDivisorMajorant d :=
    totientFourthDivisorMajorant_nonneg d
  calc
    ((Q / d : ℕ) : ℝ) * totientFourthDivisorMajorant d ≤
        ((Q : ℝ) / (d : ℝ)) * totientFourthDivisorMajorant d :=
      mul_le_mul_of_nonneg_right hfloor hmajorant
    _ = (Q : ℝ) * reciprocalTotientFourthDivisorKernel d := by
      unfold reciprocalTotientFourthDivisorKernel
      ring

/-- Main finite reduction: only uniform boundedness of the displayed kernel
prefix remains. -/
theorem totientRatioFourthMoment_le_Q_mul_reciprocal_kernel (Q : ℕ) :
    totientRatioFourthMoment Q ≤
      (Q : ℝ) *
        ∑ d ∈ Finset.Icc 1 Q, reciprocalTotientFourthDivisorKernel d := by
  exact (totientRatioFourthMoment_le_floor_divisor_prefix Q).trans
    (floor_divisor_prefix_le_Q_mul_reciprocal_kernel Q)

end GoldbachCircleMethodTotientFourthPrefixKernelReductionV18566
