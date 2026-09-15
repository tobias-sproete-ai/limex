import GoldbachCircleMethodExactLambdaPairSourceMeanSplitV18716
import GoldbachCircleMethodChebyshevEnergyBudgetV1889

/-!
# V1.8.719: actual Lambda-pair source mean and Chebyshev ceiling

This append-only module closes the elementary arithmetic size bound left open
by V1.8.716.  It first partitions the literal odd--odd pair box by the exact
half-sum coordinate used by `actualLambdaPairSource`.  The resulting total
source mass is then factored as the square of the odd-coordinate von Mangoldt
sum.  Finally, Mathlib's proved Chebyshev bound supplies an explicit linear
ceiling for the fixed finite source mean.

No cancellation estimate for the centered source, no denominator aggregation,
no moment estimate, no exceptional-set estimate, and no Goldbach conclusion is
proved.

`proof_status = NO_PROOF`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

open scoped BigOperators Classical ArithmeticFunction.vonMangoldt

namespace GoldbachCircleMethodActualLambdaPairSourceMeanChebyshevBoundV18719

open GoldbachCircleMethodActualOneSidedKernelLeakageV18648
open GoldbachCircleMethodOddOddSignedFiberAdapterV18665
open GoldbachCircleMethodOddOddFourierBesselBridgeV18668
open GoldbachCircleMethodExactLambdaPairSourceMeanSplitV18716
open GoldbachCircleMethodChebyshevEnergyBudgetV1889

/-- Public spelling of the literal odd--odd pair carrier hidden inside the
fiber implementation. -/
def actualOddOddPairCarrier (M : Nat) : Finset (Nat × Nat) :=
  (oddCarrier M).product (oddCarrier M)

/-- The half-sum coordinate of an odd--odd pair. -/
def oddOddHalfSum (ab : Nat × Nat) : Nat :=
  (ab.1 + ab.2) / 2

/-- Every pair in the literal odd--odd box maps into the defining source
coordinate `Finset.range M.succ`. -/
theorem oddOddHalfSum_mem_range
    (M : Nat) (ab : Nat × Nat)
    (hab : ab ∈ actualOddOddPairCarrier M) :
    oddOddHalfSum ab ∈ Finset.range M.succ := by
  rcases Finset.mem_product.mp hab with ⟨ha, hb⟩
  have haM : ab.1 ≤ M := by
    exact Nat.le_of_lt_succ
      (Finset.mem_range.mp (Finset.mem_filter.mp ha).1)
  have hbM : ab.2 ≤ M := by
    exact Nat.le_of_lt_succ
      (Finset.mem_range.mp (Finset.mem_filter.mp hb).1)
  unfold oddOddHalfSum
  rw [Finset.mem_range]
  omega

/-- On the odd--odd carrier, equality of half-sums is exactly equality to the
doubled source coordinate. -/
theorem oddOddHalfSum_eq_iff_sum_eq_two_mul
    (M a : Nat) (ab : Nat × Nat)
    (hab : ab ∈ actualOddOddPairCarrier M) :
    oddOddHalfSum ab = a ↔ ab.1 + ab.2 = 2 * a := by
  rcases Finset.mem_product.mp hab with ⟨ha, hb⟩
  have haOdd : Odd ab.1 := (Finset.mem_filter.mp ha).2
  have hbOdd : Odd ab.2 := (Finset.mem_filter.mp hb).2
  rcases haOdd with ⟨u, hu⟩
  rcases hbOdd with ⟨v, hv⟩
  unfold oddOddHalfSum
  omega

/-- Exact finite partition of the actual source fibers back into the literal
odd--odd Lambda-pair carrier. -/
theorem sum_actualLambdaPairSource_eq_sum_actualOddOddPairCarrier
    (M : Nat) :
    (∑ a ∈ Finset.range M.succ, actualLambdaPairSource M a) =
      ∑ ab ∈ actualOddOddPairCarrier M, lambdaPairWeight ab := by
  classical
  have hpartition :
      (∑ a ∈ Finset.range M.succ,
          ∑ ab ∈ actualOddOddPairCarrier M with oddOddHalfSum ab = a,
            lambdaPairWeight ab) =
        ∑ ab ∈ actualOddOddPairCarrier M, lambdaPairWeight ab :=
    Finset.sum_fiberwise_of_maps_to
      (fun ab hab => oddOddHalfSum_mem_range M ab hab)
      lambdaPairWeight
  rw [← hpartition]
  apply Finset.sum_congr rfl
  intro a _ha
  unfold actualLambdaPairSource
  change
    (∑ ab ∈
        (((Finset.range M.succ).product (Finset.range M.succ)).filter
          (fun ab => Odd ab.1 ∧ Odd ab.2)) with
        ab.1 + ab.2 = 2 * a, lambdaPairWeight ab) =
      ∑ ab ∈ actualOddOddPairCarrier M with oddOddHalfSum ab = a,
        lambdaPairWeight ab
  apply Finset.sum_congr
  · ext ab
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨⟨habBox, habOdd⟩, hsum⟩
      have habPublic : ab ∈ actualOddOddPairCarrier M := by
        rcases Finset.mem_product.mp habBox with ⟨ha, hb⟩
        exact Finset.mem_product.mpr
          ⟨Finset.mem_filter.mpr ⟨ha, habOdd.1⟩,
            Finset.mem_filter.mpr ⟨hb, habOdd.2⟩⟩
      exact ⟨habPublic,
        (oddOddHalfSum_eq_iff_sum_eq_two_mul M a ab habPublic).2 hsum⟩
    · rintro ⟨habPublic, hhalf⟩
      rcases Finset.mem_product.mp habPublic with ⟨ha, hb⟩
      rcases Finset.mem_filter.mp ha with ⟨haRange, haOdd⟩
      rcases Finset.mem_filter.mp hb with ⟨hbRange, hbOdd⟩
      exact ⟨⟨Finset.mem_product.mpr ⟨haRange, hbRange⟩,
          ⟨haOdd, hbOdd⟩⟩,
        (oddOddHalfSum_eq_iff_sum_eq_two_mul M a ab habPublic).1 hhalf⟩
  · intro ab _hab
    rfl

/-- Exact one-coordinate odd von Mangoldt mass. -/
noncomputable def oddLambdaSum (M : Nat) : Real :=
  ∑ n ∈ oddCarrier M, ArithmeticFunction.vonMangoldt n

/-- The total literal odd--odd pair mass factors exactly as a square. -/
theorem sum_actualOddOddPairCarrier_eq_oddLambdaSum_sq (M : Nat) :
    (∑ ab ∈ actualOddOddPairCarrier M, lambdaPairWeight ab) =
      (oddLambdaSum M) ^ 2 := by
  unfold actualOddOddPairCarrier oddLambdaSum lambdaPairWeight
  rw [Finset.product_eq_sprod, Finset.sum_product]
  rw [pow_two, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _ha
  rw [Finset.mul_sum]

/-- Exact source-mass identity: summing the actual fibers gives the square of
the odd-coordinate von Mangoldt mass. -/
theorem sum_actualLambdaPairSource_eq_oddLambdaSum_sq (M : Nat) :
    (∑ a ∈ Finset.range M.succ, actualLambdaPairSource M a) =
      (oddLambdaSum M) ^ 2 := by
  rw [sum_actualLambdaPairSource_eq_sum_actualOddOddPairCarrier,
    sum_actualOddOddPairCarrier_eq_oddLambdaSum_sq]

/-- The standard full finite von Mangoldt sum is Mathlib's Chebyshev `psi` at
the natural endpoint. -/
theorem lambdaSum_range_succ_eq_psi (M : Nat) :
    (∑ n ∈ Finset.range M.succ, ArithmeticFunction.vonMangoldt n) =
      Chebyshev.psi (M : Real) := by
  rw [Chebyshev.psi_eq_sum_Icc, Nat.floor_natCast]
  congr 1
  ext n
  simp

/-- Dropping the even coordinates cannot increase the nonnegative full
von Mangoldt mass. -/
theorem oddLambdaSum_le_psi (M : Nat) :
    oddLambdaSum M ≤ Chebyshev.psi (M : Real) := by
  rw [← lambdaSum_range_succ_eq_psi]
  unfold oddLambdaSum oddCarrier
  rw [Finset.sum_filter]
  apply Finset.sum_le_sum
  intro n _hn
  split_ifs
  · exact le_rfl
  · exact ArithmeticFunction.vonMangoldt_nonneg

/-- Mathlib's proved Chebyshev theorem yields an explicit linear ceiling for
the odd-coordinate von Mangoldt mass. -/
theorem oddLambdaSum_le_chebyshev_linear (M : Nat) :
    oddLambdaSum M ≤ chebyshevConstant * (M : Real) := by
  exact (oddLambdaSum_le_psi M).trans
    (Chebyshev.psi_le_const_mul_self (Nat.cast_nonneg M))

theorem oddLambdaSum_nonneg (M : Nat) :
    0 ≤ oddLambdaSum M := by
  unfold oddLambdaSum
  exact Finset.sum_nonneg fun n _hn => ArithmeticFunction.vonMangoldt_nonneg

/-- Explicit linear ceiling for the definitionally fixed source mean.  This
is a size estimate only; it supplies no oscillatory cancellation. -/
theorem actualLambdaPairSourceMean_le_chebyshev_linear (M : Nat) :
    actualLambdaPairSourceMean M ≤
      chebyshevConstant ^ 2 * (M : Real) := by
  have hsum := oddLambdaSum_le_chebyshev_linear M
  have hsum0 := oddLambdaSum_nonneg M
  have hC0 : 0 ≤ chebyshevConstant := chebyshevConstant_pos.le
  have hM0 : 0 ≤ (M : Real) := Nat.cast_nonneg M
  have hsq : (oddLambdaSum M) ^ 2 ≤
      (chebyshevConstant * (M : Real)) ^ 2 := by
    nlinarith
  have hden : 0 < (M.succ : Real) := by positivity
  unfold actualLambdaPairSourceMean
  rw [sum_actualLambdaPairSource_eq_oddLambdaSum_sq]
  apply (div_le_iff₀ hden).2
  have hMM : (M : Real) ^ 2 ≤ (M : Real) * (M.succ : Real) := by
    norm_num
    nlinarith
  have hscaled := mul_le_mul_of_nonneg_left hMM
    (sq_nonneg chebyshevConstant)
  calc
    (oddLambdaSum M) ^ 2 ≤
        (chebyshevConstant * (M : Real)) ^ 2 := hsq
    _ = chebyshevConstant ^ 2 * (M : Real) ^ 2 := by ring
    _ ≤ chebyshevConstant ^ 2 * ((M : Real) * (M.succ : Real)) := hscaled
    _ = chebyshevConstant ^ 2 * (M : Real) * (M.succ : Real) := by ring

end GoldbachCircleMethodActualLambdaPairSourceMeanChebyshevBoundV18719
