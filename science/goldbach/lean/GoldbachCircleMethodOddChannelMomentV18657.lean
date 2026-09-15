import GoldbachCircleMethodOddChannelCompositionV18656

/-!
# V1.8.657: finite squared-moment bound for the odd channel

This append-only module squares and sums the exact V1.8.656 pointwise odd
channel bound on the unchanged even target block.  The harmful positive part
of `negativeOdd-positiveOdd` is bounded directly by the nonnegative negative
odd mass, so no factor two is introduced.

The even channel is not estimated. `proof_status = NO_PROOF`.
-/
set_option autoImplicit false

open scoped BigOperators Classical
open GoldbachCircleMethodExceptionalTransferV1823
open GoldbachCircleMethodTwoScaleEvenBlockDefectReserveV1833
open GoldbachCircleMethodExplicitOffDiagonalKernelLeakageV18649
open GoldbachCircleMethodExplicitJordanParitySplitV18652
open GoldbachCircleMethodOddChannelCompositionV18656

namespace GoldbachCircleMethodOddChannelMomentV18657

/-- The unchanged even target block contains at most `M` indices. -/
theorem evenTargetBlock_card_le (M : Nat) :
    (evenTargetBlock M).card ≤ M := by
  unfold evenTargetBlock
  calc
    (((Finset.Icc 4 M).filter (fun N => Even N ∧ M ≤ 2 * N)).card) ≤
        (Finset.Icc 4 M).card := Finset.card_filter_le _ _
    _ = M + 1 - 4 := Nat.card_Icc 4 M
    _ ≤ M := by omega

/-- Finite positive-part square moment of the explicit odd deficit. -/
noncomputable def explicitOddChannelPositivePartSquaredMoment
    (M P R : Nat) (s : Finset Nat) : Real :=
  ∑ N ∈ s, (positivePart (explicitOddChannelDeficit M P R N)) ^ 2

/-- The harmful positive part of the odd deficit is controlled by the
negative odd mass alone; the positive odd mass can only reduce it. -/
theorem positivePart_explicitOddChannelDeficit_le
    {M P R N : Nat} (hM2 : 2 ≤ M) (hEven : Even N) (hNM : N ≤ M)
    (hP : 0 < P) (hscale : 2 * P * R < M) :
    positivePart (explicitOddChannelDeficit M P R N) ≤
      32 * (P : Real) * (R : Real) * Real.sqrt (R : Real) *
        Real.log ((2 * M : Nat) : Real) ^ 2 := by
  unfold explicitOddChannelDeficit positivePart
  apply max_le
  · have hPositive := explicitPositiveOddSumMass_nonneg M P R N
    have hNegative := explicitNegativeOddSumMass_le hM2 hEven hNM hP hscale
    linarith
  · positivity

/-- Termwise squaring and summation on any finite even carrier. -/
theorem explicitOddChannelPositivePartSquaredMoment_le_card_mul
    {M P R : Nat} (s : Finset Nat)
    (hM2 : 2 ≤ M)
    (hEven : ∀ N ∈ s, Even N)
    (hNM : ∀ N ∈ s, N ≤ M)
    (hP : 0 < P) (hscale : 2 * P * R < M) :
    explicitOddChannelPositivePartSquaredMoment M P R s ≤
      (s.card : Real) *
        (32 * (P : Real) * (R : Real) * Real.sqrt (R : Real) *
          Real.log ((2 * M : Nat) : Real) ^ 2) ^ 2 := by
  unfold explicitOddChannelPositivePartSquaredMoment
  calc
    (∑ N ∈ s, (positivePart (explicitOddChannelDeficit M P R N)) ^ 2) ≤
        ∑ _N ∈ s,
          (32 * (P : Real) * (R : Real) * Real.sqrt (R : Real) *
            Real.log ((2 * M : Nat) : Real) ^ 2) ^ 2 := by
      apply Finset.sum_le_sum
      intro N hN
      have hpoint := positivePart_explicitOddChannelDeficit_le
        hM2 (hEven N hN) (hNM N hN) hP hscale
      have hleft : 0 ≤ positivePart (explicitOddChannelDeficit M P R N) :=
        positivePart_nonneg _
      have hright :
          0 ≤ 32 * (P : Real) * (R : Real) * Real.sqrt (R : Real) *
            Real.log ((2 * M : Nat) : Real) ^ 2 := by positivity
      nlinarith
    _ = (s.card : Real) *
        (32 * (P : Real) * (R : Real) * Real.sqrt (R : Real) *
          Real.log ((2 * M : Nat) : Real) ^ 2) ^ 2 := by simp

/-- Specialization to the unchanged project target block. -/
theorem explicitOddChannelPositivePartSquaredMoment_evenTargetBlock_le
    {M P R : Nat} (hM2 : 2 ≤ M) (hP : 0 < P)
    (hscale : 2 * P * R < M) :
    explicitOddChannelPositivePartSquaredMoment M P R (evenTargetBlock M) ≤
      (M : Real) *
        (32 * (P : Real) * (R : Real) * Real.sqrt (R : Real) *
          Real.log ((2 * M : Nat) : Real) ^ 2) ^ 2 := by
  have hMoment := explicitOddChannelPositivePartSquaredMoment_le_card_mul
    (evenTargetBlock M) hM2
    (fun N hN => ((mem_evenTargetBlock_iff M N).1 hN).2.2.1)
    (fun N hN => ((mem_evenTargetBlock_iff M N).1 hN).2.1)
    hP hscale
  have hCard : ((evenTargetBlock M).card : Real) ≤ (M : Real) := by
    exact_mod_cast evenTargetBlock_card_le M
  exact hMoment.trans (mul_le_mul_of_nonneg_right hCard (sq_nonneg _))

/-- The negative part of the negated odd deficit is definitionally the
positive part used above. -/
theorem negativePartSquaredMoment_neg_explicitOddChannelDeficit_eq
    (M P R : Nat) (s : Finset Nat) :
    negativePartSquaredMoment s
        (fun N => -explicitOddChannelDeficit M P R N) =
      explicitOddChannelPositivePartSquaredMoment M P R s := by
  unfold negativePartSquaredMoment explicitOddChannelPositivePartSquaredMoment
  apply Finset.sum_congr rfl
  intro N _hN
  rw [negativePart_neg_eq_positivePart]

/-- Exact simplification of the squared pointwise budget. -/
theorem oddChannelPointwiseBudget_sq_eq (M P R : Nat) :
    (32 * (P : Real) * (R : Real) * Real.sqrt (R : Real) *
        Real.log ((2 * M : Nat) : Real) ^ 2) ^ 2 =
      1024 * (P : Real) ^ 2 * (R : Real) ^ 3 *
        Real.log ((2 * M : Nat) : Real) ^ 4 := by
  have hsqrt : (Real.sqrt (R : Real)) ^ 2 = (R : Real) :=
    Real.sq_sqrt (Nat.cast_nonneg R)
  calc
    _ = 1024 * (P : Real) ^ 2 * (R : Real) ^ 2 *
        (Real.sqrt (R : Real)) ^ 2 *
          Real.log ((2 * M : Nat) : Real) ^ 4 := by ring
    _ = _ := by rw [hsqrt]; ring

/-- Final finite V1.8.657 bound in explicit project normalization. -/
theorem negativePartSquaredMoment_neg_oddChannelDeficit_evenTargetBlock_le
    {M P R : Nat} (hM2 : 2 ≤ M) (hP : 0 < P)
    (hscale : 2 * P * R < M) :
    negativePartSquaredMoment (evenTargetBlock M)
        (fun N => -explicitOddChannelDeficit M P R N) ≤
      1024 * (M : Real) * (P : Real) ^ 2 * (R : Real) ^ 3 *
        Real.log ((2 * M : Nat) : Real) ^ 4 := by
  rw [negativePartSquaredMoment_neg_explicitOddChannelDeficit_eq]
  calc
    explicitOddChannelPositivePartSquaredMoment M P R (evenTargetBlock M) ≤
        (M : Real) *
          (32 * (P : Real) * (R : Real) * Real.sqrt (R : Real) *
            Real.log ((2 * M : Nat) : Real) ^ 2) ^ 2 :=
      explicitOddChannelPositivePartSquaredMoment_evenTargetBlock_le
        hM2 hP hscale
    _ = 1024 * (M : Real) * (P : Real) ^ 2 * (R : Real) ^ 3 *
        Real.log ((2 * M : Nat) : Real) ^ 4 := by
      rw [oddChannelPointwiseBudget_sq_eq]
      ring

end GoldbachCircleMethodOddChannelMomentV18657
