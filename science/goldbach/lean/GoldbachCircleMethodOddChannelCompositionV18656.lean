import GoldbachCircleMethodOddKernelL1V18655

/-!
# V1.8.656: composition of the odd pair fibers with the literal kernel L1 bound

This append-only module groups the unchanged V1.8.652 odd pair carrier by the
literal sum `t=a+b`, applies V1.8.653 to each fiber, and transports the shift
`k=N-t` injectively into the unchanged odd part of `shiftCarrier (2*M)`.

The even channel is not estimated. `proof_status = NO_PROOF`.
-/
set_option autoImplicit false

open scoped BigOperators Classical
open GoldbachCircleMethodSignedWindowFourierAdapterV18130
open GoldbachCircleMethodActualOneSidedKernelLeakageV18648
open GoldbachCircleMethodExplicitOffDiagonalKernelLeakageV18649
open GoldbachCircleMethodExplicitJordanParitySplitV18652
open GoldbachCircleMethodOddPairFiberAdapterV18653
open GoldbachCircleMethodOddKernelL1V18655

namespace GoldbachCircleMethodOddChannelCompositionV18656

private def oddPairCarrier (M : Nat) : Finset (Nat × Nat) :=
  ((Finset.range M.succ).product (Finset.range M.succ)).filter
    (fun ab => Odd (ab.1 + ab.2))

private def oddSumCarrier (M : Nat) : Finset Nat :=
  (Finset.range (2 * M + 1)).filter Odd

theorem oddPairCarrier_maps_to_oddSumCarrier (M : Nat) :
    ∀ ab ∈ oddPairCarrier M, ab.1 + ab.2 ∈ oddSumCarrier M := by
  intro ab hab
  rcases Finset.mem_filter.mp hab with ⟨habProduct, hOdd⟩
  rcases Finset.mem_product.mp habProduct with ⟨ha, hb⟩
  apply Finset.mem_filter.mpr
  constructor
  · apply Finset.mem_range.mpr
    rw [Finset.mem_range] at ha hb
    omega
  · exact hOdd

theorem oddPairFiberMass_eq_truncatedLambdaPairMass
    (M t : Nat) (htOdd : Odd t) :
    (∑ ab ∈ oddPairCarrier M with ab.1 + ab.2 = t,
      lambdaPairWeight ab) = truncatedLambdaPairMass M t := by
  classical
  unfold oddPairCarrier truncatedLambdaPairMass
  change
    (∑ ab ∈
      (((Finset.range M.succ).product (Finset.range M.succ)).filter
        (fun ab => Odd (ab.1 + ab.2))).filter
          (fun ab => ab.1 + ab.2 = t), lambdaPairWeight ab) =
      ∑ ab ∈
        ((Finset.range M.succ).product (Finset.range M.succ)).filter
          (fun ab => ab.1 + ab.2 = t), lambdaPairWeight ab
  apply Finset.sum_congr
  · ext ab
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨⟨hab, _hOdd⟩, habt⟩
      exact ⟨hab, habt⟩
    · rintro ⟨hab, habt⟩
      exact ⟨⟨hab, habt ▸ htOdd⟩, habt⟩
  · intro ab _hab
    rfl

/-- The literal odd-pair carrier weighted by the norm of the unchanged
explicit Major-mask coefficient at the target shift `N-a-b`. -/
noncomputable def explicitOddAbsoluteKernelMass
    (M P R N : Nat) : Real :=
  ∑ ab ∈ oddPairCarrier M,
    lambdaPairWeight ab *
      ‖explicitMajorMaskSincKernel M P R
        ((N : Int) - (ab.1 : Int) - (ab.2 : Int))‖

set_option maxHeartbeats 800000 in
/-- Exact regrouping of the odd pair carrier by `t=a+b`. -/
theorem explicitOddAbsoluteKernelMass_eq_sum_fibers
    (M P R N : Nat) :
    explicitOddAbsoluteKernelMass M P R N =
      ∑ t ∈ oddSumCarrier M,
        truncatedLambdaPairMass M t *
          ‖explicitMajorMaskSincKernel M P R ((N : Int) - (t : Int))‖ := by
  classical
  have hFiber :
      (∑ t ∈ oddSumCarrier M,
        ∑ ab ∈ oddPairCarrier M with ab.1 + ab.2 = t,
          lambdaPairWeight ab *
            ‖explicitMajorMaskSincKernel M P R
              ((N : Int) - (ab.1 : Int) - (ab.2 : Int))‖) =
        ∑ ab ∈ oddPairCarrier M,
          lambdaPairWeight ab *
            ‖explicitMajorMaskSincKernel M P R
              ((N : Int) - (ab.1 : Int) - (ab.2 : Int))‖ :=
    Finset.sum_fiberwise_of_maps_to
      (oddPairCarrier_maps_to_oddSumCarrier M)
      (fun ab : Nat × Nat =>
        lambdaPairWeight ab *
          ‖explicitMajorMaskSincKernel M P R
            ((N : Int) - (ab.1 : Int) - (ab.2 : Int))‖)
  unfold explicitOddAbsoluteKernelMass
  rw [← hFiber]
  apply Finset.sum_congr rfl
  intro t ht
  have htOdd : Odd t := (Finset.mem_filter.mp ht).2
  rw [← oddPairFiberMass_eq_truncatedLambdaPairMass M t htOdd]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro ab hab
  have habt : ab.1 + ab.2 = t := (Finset.mem_filter.mp hab).2
  have hshift :
      (N : Int) - (ab.1 : Int) - (ab.2 : Int) =
        (N : Int) - (t : Int) := by
    have habtInt : (ab.1 : Int) + (ab.2 : Int) = (t : Int) := by
      exact_mod_cast habt
    omega
  rw [hshift]

/-- The positive off-diagonal odd mass is bounded by the literal absolute
odd-kernel mass. -/
theorem explicitPositiveOddSumMass_le_absolute
    (M P R N : Nat) :
    explicitPositiveOddSumMass M P R N ≤
      explicitOddAbsoluteKernelMass M P R N := by
  classical
  unfold explicitPositiveOddSumMass explicitOddAbsoluteKernelMass
  change
    (∑ ab ∈
      (((Finset.range M.succ).product (Finset.range M.succ)).filter
        (fun ab => ab.1 + ab.2 ≠ N)).filter
          (fun ab => Odd (ab.1 + ab.2)),
      lambdaPairWeight ab *
        GoldbachCircleMethodExceptionalTransferV1823.negativePart
          (explicitMajorMaskSincKernel M P R
            ((N : Int) - (ab.1 : Int) - (ab.2 : Int))).re) ≤
      ∑ ab ∈ oddPairCarrier M,
        lambdaPairWeight ab *
          ‖explicitMajorMaskSincKernel M P R
            ((N : Int) - (ab.1 : Int) - (ab.2 : Int))‖
  let restricted :=
    (((Finset.range M.succ).product (Finset.range M.succ)).filter
      (fun ab : Nat × Nat => ab.1 + ab.2 ≠ N)).filter
        (fun ab => Odd (ab.1 + ab.2))
  calc
    _ ≤ ∑ ab ∈ restricted,
        lambdaPairWeight ab *
          ‖explicitMajorMaskSincKernel M P R
            ((N : Int) - (ab.1 : Int) - (ab.2 : Int))‖ := by
      apply Finset.sum_le_sum
      intro ab _hab
      apply mul_le_mul_of_nonneg_left _ (lambdaPairWeight_nonneg ab)
      unfold GoldbachCircleMethodExceptionalTransferV1823.negativePart
      exact max_le
        ((neg_le_abs _).trans (Complex.abs_re_le_norm _)) (norm_nonneg _)
    _ ≤ ∑ ab ∈ oddPairCarrier M,
        lambdaPairWeight ab *
          ‖explicitMajorMaskSincKernel M P R
            ((N : Int) - (ab.1 : Int) - (ab.2 : Int))‖ := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro ab hab
        rcases Finset.mem_filter.mp hab with ⟨hoff, hOdd⟩
        exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hoff).1, hOdd⟩
      · intro ab _hab _hnot
        exact mul_nonneg (lambdaPairWeight_nonneg ab) (norm_nonneg _)

/-- The negative odd mass is bounded by the same literal absolute envelope. -/
theorem explicitNegativeOddSumMass_le_absolute
    (M P R N : Nat) :
    explicitNegativeOddSumMass M P R N ≤
      explicitOddAbsoluteKernelMass M P R N := by
  classical
  unfold explicitNegativeOddSumMass explicitOddAbsoluteKernelMass
  change
    (∑ ab ∈
      (((Finset.range M.succ).product (Finset.range M.succ)).filter
        (fun ab => ab.1 + ab.2 ≠ N)).filter
          (fun ab => Odd (ab.1 + ab.2)),
      lambdaPairWeight ab *
        positivePart
          (explicitMajorMaskSincKernel M P R
            ((N : Int) - (ab.1 : Int) - (ab.2 : Int))).re) ≤
      ∑ ab ∈ oddPairCarrier M,
        lambdaPairWeight ab *
          ‖explicitMajorMaskSincKernel M P R
            ((N : Int) - (ab.1 : Int) - (ab.2 : Int))‖
  let restricted :=
    (((Finset.range M.succ).product (Finset.range M.succ)).filter
      (fun ab : Nat × Nat => ab.1 + ab.2 ≠ N)).filter
        (fun ab => Odd (ab.1 + ab.2))
  calc
    _ ≤ ∑ ab ∈ restricted,
        lambdaPairWeight ab *
          ‖explicitMajorMaskSincKernel M P R
            ((N : Int) - (ab.1 : Int) - (ab.2 : Int))‖ := by
      apply Finset.sum_le_sum
      intro ab _hab
      apply mul_le_mul_of_nonneg_left _ (lambdaPairWeight_nonneg ab)
      unfold positivePart
      exact max_le
        ((le_abs_self _).trans (Complex.abs_re_le_norm _)) (norm_nonneg _)
    _ ≤ ∑ ab ∈ oddPairCarrier M,
        lambdaPairWeight ab *
          ‖explicitMajorMaskSincKernel M P R
            ((N : Int) - (ab.1 : Int) - (ab.2 : Int))‖ := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro ab hab
        rcases Finset.mem_filter.mp hab with ⟨hoff, hOdd⟩
        exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hoff).1, hOdd⟩
      · intro ab _hab _hnot
        exact mul_nonneg (lambdaPairWeight_nonneg ab) (norm_nonneg _)

/-- The injective literal target-shift map `t ↦ N-t`. -/
private def targetShiftEmbedding (N : Nat) : Nat ↪ Int where
  toFun t := (N : Int) - (t : Int)
  inj' := by
    intro a b hab
    change (N : Int) - (a : Int) = (N : Int) - (b : Int) at hab
    exact Int.ofNat_inj.mp (sub_right_inj.mp hab)

/-- The mapped odd sum carrier under the literal target shift `N-t`. -/
private noncomputable def oddTargetShiftCarrier (M N : Nat) : Finset Int :=
  (oddSumCarrier M).map (targetShiftEmbedding N)

theorem oddSumKernelNorm_eq_targetShiftKernelNorm
    (M P R N : Nat) :
    (∑ t ∈ oddSumCarrier M,
      ‖explicitMajorMaskSincKernel M P R ((N : Int) - (t : Int))‖) =
      ∑ k ∈ oddTargetShiftCarrier M N,
        ‖explicitMajorMaskSincKernel M P R k‖ := by
  classical
  unfold oddTargetShiftCarrier
  rw [Finset.sum_map]
  rfl

theorem oddTargetShiftCarrier_subset_oddShiftCarrier
    {M N : Nat} (hEven : Even N) (hNM : N ≤ M) :
    oddTargetShiftCarrier M N ⊆
      (shiftCarrier (2 * (M : Real))).filter (fun k => Odd k) := by
  intro k hk
  unfold oddTargetShiftCarrier at hk
  rcases Finset.mem_map.mp hk with ⟨t, ht, rfl⟩
  have htData := Finset.mem_filter.mp ht
  have htRange : t < 2 * M + 1 := Finset.mem_range.mp htData.1
  have htLe : t ≤ 2 * M := by omega
  have hEvenInt : Even (N : Int) := by exact_mod_cast hEven
  have hOddInt : Odd (t : Int) := by exact_mod_cast htData.2
  apply Finset.mem_filter.mpr
  constructor
  · rw [mem_shift_carrier (2 * (M : Real)) (by positivity)]
    have hNReal : (N : Real) ≤ (M : Real) := by exact_mod_cast hNM
    have htReal : (t : Real) ≤ 2 * (M : Real) := by exact_mod_cast htLe
    have hcast :
        (((targetShiftEmbedding N) t : Int) : Real) =
          (N : Real) - (t : Real) := by
      change (((N : Int) - (t : Int) : Int) : Real) =
        (N : Real) - (t : Real)
      norm_num
    rw [hcast]
    rw [abs_le]
    constructor <;> linarith
  · change Odd ((N : Int) - (t : Int))
    exact hEvenInt.sub_odd hOddInt

/-- The two already kernelized odd estimates compose on the exact project
carrier.  This is a pointwise bound for the absolute odd channel only. -/
theorem explicitOddAbsoluteKernelMass_le
    {M P R N : Nat} (hM2 : 2 ≤ M) (hEven : Even N) (hNM : N ≤ M)
    (hP : 0 < P) (hscale : 2 * P * R < M) :
    explicitOddAbsoluteKernelMass M P R N ≤
      32 * (P : Real) * (R : Real) * Real.sqrt (R : Real) *
        Real.log ((2 * M : Nat) : Real) ^ 2 := by
  rw [explicitOddAbsoluteKernelMass_eq_sum_fibers]
  have hlog : 0 ≤ 2 * Real.log ((2 * M : Nat) : Real) ^ 2 := by positivity
  calc
    (∑ t ∈ oddSumCarrier M,
        truncatedLambdaPairMass M t *
          ‖explicitMajorMaskSincKernel M P R ((N : Int) - (t : Int))‖) ≤
      ∑ t ∈ oddSumCarrier M,
        (2 * Real.log ((2 * M : Nat) : Real) ^ 2) *
          ‖explicitMajorMaskSincKernel M P R ((N : Int) - (t : Int))‖ := by
      apply Finset.sum_le_sum
      intro t ht
      have htData := Finset.mem_filter.mp ht
      have htLe : t ≤ 2 * M := by
        have := Finset.mem_range.mp htData.1
        omega
      exact mul_le_mul_of_nonneg_right
        (truncatedLambdaPairMass_odd_le_two_log_sq hM2 htData.2 htLe)
        (norm_nonneg _)
    _ = (2 * Real.log ((2 * M : Nat) : Real) ^ 2) *
        ∑ t ∈ oddSumCarrier M,
          ‖explicitMajorMaskSincKernel M P R ((N : Int) - (t : Int))‖ := by
      rw [Finset.mul_sum]
    _ = (2 * Real.log ((2 * M : Nat) : Real) ^ 2) *
        ∑ k ∈ oddTargetShiftCarrier M N,
          ‖explicitMajorMaskSincKernel M P R k‖ := by
      rw [oddSumKernelNorm_eq_targetShiftKernelNorm]
    _ ≤ (2 * Real.log ((2 * M : Nat) : Real) ^ 2) *
        ∑ k ∈ (shiftCarrier (2 * (M : Real))).filter (fun k => Odd k),
          ‖explicitMajorMaskSincKernel M P R k‖ := by
      apply mul_le_mul_of_nonneg_left _ hlog
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (oddTargetShiftCarrier_subset_oddShiftCarrier hEven hNM)
        (fun k _ _ => norm_nonneg _)
    _ ≤ (2 * Real.log ((2 * M : Nat) : Real) ^ 2) *
        (16 * (P : Real) * (R : Real) * Real.sqrt (R : Real)) := by
      exact mul_le_mul_of_nonneg_left
        (explicitMajorMaskSincKernel_odd_window_l1_le_of_scale hP hscale) hlog
    _ = 32 * (P : Real) * (R : Real) * Real.sqrt (R : Real) *
        Real.log ((2 * M : Nat) : Real) ^ 2 := by ring

theorem explicitPositiveOddSumMass_le
    {M P R N : Nat} (hM2 : 2 ≤ M) (hEven : Even N) (hNM : N ≤ M)
    (hP : 0 < P) (hscale : 2 * P * R < M) :
    explicitPositiveOddSumMass M P R N ≤
      32 * (P : Real) * (R : Real) * Real.sqrt (R : Real) *
        Real.log ((2 * M : Nat) : Real) ^ 2 :=
  (explicitPositiveOddSumMass_le_absolute M P R N).trans
    (explicitOddAbsoluteKernelMass_le hM2 hEven hNM hP hscale)

theorem explicitNegativeOddSumMass_le
    {M P R N : Nat} (hM2 : 2 ≤ M) (hEven : Even N) (hNM : N ≤ M)
    (hP : 0 < P) (hscale : 2 * P * R < M) :
    explicitNegativeOddSumMass M P R N ≤
      32 * (P : Real) * (R : Real) * Real.sqrt (R : Real) *
        Real.log ((2 * M : Nat) : Real) ^ 2 :=
  (explicitNegativeOddSumMass_le_absolute M P R N).trans
    (explicitOddAbsoluteKernelMass_le hM2 hEven hNM hP hscale)

end GoldbachCircleMethodOddChannelCompositionV18656
