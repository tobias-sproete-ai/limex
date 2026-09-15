import GoldbachCircleMethodEvenSubchannelSplitV18660
import GoldbachCircleMethodOddKernelL1V18655

/-!
# V1.8.661: sparse even-even channel composition

The even-even coordinate subchannel isolated in V1.8.660 is sparse because a
nonzero von-Mangoldt coefficient at an even integer is supported only on a
power of two.  This module keeps the literal finite pair carrier, groups it by
`t=a+b`, bounds every fiber by the square of the exact even Mangoldt mass from
V1.8.83, and composes that bound with the unchanged V1.8.655 kernel L1 bound.

Only the even-even subchannel is estimated.  The dense odd-odd subchannel is
not estimated, and `proof_status = NO_PROOF`.
-/
set_option autoImplicit false

open scoped BigOperators Classical
open GoldbachCircleMethodExceptionalTransferV1823
open GoldbachCircleMethodTwoScaleEvenBlockDefectReserveV1833
open GoldbachCircleMethodSignedWindowFourierAdapterV18130
open GoldbachCircleMethodActualOneSidedKernelLeakageV18648
open GoldbachCircleMethodExplicitOffDiagonalKernelLeakageV18649
open GoldbachCircleMethodArithmeticHalfShiftV1883
open GoldbachCircleMethodOddKernelL1V18655
open GoldbachCircleMethodEvenSubchannelSplitV18660

namespace GoldbachCircleMethodEvenEvenChannelCompositionV18661

private def evenPairCarrier (M : Nat) : Finset (Nat × Nat) :=
  ((Finset.range M.succ).product (Finset.range M.succ)).filter
    (fun ab => Even ab.1 ∧ Even ab.2)

private def evenSumCarrier (M : Nat) : Finset Nat :=
  (Finset.range (2 * M + 1)).filter Even

theorem evenPairCarrier_maps_to_evenSumCarrier (M : Nat) :
    ∀ ab ∈ evenPairCarrier M, ab.1 + ab.2 ∈ evenSumCarrier M := by
  intro ab hab
  rcases Finset.mem_filter.mp hab with ⟨habProduct, haEven, hbEven⟩
  rcases Finset.mem_product.mp habProduct with ⟨ha, hb⟩
  apply Finset.mem_filter.mpr
  constructor
  · apply Finset.mem_range.mpr
    rw [Finset.mem_range] at ha hb
    omega
  · exact haEven.add hbEven

theorem evenPrefixMangoldtMass_eq (M : Nat) :
    (∑ n ∈ (Finset.range M.succ).filter Even,
      ArithmeticFunction.vonMangoldt n) = evenMangoldtMass M := by
  unfold evenMangoldtMass
  rw [Finset.sum_filter, Finset.sum_filter]
  symm
  apply Finset.sum_subset
  · intro n hn
    exact Finset.mem_range.mpr (by
      have h := (Finset.mem_Icc.mp hn).2
      omega)
  · intro n hn hnI
    have hn0 : n = 0 := by
      have hr := Finset.mem_range.mp hn
      simp only [Finset.mem_Icc, not_and_or] at hnI
      omega
    subst n
    simp

theorem evenPairCarrier_totalMass_eq (M : Nat) :
    (∑ ab ∈ evenPairCarrier M, lambdaPairWeight ab) =
      evenMangoldtMass M ^ 2 := by
  classical
  have hcarrier : evenPairCarrier M =
      ((Finset.range M.succ).filter Even).product
        ((Finset.range M.succ).filter Even) := by
    ext ab
    simp [evenPairCarrier, and_assoc, and_left_comm, and_comm]
  rw [hcarrier, Finset.product_eq_sprod, Finset.sum_product]
  unfold lambdaPairWeight
  have hprefix := evenPrefixMangoldtMass_eq M
  calc
    (∑ a ∈ (Finset.range M.succ).filter Even,
        ∑ b ∈ (Finset.range M.succ).filter Even,
          ArithmeticFunction.vonMangoldt a *
            ArithmeticFunction.vonMangoldt b) =
      (∑ a ∈ (Finset.range M.succ).filter Even,
        ArithmeticFunction.vonMangoldt a) *
      (∑ b ∈ (Finset.range M.succ).filter Even,
        ArithmeticFunction.vonMangoldt b) := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro a _ha
          rw [Finset.mul_sum]
    _ = evenMangoldtMass M ^ 2 := by rw [hprefix]; ring

/-- Exact even-even fiber mass at the pair sum `t`. -/
noncomputable def evenEvenPairFiberMass (M t : Nat) : Real :=
  ∑ ab ∈ evenPairCarrier M with ab.1 + ab.2 = t, lambdaPairWeight ab

theorem evenEvenPairFiberMass_nonneg (M t : Nat) :
    0 ≤ evenEvenPairFiberMass M t := by
  unfold evenEvenPairFiberMass
  exact Finset.sum_nonneg fun ab _ => lambdaPairWeight_nonneg ab

theorem evenEvenPairFiberMass_le_total (M t : Nat) :
    evenEvenPairFiberMass M t ≤ evenMangoldtMass M ^ 2 := by
  rw [← evenPairCarrier_totalMass_eq M]
  unfold evenEvenPairFiberMass
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun ab _ _ => lambdaPairWeight_nonneg ab)

theorem evenMangoldtMass_nonneg (M : Nat) : 0 ≤ evenMangoldtMass M := by
  unfold evenMangoldtMass
  exact Finset.sum_nonneg fun _ _ => ArithmeticFunction.vonMangoldt_nonneg

theorem evenEvenPairFiberMass_le_log_sq
    {M t : Nat} (hM : 0 < M) :
    evenEvenPairFiberMass M t ≤ Real.log (M : Real) ^ 2 := by
  have hmass := evenMangoldtMass_le_log M hM
  have hmass0 := evenMangoldtMass_nonneg M
  have hlog0 : 0 ≤ Real.log (M : Real) :=
    Real.log_nonneg (by exact_mod_cast hM)
  exact (evenEvenPairFiberMass_le_total M t).trans
    ((sq_le_sq₀ hmass0 hlog0).2 hmass)

/-- Absolute envelope on the full literal even-even pair carrier. -/
noncomputable def explicitEvenEvenAbsoluteKernelMass
    (M P R N : Nat) : Real :=
  ∑ ab ∈ evenPairCarrier M,
    lambdaPairWeight ab *
      ‖explicitMajorMaskSincKernel M P R
        ((N : Int) - (ab.1 : Int) - (ab.2 : Int))‖

set_option maxHeartbeats 800000 in
theorem explicitEvenEvenAbsoluteKernelMass_eq_sum_fibers
    (M P R N : Nat) :
    explicitEvenEvenAbsoluteKernelMass M P R N =
      ∑ t ∈ evenSumCarrier M,
        evenEvenPairFiberMass M t *
          ‖explicitMajorMaskSincKernel M P R ((N : Int) - (t : Int))‖ := by
  classical
  have hFiber :
      (∑ t ∈ evenSumCarrier M,
        ∑ ab ∈ evenPairCarrier M with ab.1 + ab.2 = t,
          lambdaPairWeight ab *
            ‖explicitMajorMaskSincKernel M P R
              ((N : Int) - (ab.1 : Int) - (ab.2 : Int))‖) =
        ∑ ab ∈ evenPairCarrier M,
          lambdaPairWeight ab *
            ‖explicitMajorMaskSincKernel M P R
              ((N : Int) - (ab.1 : Int) - (ab.2 : Int))‖ :=
    Finset.sum_fiberwise_of_maps_to
      (evenPairCarrier_maps_to_evenSumCarrier M)
      (fun ab : Nat × Nat =>
        lambdaPairWeight ab *
          ‖explicitMajorMaskSincKernel M P R
            ((N : Int) - (ab.1 : Int) - (ab.2 : Int))‖)
  unfold explicitEvenEvenAbsoluteKernelMass
  rw [← hFiber]
  apply Finset.sum_congr rfl
  intro t _ht
  unfold evenEvenPairFiberMass
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

theorem explicitNegativeEvenEvenMass_le_absolute
    (M P R N : Nat) :
    explicitNegativeEvenEvenMass M P R N ≤
      explicitEvenEvenAbsoluteKernelMass M P R N := by
  classical
  unfold explicitNegativeEvenEvenMass explicitEvenEvenAbsoluteKernelMass
  let restricted :=
    ((((Finset.range M.succ).product (Finset.range M.succ)).filter
      (fun ab : Nat × Nat => ab.1 + ab.2 ≠ N)).filter
        (fun ab => Even ab.1 ∧ Even ab.2))
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
    _ ≤ ∑ ab ∈ evenPairCarrier M,
        lambdaPairWeight ab *
          ‖explicitMajorMaskSincKernel M P R
            ((N : Int) - (ab.1 : Int) - (ab.2 : Int))‖ := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro ab hab
        rcases Finset.mem_filter.mp hab with ⟨hoff, heven⟩
        exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hoff).1, heven⟩
      · intro ab _hab _hnot
        exact mul_nonneg (lambdaPairWeight_nonneg ab) (norm_nonneg _)

private def targetShiftEmbedding (N : Nat) : Nat ↪ Int where
  toFun t := (N : Int) - (t : Int)
  inj' := by
    intro a b hab
    change (N : Int) - (a : Int) = (N : Int) - (b : Int) at hab
    exact Int.ofNat_inj.mp (sub_right_inj.mp hab)

private noncomputable def evenTargetShiftCarrier (M N : Nat) : Finset Int :=
  (evenSumCarrier M).map (targetShiftEmbedding N)

theorem evenSumKernelNorm_eq_targetShiftKernelNorm
    (M P R N : Nat) :
    (∑ t ∈ evenSumCarrier M,
      ‖explicitMajorMaskSincKernel M P R ((N : Int) - (t : Int))‖) =
      ∑ k ∈ evenTargetShiftCarrier M N,
        ‖explicitMajorMaskSincKernel M P R k‖ := by
  classical
  unfold evenTargetShiftCarrier
  rw [Finset.sum_map]
  rfl

theorem evenTargetShiftCarrier_subset_shiftCarrier
    {M N : Nat} (hNM : N ≤ M) :
    evenTargetShiftCarrier M N ⊆ shiftCarrier (2 * (M : Real)) := by
  intro k hk
  unfold evenTargetShiftCarrier at hk
  rcases Finset.mem_map.mp hk with ⟨t, ht, rfl⟩
  have htRange := (Finset.mem_filter.mp ht).1
  have htLe : t ≤ 2 * M := by
    have := Finset.mem_range.mp htRange
    omega
  rw [mem_shift_carrier (2 * (M : Real)) (by positivity)]
  have hNReal : (N : Real) ≤ (M : Real) := by exact_mod_cast hNM
  have htReal : (t : Real) ≤ 2 * (M : Real) := by exact_mod_cast htLe
  have hcast :
      (((targetShiftEmbedding N) t : Int) : Real) =
        (N : Real) - (t : Real) := by
    change (((N : Int) - (t : Int) : Int) : Real) =
      (N : Real) - (t : Real)
    norm_num
  rw [hcast, abs_le]
  constructor <;> linarith

/-- Pointwise absolute envelope for the sparse even-even channel. -/
theorem explicitEvenEvenAbsoluteKernelMass_le
    {M P R N : Nat} (hM2 : 2 ≤ M) (hNM : N ≤ M)
    (hP : 0 < P) (hscale : 2 * P * R < M) :
    explicitEvenEvenAbsoluteKernelMass M P R N ≤
      16 * (P : Real) * (R : Real) * Real.sqrt (R : Real) *
        Real.log (M : Real) ^ 2 := by
  rw [explicitEvenEvenAbsoluteKernelMass_eq_sum_fibers]
  have hlog : 0 ≤ Real.log (M : Real) ^ 2 := sq_nonneg _
  calc
    _ ≤ ∑ t ∈ evenSumCarrier M,
        Real.log (M : Real) ^ 2 *
          ‖explicitMajorMaskSincKernel M P R ((N : Int) - (t : Int))‖ := by
      apply Finset.sum_le_sum
      intro t _ht
      exact mul_le_mul_of_nonneg_right
        (evenEvenPairFiberMass_le_log_sq (show 0 < M by omega))
        (norm_nonneg _)
    _ = Real.log (M : Real) ^ 2 *
        ∑ t ∈ evenSumCarrier M,
          ‖explicitMajorMaskSincKernel M P R ((N : Int) - (t : Int))‖ := by
      rw [Finset.mul_sum]
    _ = Real.log (M : Real) ^ 2 *
        ∑ k ∈ evenTargetShiftCarrier M N,
          ‖explicitMajorMaskSincKernel M P R k‖ := by
      rw [evenSumKernelNorm_eq_targetShiftKernelNorm]
    _ ≤ Real.log (M : Real) ^ 2 *
        ∑ k ∈ shiftCarrier (2 * (M : Real)),
          ‖explicitMajorMaskSincKernel M P R k‖ := by
      apply mul_le_mul_of_nonneg_left _ hlog
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (evenTargetShiftCarrier_subset_shiftCarrier hNM)
        (fun k _ _ => norm_nonneg _)
    _ ≤ Real.log (M : Real) ^ 2 *
        (16 * (P : Real) * (R : Real) * Real.sqrt (R : Real)) := by
      exact mul_le_mul_of_nonneg_left
        (explicitMajorMaskSincKernel_window_l1_le_of_scale hP hscale) hlog
    _ = 16 * (P : Real) * (R : Real) * Real.sqrt (R : Real) *
        Real.log (M : Real) ^ 2 := by ring

theorem positivePart_evenEvenSubchannelDeficit_le
    {M P R N : Nat} (hM2 : 2 ≤ M) (hNM : N ≤ M)
    (hP : 0 < P) (hscale : 2 * P * R < M) :
    positivePart (explicitEvenEvenSubchannelDeficit M P R N) ≤
      16 * (P : Real) * (R : Real) * Real.sqrt (R : Real) *
        Real.log (M : Real) ^ 2 :=
  (positivePart_evenEvenSubchannelDeficit_le_negativeMass M P R N).trans
    ((explicitNegativeEvenEvenMass_le_absolute M P R N).trans
      (explicitEvenEvenAbsoluteKernelMass_le hM2 hNM hP hscale))

noncomputable def explicitEvenEvenPositivePartSquaredMoment
    (M P R : Nat) (s : Finset Nat) : Real :=
  ∑ N ∈ s, (positivePart (explicitEvenEvenSubchannelDeficit M P R N)) ^ 2

theorem evenTargetBlock_card_le (M : Nat) :
    (evenTargetBlock M).card ≤ M := by
  unfold evenTargetBlock
  calc
    (((Finset.Icc 4 M).filter (fun N => Even N ∧ M ≤ 2 * N)).card) ≤
        (Finset.Icc 4 M).card := Finset.card_filter_le _ _
    _ = M + 1 - 4 := Nat.card_Icc 4 M
    _ ≤ M := by omega

theorem explicitEvenEvenPositivePartSquaredMoment_evenTargetBlock_le
    {M P R : Nat} (hM2 : 2 ≤ M) (hP : 0 < P)
    (hscale : 2 * P * R < M) :
    explicitEvenEvenPositivePartSquaredMoment M P R (evenTargetBlock M) ≤
      256 * (M : Real) * (P : Real) ^ 2 * (R : Real) ^ 3 *
        Real.log (M : Real) ^ 4 := by
  have hCard : ((evenTargetBlock M).card : Real) ≤ (M : Real) := by
    exact_mod_cast evenTargetBlock_card_le M
  unfold explicitEvenEvenPositivePartSquaredMoment
  calc
    _ ≤ ∑ _N ∈ evenTargetBlock M,
        (16 * (P : Real) * (R : Real) * Real.sqrt (R : Real) *
          Real.log (M : Real) ^ 2) ^ 2 := by
      apply Finset.sum_le_sum
      intro N hN
      have hNM := ((mem_evenTargetBlock_iff M N).1 hN).2.1
      have hpoint := positivePart_evenEvenSubchannelDeficit_le
        hM2 hNM hP hscale
      have hleft : 0 ≤ positivePart
          (explicitEvenEvenSubchannelDeficit M P R N) := positivePart_nonneg _
      have hright : 0 ≤
          16 * (P : Real) * (R : Real) * Real.sqrt (R : Real) *
            Real.log (M : Real) ^ 2 := by positivity
      nlinarith
    _ = ((evenTargetBlock M).card : Real) *
        (16 * (P : Real) * (R : Real) * Real.sqrt (R : Real) *
          Real.log (M : Real) ^ 2) ^ 2 := by simp
    _ ≤ (M : Real) *
        (16 * (P : Real) * (R : Real) * Real.sqrt (R : Real) *
          Real.log (M : Real) ^ 2) ^ 2 :=
      mul_le_mul_of_nonneg_right hCard (sq_nonneg _)
    _ = 256 * (M : Real) * (P : Real) ^ 2 * (R : Real) ^ 2 *
        (Real.sqrt (R : Real)) ^ 2 * Real.log (M : Real) ^ 4 := by ring
    _ = 256 * (M : Real) * (P : Real) ^ 2 * (R : Real) ^ 3 *
        Real.log (M : Real) ^ 4 := by
      rw [Real.sq_sqrt (Nat.cast_nonneg R)]
      ring

/-- The negative-part moment of the negated even-even deficit is exactly the
positive-part moment estimated above. -/
theorem negativePartSquaredMoment_neg_evenEvenSubchannelDeficit_eq
    (M P R : Nat) (s : Finset Nat) :
    negativePartSquaredMoment s
        (fun N => -explicitEvenEvenSubchannelDeficit M P R N) =
      explicitEvenEvenPositivePartSquaredMoment M P R s := by
  unfold negativePartSquaredMoment explicitEvenEvenPositivePartSquaredMoment
  apply Finset.sum_congr rfl
  intro N _hN
  rw [negativePart_neg_eq_positivePart]

/-- Final finite sparse-channel moment bound in the same one-sided
normalization used by the downstream exceptional-set transfer. -/
theorem negativePartSquaredMoment_neg_evenEvenSubchannelDeficit_evenTargetBlock_le
    {M P R : Nat} (hM2 : 2 ≤ M) (hP : 0 < P)
    (hscale : 2 * P * R < M) :
    negativePartSquaredMoment (evenTargetBlock M)
        (fun N => -explicitEvenEvenSubchannelDeficit M P R N) ≤
      256 * (M : Real) * (P : Real) ^ 2 * (R : Real) ^ 3 *
        Real.log (M : Real) ^ 4 := by
  rw [negativePartSquaredMoment_neg_evenEvenSubchannelDeficit_eq]
  exact explicitEvenEvenPositivePartSquaredMoment_evenTargetBlock_le
    hM2 hP hscale

end GoldbachCircleMethodEvenEvenChannelCompositionV18661
