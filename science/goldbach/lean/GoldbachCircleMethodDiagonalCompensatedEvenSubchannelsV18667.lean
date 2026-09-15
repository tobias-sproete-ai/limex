import GoldbachCircleMethodOddOddSmallDenominatorNegativeWitnessV18666

/-!
# V1.8.667: diagonal-compensated even subchannels

V1.8.663 obtained a sufficient odd-odd moment gate by dropping the entire
nonnegative convolution-diagonal reserve.  That gate is correct but strictly
stronger than necessary and deletes the exact cancellation paired with the
dense odd-odd off-diagonal term.

This append-only correction splits the diagonal Lambda-pair mass exactly into
even-even and odd-odd coordinate parts for even targets.  Each reserve is then
subtracted from its matching off-diagonal deficit.  The resulting compensated
subchannels recompose the unchanged even deficit exactly.  The already closed
even-even estimate still controls its compensated version, so the sole open
premise becomes the compensated odd-odd moment.

The compensated odd-odd deficit is also identified exactly with the negative
of the full odd-odd Minor-kernel convolution, including its zero-shift diagonal.
No sign, cancellation, moment estimate, or Goldbach conclusion is supplied.

`proof_status = NO_PROOF`.
-/

set_option autoImplicit false

open scoped BigOperators Classical
open MeasureTheory AddCircle
open GoldbachCircleMethodActualOneSidedKernelLeakageV18648
open GoldbachCircleMethodExplicitOffDiagonalKernelLeakageV18649
open GoldbachCircleMethodExactKernelJordanBalanceV18650
open GoldbachCircleMethodExplicitJordanDeficitV18651
open GoldbachCircleMethodExplicitJordanParitySplitV18652
open GoldbachCircleMethodEvenSubchannelSplitV18660
open GoldbachCircleMethodOddOddSoleGateV18663
open GoldbachCircleMethodEvenEvenEventualAbsorptionV18662
open GoldbachCircleMethodOddChannelEventualAbsorptionV18658
open Filter Topology

namespace GoldbachCircleMethodDiagonalCompensatedEvenSubchannelsV18667

private def diagonalPairCarrier (M N : Nat) : Finset (Nat × Nat) :=
  ((Finset.range M.succ).product (Finset.range M.succ)).filter
    (fun ab => ab.1 + ab.2 = N)

noncomputable def diagonalEvenEvenLambdaPairMass (M N : Nat) : Real :=
  ∑ ab ∈ (diagonalPairCarrier M N).filter
      (fun ab => Even ab.1 ∧ Even ab.2),
    lambdaPairWeight ab

noncomputable def diagonalOddOddLambdaPairMass (M N : Nat) : Real :=
  ∑ ab ∈ (diagonalPairCarrier M N).filter
      (fun ab => Odd ab.1 ∧ Odd ab.2),
    lambdaPairWeight ab

theorem diagonalLambdaPairMass_eq_evenEven_add_oddOdd
    (M N : Nat) (hN : Even N) :
    diagonalLambdaPairMass M N =
      diagonalEvenEvenLambdaPairMass M N +
        diagonalOddOddLambdaPairMass M N := by
  classical
  unfold diagonalLambdaPairMass diagonalEvenEvenLambdaPairMass
    diagonalOddOddLambdaPairMass diagonalPairCarrier
  let base :=
    ((Finset.range M.succ).product (Finset.range M.succ)).filter
      (fun ab : Nat × Nat => ab.1 + ab.2 = N)
  let f := fun ab : Nat × Nat => lambdaPairWeight ab
  change (∑ ab ∈ base, f ab) =
    (∑ ab ∈ base.filter (fun ab => Even ab.1 ∧ Even ab.2), f ab) +
      ∑ ab ∈ base.filter (fun ab => Odd ab.1 ∧ Odd ab.2), f ab
  rw [← Finset.sum_filter_add_sum_filter_not base (fun ab => Even ab.1) f]
  congr 1
  · apply Finset.sum_congr
    · ext ab
      simp only [base, Finset.mem_filter]
      constructor
      · rintro ⟨⟨habBox, habSum⟩, haEven⟩
        rcases even_diagonal_coordinates_same_parity hN habSum with hEE | hOO
        · exact ⟨⟨habBox, habSum⟩, hEE⟩
        · exact False.elim (Nat.not_odd_iff_even.mpr haEven hOO.1)
      · rintro ⟨⟨habBox, habSum⟩, haEven, hbEven⟩
        exact ⟨⟨habBox, habSum⟩, haEven⟩
    · intro ab _
      rfl
  · apply Finset.sum_congr
    · ext ab
      simp only [base, Finset.mem_filter]
      constructor
      · rintro ⟨⟨habBox, habSum⟩, haNotEven⟩
        rcases even_diagonal_coordinates_same_parity hN habSum with hEE | hOO
        · exact False.elim (haNotEven hEE.1)
        · exact ⟨⟨habBox, habSum⟩, hOO⟩
      · rintro ⟨⟨habBox, habSum⟩, haOdd, hbOdd⟩
        exact ⟨⟨habBox, habSum⟩, Nat.not_even_iff_odd.mpr haOdd⟩
    · intro ab _
      rfl

noncomputable def explicitDiagonalEvenEvenReserve
    (M P R N : Nat) : Real :=
  haarAddCircle.real
      (GoldbachCircleMethodTwoScaleIntegralPartitionV1831.twoScaleMinorMask
        M P R) * diagonalEvenEvenLambdaPairMass M N

noncomputable def explicitDiagonalOddOddReserve
    (M P R N : Nat) : Real :=
  haarAddCircle.real
      (GoldbachCircleMethodTwoScaleIntegralPartitionV1831.twoScaleMinorMask
        M P R) * diagonalOddOddLambdaPairMass M N

theorem explicitDiagonalPositiveReserve_eq_subchannel_reserves
    (M P R N : Nat) (hN : Even N) :
    explicitDiagonalPositiveReserve M P R N =
      explicitDiagonalEvenEvenReserve M P R N +
        explicitDiagonalOddOddReserve M P R N := by
  unfold explicitDiagonalPositiveReserve explicitDiagonalEvenEvenReserve
    explicitDiagonalOddOddReserve
  rw [diagonalLambdaPairMass_eq_evenEven_add_oddOdd M N hN]
  ring

theorem diagonalEvenEvenLambdaPairMass_nonneg (M N : Nat) :
    0 ≤ diagonalEvenEvenLambdaPairMass M N := by
  unfold diagonalEvenEvenLambdaPairMass
  exact Finset.sum_nonneg fun ab _ => lambdaPairWeight_nonneg ab

theorem diagonalOddOddLambdaPairMass_nonneg (M N : Nat) :
    0 ≤ diagonalOddOddLambdaPairMass M N := by
  unfold diagonalOddOddLambdaPairMass
  exact Finset.sum_nonneg fun ab _ => lambdaPairWeight_nonneg ab

theorem explicitDiagonalEvenEvenReserve_nonneg (M P R N : Nat) :
    0 ≤ explicitDiagonalEvenEvenReserve M P R N := by
  unfold explicitDiagonalEvenEvenReserve
  exact mul_nonneg measureReal_nonneg (diagonalEvenEvenLambdaPairMass_nonneg M N)

theorem explicitDiagonalOddOddReserve_nonneg (M P R N : Nat) :
    0 ≤ explicitDiagonalOddOddReserve M P R N := by
  unfold explicitDiagonalOddOddReserve
  exact mul_nonneg measureReal_nonneg (diagonalOddOddLambdaPairMass_nonneg M N)

noncomputable def compensatedEvenEvenDeficit
    (M P R N : Nat) : Real :=
  explicitEvenEvenSubchannelDeficit M P R N -
    explicitDiagonalEvenEvenReserve M P R N

noncomputable def compensatedOddOddDeficit
    (M P R N : Nat) : Real :=
  explicitOddOddSubchannelDeficit M P R N -
    explicitDiagonalOddOddReserve M P R N

theorem explicitEvenChannelDeficit_eq_compensated_subchannels
    (M P R N : Nat) (hN : Even N) :
    explicitEvenChannelDeficit M P R N =
      compensatedEvenEvenDeficit M P R N +
        compensatedOddOddDeficit M P R N := by
  rw [explicitEvenChannelDeficit_eq_subchannels_sub_diagonal]
  rw [explicitDiagonalPositiveReserve_eq_subchannel_reserves M P R N hN]
  unfold compensatedEvenEvenDeficit compensatedOddOddDeficit
  ring

theorem positivePart_evenChannel_sq_le_compensated
    (M P R N : Nat) (hN : Even N) :
    positivePart (explicitEvenChannelDeficit M P R N) ^ 2 ≤
      2 * positivePart (compensatedEvenEvenDeficit M P R N) ^ 2 +
        2 * positivePart (compensatedOddOddDeficit M P R N) ^ 2 := by
  rw [explicitEvenChannelDeficit_eq_compensated_subchannels M P R N hN]
  exact GoldbachCircleMethodTotalJordanEvenGateV18659.positivePart_add_sq_le_two _ _

theorem positivePart_compensatedEvenEven_le
    (M P R N : Nat) :
    positivePart (compensatedEvenEvenDeficit M P R N) ≤
      positivePart (explicitEvenEvenSubchannelDeficit M P R N) := by
  unfold compensatedEvenEvenDeficit positivePart
  apply max_le
  · have hres := explicitDiagonalEvenEvenReserve_nonneg M P R N
    have hupper : explicitEvenEvenSubchannelDeficit M P R N ≤
        max (explicitEvenEvenSubchannelDeficit M P R N) 0 := le_max_left _ _
    linarith
  · exact le_max_right _ _

theorem compensatedEvenEvenMoment_le_original
    (M P R : Nat) (s : Finset Nat) :
    GoldbachCircleMethodExceptionalTransferV1823.negativePartSquaredMoment s
        (fun N => -compensatedEvenEvenDeficit M P R N) ≤
      GoldbachCircleMethodExceptionalTransferV1823.negativePartSquaredMoment s
        (fun N => -explicitEvenEvenSubchannelDeficit M P R N) := by
  unfold GoldbachCircleMethodExceptionalTransferV1823.negativePartSquaredMoment
  apply Finset.sum_le_sum
  intro N _hN
  rw [negativePart_neg_eq_positivePart, negativePart_neg_eq_positivePart]
  have h := positivePart_compensatedEvenEven_le M P R N
  have hleft : 0 ≤ positivePart (compensatedEvenEvenDeficit M P R N) :=
    positivePart_nonneg _
  have hright : 0 ≤ positivePart (explicitEvenEvenSubchannelDeficit M P R N) :=
    positivePart_nonneg _
  nlinarith

theorem compensatedEvenEven_project_moment_eventually_lt_one_over_12544 :
    ∀ᶠ M : Nat in atTop,
      GoldbachCircleMethodExceptionalTransferV1823.negativePartSquaredMoment
          (GoldbachCircleMethodTwoScaleEvenBlockDefectReserveV1833.evenTargetBlock M)
          (fun N => -compensatedEvenEvenDeficit M
            (oddProjectWidth M) (oddProjectRadius M) N) <
        (M : Real) ^ 2 / 12544 := by
  filter_upwards [evenEven_channel_project_moment_eventually_lt_one_over_12544]
    with M hM
  exact (compensatedEvenEvenMoment_le_original M
    (oddProjectWidth M) (oddProjectRadius M)
      (GoldbachCircleMethodTwoScaleEvenBlockDefectReserveV1833.evenTargetBlock M)).trans_lt hM

theorem project_totalJordan_eventually_lt_one_over_784_of_compensatedOddOdd
    (hOddOdd :
      ∀ᶠ M : Nat in atTop,
        GoldbachCircleMethodExceptionalTransferV1823.negativePartSquaredMoment
            (GoldbachCircleMethodTwoScaleEvenBlockDefectReserveV1833.evenTargetBlock M)
            (fun N => -compensatedOddOddDeficit M
              (oddProjectWidth M) (oddProjectRadius M) N) <
          (M : Real) ^ 2 / 12544) :
    ∀ᶠ M : Nat in atTop,
      GoldbachCircleMethodExplicitJordanDeficitV18651.explicitJordanDeficitSquaredMoment M
          (oddProjectWidth M) (oddProjectRadius M)
          (GoldbachCircleMethodTwoScaleEvenBlockDefectReserveV1833.evenTargetBlock M) <
        (M : Real) ^ 2 / 784 := by
  have hEvenEven := compensatedEvenEven_project_moment_eventually_lt_one_over_12544
  have hEven :
      ∀ᶠ M : Nat in atTop,
        GoldbachCircleMethodExceptionalTransferV1823.negativePartSquaredMoment
            (GoldbachCircleMethodTwoScaleEvenBlockDefectReserveV1833.evenTargetBlock M)
            (fun N => -explicitEvenChannelDeficit M
              (oddProjectWidth M) (oddProjectRadius M) N) <
          (M : Real) ^ 2 / 3136 := by
    filter_upwards [hEvenEven, hOddOdd] with M hEEM hOOM
    rw [negativePartSquaredMoment_neg_explicitEvenChannelDeficit_eq]
    unfold explicitEvenChannelPositivePartSquaredMoment
    have hcompose :
        (∑ N ∈ GoldbachCircleMethodTwoScaleEvenBlockDefectReserveV1833.evenTargetBlock M,
          positivePart (explicitEvenChannelDeficit M
            (oddProjectWidth M) (oddProjectRadius M) N) ^ 2) ≤
          2 * GoldbachCircleMethodExceptionalTransferV1823.negativePartSquaredMoment
              (GoldbachCircleMethodTwoScaleEvenBlockDefectReserveV1833.evenTargetBlock M)
              (fun N => -compensatedEvenEvenDeficit M
                (oddProjectWidth M) (oddProjectRadius M) N) +
            2 * GoldbachCircleMethodExceptionalTransferV1823.negativePartSquaredMoment
              (GoldbachCircleMethodTwoScaleEvenBlockDefectReserveV1833.evenTargetBlock M)
              (fun N => -compensatedOddOddDeficit M
                (oddProjectWidth M) (oddProjectRadius M) N) := by
      unfold GoldbachCircleMethodExceptionalTransferV1823.negativePartSquaredMoment
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro N hN
      rw [negativePart_neg_eq_positivePart, negativePart_neg_eq_positivePart]
      apply positivePart_evenChannel_sq_le_compensated
      exact (GoldbachCircleMethodTwoScaleEvenBlockDefectReserveV1833.mem_evenTargetBlock_iff M N).mp hN |>.2.2.1
    calc
      (∑ N ∈ GoldbachCircleMethodTwoScaleEvenBlockDefectReserveV1833.evenTargetBlock M,
          positivePart (explicitEvenChannelDeficit M
            (oddProjectWidth M) (oddProjectRadius M) N) ^ 2) ≤
          2 * GoldbachCircleMethodExceptionalTransferV1823.negativePartSquaredMoment
              (GoldbachCircleMethodTwoScaleEvenBlockDefectReserveV1833.evenTargetBlock M)
              (fun N => -compensatedEvenEvenDeficit M
                (oddProjectWidth M) (oddProjectRadius M) N) +
            2 * GoldbachCircleMethodExceptionalTransferV1823.negativePartSquaredMoment
              (GoldbachCircleMethodTwoScaleEvenBlockDefectReserveV1833.evenTargetBlock M)
              (fun N => -compensatedOddOddDeficit M
                (oddProjectWidth M) (oddProjectRadius M) N) := hcompose
      _ < (M : Real) ^ 2 / 3136 := by nlinarith
  exact GoldbachCircleMethodTotalJordanEvenGateV18659.project_totalJordan_eventually_lt_one_over_784 hEven

private def oddOddPairCarrier (M : Nat) : Finset (Nat × Nat) :=
  ((Finset.range M.succ).product (Finset.range M.succ)).filter
    (fun ab => Odd ab.1 ∧ Odd ab.2)

private def oddOddOffDiagonalPairCarrier
    (M N : Nat) : Finset (Nat × Nat) :=
  (((Finset.range M.succ).product (Finset.range M.succ)).filter
    (fun ab => ab.1 + ab.2 ≠ N)).filter
      (fun ab => Odd ab.1 ∧ Odd ab.2)

noncomputable def oddOddMinorKernelConvolution
    (M P R N : Nat) : Real :=
  ∑ ab ∈ oddOddPairCarrier M,
    lambdaPairWeight ab *
      (GoldbachCircleMethodSignedMaskKernelConvolutionV1884.minorMaskKernel
        M P R ((N : Int) - (ab.1 : Int) - (ab.2 : Int))).re

theorem oddOdd_diagonal_minor_eq_reserve
    (M P R N : Nat) :
    (∑ ab ∈ (oddOddPairCarrier M).filter (fun ab => ab.1 + ab.2 = N),
      lambdaPairWeight ab *
        (GoldbachCircleMethodSignedMaskKernelConvolutionV1884.minorMaskKernel
          M P R ((N : Int) - (ab.1 : Int) - (ab.2 : Int))).re) =
      explicitDiagonalOddOddReserve M P R N := by
  classical
  unfold explicitDiagonalOddOddReserve diagonalOddOddLambdaPairMass
  rw [Finset.mul_sum]
  apply Finset.sum_congr
  · ext ab
    simp [oddOddPairCarrier, diagonalPairCarrier, and_left_comm,
      and_assoc, and_comm]
  · intro ab hab
    have hsum : ab.1 + ab.2 = N :=
      (Finset.mem_filter.mp (Finset.mem_filter.mp hab).1).2
    have hshift : (N : Int) - (ab.1 : Int) - (ab.2 : Int) = 0 := by
      have hsumInt : (ab.1 : Int) + (ab.2 : Int) = (N : Int) := by
        exact_mod_cast hsum
      omega
    rw [hshift,
      GoldbachCircleMethodSignedMaskKernelConvolutionV1884.minorMaskKernel_zero]
    simp only [Complex.ofReal_re]
    ring

theorem oddOdd_offDiagonal_minor_eq_neg_deficit
    (M P R N : Nat) (hscale : 2 * P * R < M) :
    (∑ ab ∈ oddOddOffDiagonalPairCarrier M N,
      lambdaPairWeight ab *
        (GoldbachCircleMethodSignedMaskKernelConvolutionV1884.minorMaskKernel
          M P R ((N : Int) - (ab.1 : Int) - (ab.2 : Int))).re) =
      -explicitOddOddSubchannelDeficit M P R N := by
  rw [GoldbachCircleMethodOddOddSignedFiberAdapterV18665.explicitOddOddSubchannelDeficit_eq_signedKernelMass
    M P R N]
  unfold GoldbachCircleMethodOddOddSignedFiberAdapterV18665.explicitOddOddSignedKernelMass
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr
  · ext ab
    change ab ∈ oddOddOffDiagonalPairCarrier M N ↔
      ab ∈ ((((Finset.range M.succ).product (Finset.range M.succ)).filter
        (fun ab => ab.1 + ab.2 ≠ N)).filter
          (fun ab => Odd ab.1 ∧ Odd ab.2))
    rfl
  · intro ab hab
    have hne : ab.1 + ab.2 ≠ N :=
      (Finset.mem_filter.mp (Finset.mem_filter.mp hab).1).2
    have hshift : (N : Int) - (ab.1 : Int) - (ab.2 : Int) ≠ 0 := by
      intro hz
      apply hne
      omega
    rw [GoldbachCircleMethodExplicitOffDiagonalKernelLeakageV18649.minorMaskKernel_eq_neg_explicitMajorMaskSincKernel
        M P R hscale _ hshift]
    simp only [Complex.neg_re]
    ring

theorem compensatedOddOddDeficit_eq_neg_minorConvolution
    (M P R N : Nat) (hscale : 2 * P * R < M) :
    compensatedOddOddDeficit M P R N =
      -oddOddMinorKernelConvolution M P R N := by
  unfold compensatedOddOddDeficit oddOddMinorKernelConvolution
  rw [← Finset.sum_filter_add_sum_filter_not
    (oddOddPairCarrier M) (fun ab => ab.1 + ab.2 = N)
      (fun ab =>
        lambdaPairWeight ab *
          (GoldbachCircleMethodSignedMaskKernelConvolutionV1884.minorMaskKernel
            M P R ((N : Int) - (ab.1 : Int) - (ab.2 : Int))).re)]
  rw [oddOdd_diagonal_minor_eq_reserve]
  have hoff :
      (∑ ab ∈ (oddOddPairCarrier M).filter (fun ab => ab.1 + ab.2 ≠ N),
        lambdaPairWeight ab *
          (GoldbachCircleMethodSignedMaskKernelConvolutionV1884.minorMaskKernel
            M P R ((N : Int) - (ab.1 : Int) - (ab.2 : Int))).re) =
        ∑ ab ∈ oddOddOffDiagonalPairCarrier M N,
          lambdaPairWeight ab *
            (GoldbachCircleMethodSignedMaskKernelConvolutionV1884.minorMaskKernel
              M P R ((N : Int) - (ab.1 : Int) - (ab.2 : Int))).re := by
    apply Finset.sum_congr
    · ext ab
      simp [oddOddPairCarrier, oddOddOffDiagonalPairCarrier,
        and_left_comm, and_assoc, and_comm]
    · intro ab _
      rfl
  rw [hoff]
  rw [oddOdd_offDiagonal_minor_eq_neg_deficit M P R N hscale]
  ring

end GoldbachCircleMethodDiagonalCompensatedEvenSubchannelsV18667
