import GoldbachCircleMethodTotalJordanEvenGateV18659
import GoldbachCircleMethodEvenEvenEventualAbsorptionV18662

/-!
# V1.8.663: exact reduction to the sole dense odd-odd gate

This append-only module composes the exact V1.8.660 even-subchannel split,
the V1.8.662 eventual absorption of the sparse even-even subchannel, and the
V1.8.659 total-channel transfer.  At the unchanged project schedule the full
Jordan target now follows from one exposed premise only: an `M^2/12544`
one-sided moment bound for the dense odd-odd subchannel.

That premise is not inhabited here. `proof_status = NO_PROOF`.
-/
set_option autoImplicit false

open Filter Topology
open GoldbachCircleMethodExceptionalTransferV1823
open GoldbachCircleMethodTwoScaleEvenBlockDefectReserveV1833
open GoldbachCircleMethodExplicitOffDiagonalKernelLeakageV18649
open GoldbachCircleMethodExplicitJordanDeficitV18651
open GoldbachCircleMethodExplicitJordanParitySplitV18652
open GoldbachCircleMethodOddChannelEventualAbsorptionV18658
open GoldbachCircleMethodTotalJordanEvenGateV18659
open GoldbachCircleMethodEvenSubchannelSplitV18660
open GoldbachCircleMethodEvenEvenChannelCompositionV18661
open GoldbachCircleMethodEvenEvenEventualAbsorptionV18662

namespace GoldbachCircleMethodOddOddSoleGateV18663

/-- Finite one-sided moment of the full even channel. -/
noncomputable def explicitEvenChannelPositivePartSquaredMoment
    (M P R : Nat) (s : Finset Nat) : Real :=
  ∑ N ∈ s, (positivePart (explicitEvenChannelDeficit M P R N)) ^ 2

/-- The full even-channel harmful moment is at most twice the even-even
moment plus twice the odd-odd moment.  The nonnegative diagonal reserve is
retained and may only improve this inequality. -/
theorem explicitEvenChannelPositivePartSquaredMoment_le_two_subchannels
    (M P R : Nat) (s : Finset Nat) :
    explicitEvenChannelPositivePartSquaredMoment M P R s ≤
      2 * negativePartSquaredMoment s
        (fun N => -explicitEvenEvenSubchannelDeficit M P R N) +
      2 * negativePartSquaredMoment s
        (fun N => -explicitOddOddSubchannelDeficit M P R N) := by
  unfold explicitEvenChannelPositivePartSquaredMoment negativePartSquaredMoment
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro N hN
  rw [negativePart_neg_eq_positivePart, negativePart_neg_eq_positivePart]
  have hlinear := positivePart_explicitEvenChannelDeficit_le_subchannels M P R N
  have hleft : 0 ≤ positivePart (explicitEvenChannelDeficit M P R N) :=
    positivePart_nonneg _
  have hright : 0 ≤
      positivePart (explicitEvenEvenSubchannelDeficit M P R N) +
        positivePart (explicitOddOddSubchannelDeficit M P R N) :=
    add_nonneg (positivePart_nonneg _) (positivePart_nonneg _)
  calc
    positivePart (explicitEvenChannelDeficit M P R N) ^ 2 ≤
        (positivePart (explicitEvenEvenSubchannelDeficit M P R N) +
          positivePart (explicitOddOddSubchannelDeficit M P R N)) ^ 2 := by
      nlinarith
    _ ≤ 2 * positivePart (explicitEvenEvenSubchannelDeficit M P R N) ^ 2 +
        2 * positivePart (explicitOddOddSubchannelDeficit M P R N) ^ 2 := by
      nlinarith [sq_nonneg
        (positivePart (explicitEvenEvenSubchannelDeficit M P R N) -
          positivePart (explicitOddOddSubchannelDeficit M P R N))]

/-- Negative-part notation used by V1.8.659 is exactly the positive-part
moment defined above. -/
theorem negativePartSquaredMoment_neg_explicitEvenChannelDeficit_eq
    (M P R : Nat) (s : Finset Nat) :
    negativePartSquaredMoment s
        (fun N => -explicitEvenChannelDeficit M P R N) =
      explicitEvenChannelPositivePartSquaredMoment M P R s := by
  unfold negativePartSquaredMoment explicitEvenChannelPositivePartSquaredMoment
  apply Finset.sum_congr rfl
  intro N _hN
  rw [negativePart_neg_eq_positivePart]

/-- One strict `M^2/12544` odd-odd budget, together with the already proved
sparse-channel absorption, yields the V1.8.659 even budget `M^2/3136`. -/
theorem project_evenChannel_eventually_lt_one_over_3136_of_oddOdd
    (hOddOdd :
      ∀ᶠ M : Nat in atTop,
        negativePartSquaredMoment (evenTargetBlock M)
          (fun N => -explicitOddOddSubchannelDeficit M
            (oddProjectWidth M) (oddProjectRadius M) N) <
          (M : Real) ^ 2 / 12544) :
    ∀ᶠ M : Nat in atTop,
      negativePartSquaredMoment (evenTargetBlock M)
          (fun N => -explicitEvenChannelDeficit M
            (oddProjectWidth M) (oddProjectRadius M) N) <
        (M : Real) ^ 2 / 3136 := by
  have hEvenEven :=
    evenEven_channel_project_moment_eventually_lt_one_over_12544
  filter_upwards [hEvenEven, hOddOdd] with M hEEM hOOM
  rw [negativePartSquaredMoment_neg_explicitEvenChannelDeficit_eq]
  have hcompose :=
    explicitEvenChannelPositivePartSquaredMoment_le_two_subchannels
      M (oddProjectWidth M) (oddProjectRadius M) (evenTargetBlock M)
  calc
    explicitEvenChannelPositivePartSquaredMoment M
          (oddProjectWidth M) (oddProjectRadius M) (evenTargetBlock M) ≤
        2 * negativePartSquaredMoment (evenTargetBlock M)
            (fun N => -explicitEvenEvenSubchannelDeficit M
              (oddProjectWidth M) (oddProjectRadius M) N) +
          2 * negativePartSquaredMoment (evenTargetBlock M)
            (fun N => -explicitOddOddSubchannelDeficit M
              (oddProjectWidth M) (oddProjectRadius M) N) := hcompose
    _ < (M : Real) ^ 2 / 3136 := by nlinarith

/-- Final exact reduction of the full project Jordan budget to the sole dense
odd-odd one-sided moment premise. -/
theorem project_totalJordan_eventually_lt_one_over_784_of_oddOdd
    (hOddOdd :
      ∀ᶠ M : Nat in atTop,
        negativePartSquaredMoment (evenTargetBlock M)
          (fun N => -explicitOddOddSubchannelDeficit M
            (oddProjectWidth M) (oddProjectRadius M) N) <
          (M : Real) ^ 2 / 12544) :
    ∀ᶠ M : Nat in atTop,
      explicitJordanDeficitSquaredMoment M
          (oddProjectWidth M) (oddProjectRadius M) (evenTargetBlock M) <
        (M : Real) ^ 2 / 784 :=
  project_totalJordan_eventually_lt_one_over_784
    (project_evenChannel_eventually_lt_one_over_3136_of_oddOdd hOddOdd)

end GoldbachCircleMethodOddOddSoleGateV18663
