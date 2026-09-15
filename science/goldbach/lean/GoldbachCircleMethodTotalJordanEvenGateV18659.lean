import GoldbachCircleMethodOddChannelEventualAbsorptionV18658

/-!
# V1.8.659: exact total Jordan reduction to the remaining even channel

This append-only module combines the exact parity decomposition of V1.8.652
with the kernel-checked eventual odd-channel absorption of V1.8.658.  It proves
that the full explicit Jordan moment satisfies the standard two-channel square
bound and reduces the project target `M^2 / 784` to a matching
`M^2 / 3136` estimate for the still-open even channel.

No estimate of the even channel is asserted or inhabited here.
`proof_status = NO_PROOF`.
-/
set_option autoImplicit false

open Filter Topology
open GoldbachCircleMethodExceptionalTransferV1823
open GoldbachCircleMethodTwoScaleEvenBlockDefectReserveV1833
open GoldbachCircleMethodExplicitOffDiagonalKernelLeakageV18649
open GoldbachCircleMethodExplicitJordanDeficitV18651
open GoldbachCircleMethodExplicitJordanParitySplitV18652
open GoldbachCircleMethodOddChannelEventualAbsorptionV18658

namespace GoldbachCircleMethodTotalJordanEvenGateV18659

/-- Elementary one-sided square bound used to compose two signed channels. -/
theorem positivePart_add_sq_le_two
    (a b : Real) :
    positivePart (a + b) ^ 2 ≤
      2 * positivePart a ^ 2 + 2 * positivePart b ^ 2 := by
  have ha : a ≤ positivePart a := le_max_left _ _
  have hb : b ≤ positivePart b := le_max_left _ _
  have hab : positivePart (a + b) ≤ positivePart a + positivePart b := by
    unfold positivePart
    apply max_le
    · simpa only [positivePart] using add_le_add ha hb
    · exact add_nonneg (le_max_right _ _) (le_max_right _ _)
  have hleft : 0 ≤ positivePart (a + b) := positivePart_nonneg _
  have hright : 0 ≤ positivePart a + positivePart b :=
    add_nonneg (positivePart_nonneg _) (positivePart_nonneg _)
  have hsq : positivePart (a + b) ^ 2 ≤
      (positivePart a + positivePart b) ^ 2 := by nlinarith
  calc
    positivePart (a + b) ^ 2 ≤
        (positivePart a + positivePart b) ^ 2 := hsq
    _ ≤ 2 * positivePart a ^ 2 + 2 * positivePart b ^ 2 := by
      nlinarith [sq_nonneg (positivePart a - positivePart b)]

/-- The total explicit Jordan moment is controlled by twice the odd harmful
moment plus twice the even harmful moment.  This is a finite exact-algebra
transfer and introduces no analytic estimate. -/
theorem explicitJordanDeficitSquaredMoment_le_two_parity_channels
    (M P R : Nat) (s : Finset Nat) :
    explicitJordanDeficitSquaredMoment M P R s ≤
      2 * negativePartSquaredMoment s
        (fun N => -explicitOddChannelDeficit M P R N) +
      2 * negativePartSquaredMoment s
        (fun N => -explicitEvenChannelDeficit M P R N) := by
  unfold explicitJordanDeficitSquaredMoment negativePartSquaredMoment
  rw [Finset.mul_sum, Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro N hN
  rw [explicitMassDeficit_eq_odd_add_even]
  rw [negativePart_neg_eq_positivePart, negativePart_neg_eq_positivePart]
  exact positivePart_add_sq_le_two
    (explicitOddChannelDeficit M P R N)
    (explicitEvenChannelDeficit M P R N)

/-- The already closed odd channel and a matching even-channel premise imply
the literal project budget for the full explicit Jordan moment.  The premise
is deliberately exposed: this theorem does not inhabit it. -/
theorem project_totalJordan_eventually_lt_one_over_784
    (hEven :
      ∀ᶠ M : Nat in atTop,
        negativePartSquaredMoment (evenTargetBlock M)
          (fun N => -explicitEvenChannelDeficit M
            (oddProjectWidth M) (oddProjectRadius M) N) <
          (M : Real) ^ 2 / 3136) :
    ∀ᶠ M : Nat in atTop,
      explicitJordanDeficitSquaredMoment M
          (oddProjectWidth M) (oddProjectRadius M) (evenTargetBlock M) <
        (M : Real) ^ 2 / 784 := by
  have hOdd := odd_channel_project_moment_eventually_lt_one_over_3136
  filter_upwards [hOdd, hEven] with M hOddM hEvenM
  have hcompose := explicitJordanDeficitSquaredMoment_le_two_parity_channels
    M (oddProjectWidth M) (oddProjectRadius M) (evenTargetBlock M)
  calc
    explicitJordanDeficitSquaredMoment M
          (oddProjectWidth M) (oddProjectRadius M) (evenTargetBlock M) ≤
        2 * negativePartSquaredMoment (evenTargetBlock M)
            (fun N => -explicitOddChannelDeficit M
              (oddProjectWidth M) (oddProjectRadius M) N) +
          2 * negativePartSquaredMoment (evenTargetBlock M)
            (fun N => -explicitEvenChannelDeficit M
              (oddProjectWidth M) (oddProjectRadius M) N) := hcompose
    _ < (M : Real) ^ 2 / 784 := by nlinarith

end GoldbachCircleMethodTotalJordanEvenGateV18659
