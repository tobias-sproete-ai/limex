import GoldbachCircleMethodExplicitJordanDeficitV18651

/-!
# V1.8.652: exact parity split of the explicit Jordan deficit

This append-only module partitions the unchanged off-diagonal pair carrier of
V1.8.649--V1.8.651 by the parity of `a + b`.  On an even Goldbach target this
is exactly the parity split of the Fourier shift `N - a - b`, but the finite
sum identities proved here do not require an analytic estimate or evenness.

Both signs of the explicit Major Jordan kernel are partitioned.  Consequently
the total positive mass, total negative mass, actual Minor real part, and the
actual-Major overshoot deficit are expressed exactly through odd and even
channels.  No endpoint, pair, or off-diagonal condition is changed.

No analytic bound and no new assumption is introduced.

`proof_status = NO_PROOF`.
-/
set_option autoImplicit false

open scoped BigOperators Classical
open GoldbachCircleMethodSignedMaskKernelConvolutionV1884
open GoldbachCircleMethodActualMajorOvershootIdentityV18630
open GoldbachCircleMethodActualOneSidedKernelLeakageV18648
open GoldbachCircleMethodExplicitOffDiagonalKernelLeakageV18649
open GoldbachCircleMethodExplicitJordanDeficitV18651

namespace GoldbachCircleMethodExplicitJordanParitySplitV18652

/-- The exact V1.8.649 off-diagonal pair carrier, named once for the parity
partition.  Its endpoints remain `0 <= a,b <= M`, and the diagonal `a+b=N`
is excluded. -/
private def offDiagonalPairCarrier (M N : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range M.succ).product (Finset.range M.succ)).filter
    (fun ab => ab.1 + ab.2 ≠ N)

/-- Odd-pair-sum positive off-diagonal Minor mass.  The target-dependent
Fourier shift is retained literally in the definition. -/
noncomputable def explicitPositiveOddSumMass
    (M P R N : ℕ) : ℝ :=
  ∑ ab ∈ (offDiagonalPairCarrier M N).filter
      (fun ab => Odd (ab.1 + ab.2)),
    lambdaPairWeight ab *
      GoldbachCircleMethodExceptionalTransferV1823.negativePart
        (explicitMajorMaskSincKernel M P R
          ((N : ℤ) - (ab.1 : ℤ) - (ab.2 : ℤ))).re

/-- Even-pair-sum positive off-diagonal Minor mass. -/
noncomputable def explicitPositiveEvenSumMass
    (M P R N : ℕ) : ℝ :=
  ∑ ab ∈ (offDiagonalPairCarrier M N).filter
      (fun ab => Even (ab.1 + ab.2)),
    lambdaPairWeight ab *
      GoldbachCircleMethodExceptionalTransferV1823.negativePart
        (explicitMajorMaskSincKernel M P R
          ((N : ℤ) - (ab.1 : ℤ) - (ab.2 : ℤ))).re

/-- Odd-pair-sum negative Minor mass, equivalently the positive part of the
real explicit Major Ramanujan--sinc coefficient. -/
noncomputable def explicitNegativeOddSumMass
    (M P R N : ℕ) : ℝ :=
  ∑ ab ∈ (offDiagonalPairCarrier M N).filter
      (fun ab => Odd (ab.1 + ab.2)),
    lambdaPairWeight ab *
      positivePart
        (explicitMajorMaskSincKernel M P R
          ((N : ℤ) - (ab.1 : ℤ) - (ab.2 : ℤ))).re

/-- Even-pair-sum negative Minor mass. -/
noncomputable def explicitNegativeEvenSumMass
    (M P R N : ℕ) : ℝ :=
  ∑ ab ∈ (offDiagonalPairCarrier M N).filter
      (fun ab => Even (ab.1 + ab.2)),
    lambdaPairWeight ab *
      positivePart
        (explicitMajorMaskSincKernel M P R
          ((N : ℤ) - (ab.1 : ℤ) - (ab.2 : ℤ))).re

theorem explicitPositiveOddSumMass_nonneg (M P R N : ℕ) :
    0 ≤ explicitPositiveOddSumMass M P R N := by
  unfold explicitPositiveOddSumMass
  exact Finset.sum_nonneg fun ab _ =>
    mul_nonneg (lambdaPairWeight_nonneg ab) (negativePart_nonneg _)

theorem explicitPositiveEvenSumMass_nonneg (M P R N : ℕ) :
    0 ≤ explicitPositiveEvenSumMass M P R N := by
  unfold explicitPositiveEvenSumMass
  exact Finset.sum_nonneg fun ab _ =>
    mul_nonneg (lambdaPairWeight_nonneg ab) (negativePart_nonneg _)

theorem explicitNegativeOddSumMass_nonneg (M P R N : ℕ) :
    0 ≤ explicitNegativeOddSumMass M P R N := by
  unfold explicitNegativeOddSumMass
  exact Finset.sum_nonneg fun ab _ =>
    mul_nonneg (lambdaPairWeight_nonneg ab) (positivePart_nonneg _)

theorem explicitNegativeEvenSumMass_nonneg (M P R N : ℕ) :
    0 ≤ explicitNegativeEvenSumMass M P R N := by
  unfold explicitNegativeEvenSumMass
  exact Finset.sum_nonneg fun ab _ =>
    mul_nonneg (lambdaPairWeight_nonneg ab) (positivePart_nonneg _)

/-- Exact parity partition of the V1.8.651 positive off-diagonal mass. -/
theorem explicitPositiveOffDiagonalMass_eq_odd_add_even
    (M P R N : ℕ) :
    explicitPositiveOffDiagonalMass M P R N =
      explicitPositiveOddSumMass M P R N +
        explicitPositiveEvenSumMass M P R N := by
  classical
  unfold explicitPositiveOffDiagonalMass explicitPositiveOddSumMass
    explicitPositiveEvenSumMass offDiagonalPairCarrier
  rw [← Finset.sum_filter_add_sum_filter_not
    (((Finset.range M.succ).product (Finset.range M.succ)).filter
      (fun ab : ℕ × ℕ => ab.1 + ab.2 ≠ N))
    (fun ab : ℕ × ℕ => Odd (ab.1 + ab.2))
    (fun ab =>
      lambdaPairWeight ab *
        GoldbachCircleMethodExceptionalTransferV1823.negativePart
          (explicitMajorMaskSincKernel M P R
            ((N : ℤ) - (ab.1 : ℤ) - (ab.2 : ℤ))).re)]
  congr 1
  apply Finset.sum_congr
  · ext ab
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hab, hNotOdd⟩
      exact ⟨hab, Nat.not_odd_iff_even.mp hNotOdd⟩
    · rintro ⟨hab, hEven⟩
      exact ⟨hab, Nat.not_odd_iff_even.mpr hEven⟩
  · intro ab hab
    rfl

/-- Exact parity partition of the V1.8.651 negative mass. -/
theorem explicitNegativeMass_eq_odd_add_even
    (M P R N : ℕ) :
    explicitNegativeMass M P R N =
      explicitNegativeOddSumMass M P R N +
        explicitNegativeEvenSumMass M P R N := by
  classical
  unfold explicitNegativeMass explicitOffDiagonalKernelLeakage
    explicitNegativeOddSumMass explicitNegativeEvenSumMass offDiagonalPairCarrier
  rw [← Finset.sum_filter_add_sum_filter_not
    (((Finset.range M.succ).product (Finset.range M.succ)).filter
      (fun ab : ℕ × ℕ => ab.1 + ab.2 ≠ N))
    (fun ab : ℕ × ℕ => Odd (ab.1 + ab.2))
    (fun ab =>
      lambdaPairWeight ab *
        positivePart
          (explicitMajorMaskSincKernel M P R
            ((N : ℤ) - (ab.1 : ℤ) - (ab.2 : ℤ))).re)]
  congr 1
  apply Finset.sum_congr
  · ext ab
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hab, hNotOdd⟩
      exact ⟨hab, Nat.not_odd_iff_even.mp hNotOdd⟩
    · rintro ⟨hab, hEven⟩
      exact ⟨hab, Nat.not_odd_iff_even.mpr hEven⟩
  · intro ab hab
    rfl

/-- Total positive mass split into the unchanged diagonal reserve and the two
off-diagonal parity channels. -/
theorem explicitPositiveMass_eq_diagonal_add_odd_add_even
    (M P R N : ℕ) :
    explicitPositiveMass M P R N =
      explicitDiagonalPositiveReserve M P R N +
        (explicitPositiveOddSumMass M P R N +
          explicitPositiveEvenSumMass M P R N) := by
  unfold explicitPositiveMass
  rw [explicitPositiveOffDiagonalMass_eq_odd_add_even]

/-- Odd-channel explicit Jordan deficit. -/
noncomputable def explicitOddChannelDeficit
    (M P R N : ℕ) : ℝ :=
  explicitNegativeOddSumMass M P R N -
    explicitPositiveOddSumMass M P R N

/-- Even-channel explicit Jordan deficit.  The diagonal positive reserve stays
in this channel because an even target has zero (hence even) diagonal shift. -/
noncomputable def explicitEvenChannelDeficit
    (M P R N : ℕ) : ℝ :=
  explicitNegativeEvenSumMass M P R N -
    (explicitDiagonalPositiveReserve M P R N +
      explicitPositiveEvenSumMass M P R N)

/-- Exact partition of the total negative-minus-positive mass deficit. -/
theorem explicitMassDeficit_eq_odd_add_even
    (M P R N : ℕ) :
    explicitNegativeMass M P R N - explicitPositiveMass M P R N =
      explicitOddChannelDeficit M P R N +
        explicitEvenChannelDeficit M P R N := by
  rw [explicitNegativeMass_eq_odd_add_even]
  rw [explicitPositiveMass_eq_diagonal_add_odd_add_even]
  unfold explicitOddChannelDeficit explicitEvenChannelDeficit
  ring

/-- Exact parity-channel form of the actual Minor real part. -/
theorem actual_minor_real_eq_neg_odd_add_even_deficit
    (M P R N : ℕ) (hscale : 2 * P * R < M) :
    GoldbachCircleMethodTwoScaleIntegralPartitionV1831.twoScaleMinorIntegralReal
        M P R N =
      -(explicitOddChannelDeficit M P R N +
        explicitEvenChannelDeficit M P R N) := by
  rw [actual_minor_real_eq_explicitPositiveMass_sub_explicitNegativeMass
    M P R N hscale]
  rw [← explicitMassDeficit_eq_odd_add_even]
  ring

/-- For an even target in the original range, the actual-Major overshoot is
exactly the positive part of the sum of the two explicit parity deficits.
Evenness is carried in the contract because the channels are intended for the
Goldbach target block; no estimate is inferred from it here. -/
theorem actualMajorOvershoot_eq_max_parityChannelDeficit
    (M P R N : ℕ) (hNM : N ≤ M) (hscale : 2 * P * R < M)
    (_hEven : Even N) :
    actualMajorOvershoot M P R N =
      max (explicitOddChannelDeficit M P R N +
        explicitEvenChannelDeficit M P R N) 0 := by
  rw [actualMajorOvershoot_eq_max_explicitMassDeficit M P R N hNM hscale]
  rw [explicitMassDeficit_eq_odd_add_even]

end GoldbachCircleMethodExplicitJordanParitySplitV18652
