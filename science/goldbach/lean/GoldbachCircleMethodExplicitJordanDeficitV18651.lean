import GoldbachCircleMethodExplicitOffDiagonalKernelLeakageV18649
import GoldbachCircleMethodExactKernelJordanBalanceV18650

/-!
# V1.8.651: exact explicit Jordan deficit

This module resolves the sign convention left implicit between V1.8.649 and
V1.8.650.  At every off-diagonal shift and under `2 * P * R < M`, the Minor
kernel is the negative of the explicit Major Ramanujan--sinc kernel.  Thus the
positive off-diagonal Minor mass uses the negative part of the real explicit
Major coefficient, while the negative Minor mass is exactly the V1.8.649 sum
of its positive parts.

The diagonal positive reserve is kept exactly as the Haar mass of the Minor
mask times the diagonal von-Mangoldt pair mass.  It is proved nonnegative;
no strict positivity is asserted.  The original finite pair carrier and all
filters are unchanged.

No estimate or new analytic assumption is introduced.  The remaining task is
an arithmetic bound for the explicit nonnegative deficit.

`proof_status = NO_PROOF`.
-/
set_option autoImplicit false

open scoped BigOperators Classical
open MeasureTheory AddCircle
open GoldbachCircleMethodSignedMaskKernelConvolutionV1884
open GoldbachCircleMethodActualMajorOvershootIdentityV18630
open GoldbachCircleMethodActualOneSidedKernelLeakageV18648
open GoldbachCircleMethodExplicitOffDiagonalKernelLeakageV18649
open GoldbachCircleMethodExactKernelJordanBalanceV18650

namespace GoldbachCircleMethodExplicitJordanDeficitV18651

/-- Sign reversal exchanges the positive part with the negative part. -/
theorem positivePart_neg_eq_negativePart (x : ℝ) :
    positivePart (-x) =
      GoldbachCircleMethodExceptionalTransferV1823.negativePart x := by
  simp [positivePart, GoldbachCircleMethodExceptionalTransferV1823.negativePart]

/-- At a nonzero shift, the positive part of the Minor coefficient is exactly
the negative part of the explicit Major coefficient. -/
theorem positivePart_minorMaskKernel_re_eq_negativePart_explicitMajorMaskSincKernel
    (M P R : ℕ) (hscale : 2 * P * R < M) (k : ℤ) (hk : k ≠ 0) :
    positivePart (minorMaskKernel M P R k).re =
      GoldbachCircleMethodExceptionalTransferV1823.negativePart
        (explicitMajorMaskSincKernel M P R k).re := by
  rw [minorMaskKernel_eq_neg_explicitMajorMaskSincKernel M P R hscale k hk]
  simp only [Complex.neg_re]
  exact positivePart_neg_eq_negativePart _

/-- Off-diagonal positive Minor mass on the unchanged V1.8.649 pair carrier.
The sign-correct integrand is the negative part of the real explicit Major
Ramanujan--sinc coefficient. -/
noncomputable def explicitPositiveOffDiagonalMass
    (M P R N : ℕ) : ℝ :=
  ∑ ab ∈
      ((Finset.range M.succ).product (Finset.range M.succ)).filter
        (fun ab => ab.1 + ab.2 ≠ N),
    lambdaPairWeight ab *
      GoldbachCircleMethodExceptionalTransferV1823.negativePart
        (explicitMajorMaskSincKernel M P R
          ((N : ℤ) - (ab.1 : ℤ) - (ab.2 : ℤ))).re

theorem explicitPositiveOffDiagonalMass_nonneg (M P R N : ℕ) :
    0 ≤ explicitPositiveOffDiagonalMass M P R N := by
  unfold explicitPositiveOffDiagonalMass
  exact Finset.sum_nonneg fun ab _ =>
    mul_nonneg (lambdaPairWeight_nonneg ab) (negativePart_nonneg _)

/-- Exact diagonal positive reserve: Haar Minor-mask mass times the complete
diagonal von-Mangoldt pair mass. -/
noncomputable def explicitDiagonalPositiveReserve
    (M P R N : ℕ) : ℝ :=
  haarAddCircle.real
      (GoldbachCircleMethodTwoScaleIntegralPartitionV1831.twoScaleMinorMask
        M P R) *
    diagonalLambdaPairMass M N

theorem explicitDiagonalPositiveReserve_eq_haar_mul_diagonalLambdaPairMass
    (M P R N : ℕ) :
    explicitDiagonalPositiveReserve M P R N =
      haarAddCircle.real
          (GoldbachCircleMethodTwoScaleIntegralPartitionV1831.twoScaleMinorMask
            M P R) *
        diagonalLambdaPairMass M N := by
  rfl

/-- The exact diagonal reserve is nonnegative.  No strict positivity follows
without an arithmetic lower bound for the diagonal von-Mangoldt mass. -/
theorem explicitDiagonalPositiveReserve_nonneg (M P R N : ℕ) :
    0 ≤ explicitDiagonalPositiveReserve M P R N := by
  unfold explicitDiagonalPositiveReserve
  rw [← diagonalPositiveKernelMass_eq_haar_mul_diagonalLambdaPairMass]
  exact diagonalPositiveKernelMass_nonneg M P R N

/-- Total explicit positive Minor mass: exact diagonal reserve plus the
sign-correct off-diagonal positive mass. -/
noncomputable def explicitPositiveMass (M P R N : ℕ) : ℝ :=
  explicitDiagonalPositiveReserve M P R N +
    explicitPositiveOffDiagonalMass M P R N

/-- Total explicit negative Minor mass, definitionally the V1.8.649 positive
part of the real explicit Major coefficient on the off-diagonal carrier. -/
noncomputable def explicitNegativeMass (M P R N : ℕ) : ℝ :=
  explicitOffDiagonalKernelLeakage M P R N

theorem explicitPositiveMass_nonneg (M P R N : ℕ) :
    0 ≤ explicitPositiveMass M P R N := by
  unfold explicitPositiveMass
  exact add_nonneg
    (explicitDiagonalPositiveReserve_nonneg M P R N)
    (explicitPositiveOffDiagonalMass_nonneg M P R N)

theorem explicitNegativeMass_eq_explicitOffDiagonalKernelLeakage
    (M P R N : ℕ) :
    explicitNegativeMass M P R N =
      explicitOffDiagonalKernelLeakage M P R N := by
  rfl

theorem explicitNegativeMass_nonneg (M P R N : ℕ) :
    0 ≤ explicitNegativeMass M P R N := by
  unfold explicitNegativeMass
  exact explicitOffDiagonalKernelLeakage_nonneg M P R N

/-- The V1.8.650 positive kernel mass is exactly the explicit diagonal reserve
plus the sign-correct explicit off-diagonal positive mass. -/
theorem positiveKernelMass_eq_explicitPositiveMass
    (M P R N : ℕ) (hscale : 2 * P * R < M) :
    positiveKernelMass M P R N = explicitPositiveMass M P R N := by
  classical
  unfold positiveKernelMass explicitPositiveMass
    explicitDiagonalPositiveReserve explicitPositiveOffDiagonalMass
  rw [← diagonalPositiveKernelMass_eq_haar_mul_diagonalLambdaPairMass]
  unfold diagonalPositiveKernelMass
  rw [← Finset.sum_filter_add_sum_filter_not
    ((Finset.range M.succ).product (Finset.range M.succ))
    (fun ab : ℕ × ℕ => ab.1 + ab.2 = N)
    (fun ab =>
      lambdaPairWeight ab *
        positivePart
          (minorMaskKernel M P R
            ((N : ℤ) - (ab.1 : ℤ) - (ab.2 : ℤ))).re)]
  congr 1
  apply Finset.sum_congr rfl
  intro ab hab
  have hsum : ab.1 + ab.2 ≠ N := (Finset.mem_filter.mp hab).2
  have hshift : (N : ℤ) - (ab.1 : ℤ) - (ab.2 : ℤ) ≠ 0 := by
    intro hz
    apply hsum
    omega
  rw [positivePart_minorMaskKernel_re_eq_negativePart_explicitMajorMaskSincKernel
    M P R hscale _ hshift]

/-- Exact explicit Jordan decomposition of the actual Minor real part. -/
theorem actual_minor_real_eq_explicitPositiveMass_sub_explicitNegativeMass
    (M P R N : ℕ) (hscale : 2 * P * R < M) :
    GoldbachCircleMethodTwoScaleIntegralPartitionV1831.twoScaleMinorIntegralReal
        M P R N =
      explicitPositiveMass M P R N - explicitNegativeMass M P R N := by
  rw [actual_minor_real_eq_positiveKernelMass_sub_negativeKernelLeakage]
  rw [positiveKernelMass_eq_explicitPositiveMass M P R N hscale]
  rw [negativeKernelLeakage_eq_explicitOffDiagonalKernelLeakage
    M P R N hscale]
  rfl

/-- For `N ≤ M`, the actual Major overshoot is exactly the positive part of
the explicit negative-minus-positive Minor mass deficit. -/
theorem actualMajorOvershoot_eq_max_explicitMassDeficit
    (M P R N : ℕ) (hNM : N ≤ M) (hscale : 2 * P * R < M) :
    actualMajorOvershoot M P R N =
      max (explicitNegativeMass M P R N - explicitPositiveMass M P R N) 0 := by
  rw [actualMajorOvershoot_eq_positivePart_kernelImbalance M P R N hNM]
  rw [negativeKernelLeakage_eq_explicitOffDiagonalKernelLeakage
    M P R N hscale]
  rw [positiveKernelMass_eq_explicitPositiveMass M P R N hscale]
  rfl

/-- Squared explicit Jordan deficit on an arbitrary finite target carrier. -/
noncomputable def explicitJordanDeficitSquaredMoment
    (M P R : ℕ) (s : Finset ℕ) : ℝ :=
  ∑ N ∈ s,
    (max (explicitNegativeMass M P R N - explicitPositiveMass M P R N) 0) ^ 2

/-- Exact squared-moment identity on any finite target carrier contained in
`Finset.range M.succ`. -/
theorem actualMajorOvershootSquaredMoment_eq_explicitJordanDeficitSquaredMoment
    (M P R : ℕ) (s : Finset ℕ)
    (hRange : ∀ N ∈ s, N ≤ M) (hscale : 2 * P * R < M) :
    actualMajorOvershootSquaredMoment M P R s =
      explicitJordanDeficitSquaredMoment M P R s := by
  unfold actualMajorOvershootSquaredMoment explicitJordanDeficitSquaredMoment
  apply Finset.sum_congr rfl
  intro N hN
  rw [actualMajorOvershoot_eq_max_explicitMassDeficit
    M P R N (hRange N hN) hscale]

end GoldbachCircleMethodExplicitJordanDeficitV18651
