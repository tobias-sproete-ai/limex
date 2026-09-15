import GoldbachCircleMethodActualOneSidedKernelLeakageV18648
import GoldbachCircleMethodExplicitMaskFourierKernelV1887

/-!
# V1.8.649: explicit off-diagonal kernel leakage

V1.8.648 reduces the actual Major overshoot to a finite weighted sum of
`negativePart (minorMaskKernel ... k).re`.  This module performs two exact
algebraic steps on that reduction.

First, the V1.8.87 denominator/Ramanujan formula and its nonzero-frequency
sine identity show that the Minor-mask kernel is the negative of the explicit
finite Major-mask Ramanujan--sinc kernel whenever `k != 0`.  Consequently the
negative part of the Minor coefficient is exactly the positive part of the
real Major coefficient; there is no absolute-value or triangle-inequality
loss in this step.

Second, the `a + b = N` convolution diagonal is removed from the V1.8.648
leakage sum.  Its contribution is zero by the existing zero-frequency
nonnegativity theorem.  Every remaining filtered pair has a nonzero integer
shift, so the exact Ramanujan--sinc rewrite applies term by term.

No bound on the resulting explicit off-diagonal finite sum is proved here.
This is an exact kernel exposure plus the existing V1.8.648 one-sided
reduction, not an analytic leakage estimate and not a Goldbach proof.

`proof_status = NO_PROOF`.
-/
set_option autoImplicit false

open scoped BigOperators Classical
open GoldbachCircleMethodSignedMaskKernelConvolutionV1884
open GoldbachCircleMethodExplicitMaskFourierKernelV1887
open GoldbachCircleMethodActualOneSidedKernelLeakageV18648

namespace GoldbachCircleMethodExplicitOffDiagonalKernelLeakageV18649

/-- The positive part used after the exact Minor/Major sign reversal. -/
noncomputable def positivePart (x : ℝ) : ℝ := max x 0

theorem positivePart_nonneg (x : ℝ) :
    0 <= positivePart x := by
  unfold positivePart
  exact le_max_right _ _

/-- Negative part after sign reversal is exactly the positive part. -/
theorem negativePart_neg_eq_positivePart (x : ℝ) :
    GoldbachCircleMethodExceptionalTransferV1823.negativePart (-x) =
      positivePart x := by
  simp [GoldbachCircleMethodExceptionalTransferV1823.negativePart, positivePart]

/-- The explicit finite Major-mask coefficient at frequency `k`: the exact
Ramanujan denominator sum from V1.8.87 with the centered arc integral written
as its sinc expression. -/
noncomputable def explicitMajorMaskSincKernel
    (M P R : ℕ) (k : ℤ) : ℂ :=
  ∑ q : GoldbachCircleMethodOriginalMaskModelBindingV1859.Denominator R,
    GoldbachCircleMethodSignedFullPrefixV1850.integerFourierRamanujan
        q.val (-k) (NeZero.ne q.val) *
      (((Real.sin
          (2 * Real.pi * (k : ℝ) *
            ((P : ℝ) / ((q.val : ℝ) * (M : ℝ)))) /
          (Real.pi * (k : ℝ))) : ℝ) : ℂ)

/-- At nonzero frequency the Minor-mask coefficient is exactly the negative
of the explicit finite Major-mask Ramanujan--sinc coefficient. -/
theorem minorMaskKernel_eq_neg_explicitMajorMaskSincKernel
    (M P R : ℕ) (hscale : 2 * P * R < M) (k : ℤ) (hk : k ≠ 0) :
    minorMaskKernel M P R k = -explicitMajorMaskSincKernel M P R k := by
  rw [explicit_denominator_mask_kernel M P R hscale k, if_neg hk]
  unfold explicitMajorMaskSincKernel
  simp_rw [centeredCharacterKernel_sine k hk]
  simp

/-- The sign-correct one-sided identity requested by the leakage reduction:
the negative part of the nonzero Minor coefficient equals the positive part
of the explicit Major-mask finite kernel. -/
theorem negativePart_minorMaskKernel_re_eq_positivePart_explicitMajorMaskSincKernel
    (M P R : ℕ) (hscale : 2 * P * R < M) (k : ℤ) (hk : k ≠ 0) :
    GoldbachCircleMethodExceptionalTransferV1823.negativePart
        (minorMaskKernel M P R k).re =
      positivePart (explicitMajorMaskSincKernel M P R k).re := by
  rw [minorMaskKernel_eq_neg_explicitMajorMaskSincKernel M P R hscale k hk]
  simp only [Complex.neg_re]
  exact negativePart_neg_eq_positivePart _

/-- Exact removal of the convolution diagonal from the V1.8.648 leakage.
The original ranges and pair weights are unchanged. -/
theorem negativeKernelLeakage_eq_offDiagonal
    (M P R N : ℕ) :
    negativeKernelLeakage M P R N =
      ∑ ab ∈
          ((Finset.range M.succ).product (Finset.range M.succ)).filter
            (fun ab => ab.1 + ab.2 ≠ N),
        lambdaPairWeight ab *
          GoldbachCircleMethodExceptionalTransferV1823.negativePart
            (minorMaskKernel M P R
              ((N : ℤ) - (ab.1 : ℤ) - (ab.2 : ℤ))).re := by
  classical
  unfold negativeKernelLeakage
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro ab hab
  by_cases hdiag : ab.1 + ab.2 = N
  · rw [if_neg]
    · exact diagonal_negativeKernelContribution_eq_zero
        M P R N ab.1 ab.2 hdiag
    · exact fun h => h hdiag
  · rw [if_pos hdiag]

/-- The exact explicit off-diagonal Ramanujan--sinc leakage.  The filter keeps
precisely the nonzero shifts of the original finite convolution carrier. -/
noncomputable def explicitOffDiagonalKernelLeakage
    (M P R N : ℕ) : ℝ :=
  ∑ ab ∈
      ((Finset.range M.succ).product (Finset.range M.succ)).filter
        (fun ab => ab.1 + ab.2 ≠ N),
    lambdaPairWeight ab *
      positivePart
        (explicitMajorMaskSincKernel M P R
          ((N : ℤ) - (ab.1 : ℤ) - (ab.2 : ℤ))).re

theorem explicitOffDiagonalKernelLeakage_nonneg
    (M P R N : ℕ) :
    0 <= explicitOffDiagonalKernelLeakage M P R N := by
  unfold explicitOffDiagonalKernelLeakage
  exact Finset.sum_nonneg fun ab _ =>
    mul_nonneg (lambdaPairWeight_nonneg ab) (positivePart_nonneg _)

/-- Exact V1.8.648 leakage rewritten as the filtered explicit Major-mask
Ramanujan--sinc leakage. -/
theorem negativeKernelLeakage_eq_explicitOffDiagonalKernelLeakage
    (M P R N : ℕ) (hscale : 2 * P * R < M) :
    negativeKernelLeakage M P R N =
      explicitOffDiagonalKernelLeakage M P R N := by
  rw [negativeKernelLeakage_eq_offDiagonal]
  unfold explicitOffDiagonalKernelLeakage
  apply Finset.sum_congr rfl
  intro ab hab
  have hsum : ab.1 + ab.2 ≠ N := (Finset.mem_filter.mp hab).2
  have hshift : (N : ℤ) - (ab.1 : ℤ) - (ab.2 : ℤ) ≠ 0 := by
    intro hz
    apply hsum
    omega
  rw [negativePart_minorMaskKernel_re_eq_positivePart_explicitMajorMaskSincKernel
    M P R hscale _ hshift]

/-- The actual Major overshoot is bounded by the exact filtered explicit
off-diagonal finite kernel leakage.  This imports only the V1.8.648
subadditivity loss; the kernel rewrite itself is an equality. -/
theorem actualMajorOvershoot_le_explicitOffDiagonalKernelLeakage
    (M P R N : ℕ) (hNM : N <= M) (hscale : 2 * P * R < M) :
    GoldbachCircleMethodActualMajorOvershootIdentityV18630.actualMajorOvershoot
        M P R N <=
      explicitOffDiagonalKernelLeakage M P R N := by
  rw [<- negativeKernelLeakage_eq_explicitOffDiagonalKernelLeakage
    M P R N hscale]
  exact actualMajorOvershoot_le_negativeKernelLeakage M P R N hNM

/-- Squared pointwise form, retaining nonnegativity of both sides. -/
theorem actualMajorOvershoot_sq_le_explicitOffDiagonalKernelLeakage_sq
    (M P R N : ℕ) (hNM : N <= M) (hscale : 2 * P * R < M) :
    (GoldbachCircleMethodActualMajorOvershootIdentityV18630.actualMajorOvershoot
        M P R N) ^ 2 <=
      (explicitOffDiagonalKernelLeakage M P R N) ^ 2 := by
  have hle := actualMajorOvershoot_le_explicitOffDiagonalKernelLeakage
    M P R N hNM hscale
  have hov : 0 <=
      GoldbachCircleMethodActualMajorOvershootIdentityV18630.actualMajorOvershoot
        M P R N := by
    unfold GoldbachCircleMethodActualMajorOvershootIdentityV18630.actualMajorOvershoot
    exact le_max_right _ _
  have hexp := explicitOffDiagonalKernelLeakage_nonneg M P R N
  nlinarith

/-- Finite squared explicit off-diagonal leakage on an arbitrary target
carrier, parallel to the V1.8.648 moment definition. -/
noncomputable def explicitOffDiagonalKernelLeakageSquaredMoment
    (M P R : ℕ) (s : Finset ℕ) : ℝ :=
  ∑ N ∈ s, (explicitOffDiagonalKernelLeakage M P R N) ^ 2

/-- The V1.8.648 leakage moment is exactly the explicit filtered
Ramanujan--sinc leakage moment under the unchanged scale separation. -/
theorem negativeKernelLeakageSquaredMoment_eq_explicitOffDiagonalKernelLeakageSquaredMoment
    (M P R : ℕ) (s : Finset ℕ) (hscale : 2 * P * R < M) :
    negativeKernelLeakageSquaredMoment M P R s =
      explicitOffDiagonalKernelLeakageSquaredMoment M P R s := by
  unfold negativeKernelLeakageSquaredMoment
    explicitOffDiagonalKernelLeakageSquaredMoment
  apply Finset.sum_congr rfl
  intro N _
  rw [negativeKernelLeakage_eq_explicitOffDiagonalKernelLeakage
    M P R N hscale]

/-- Corresponding finite squared-moment upper bound for the actual Major
overshoot, now with the convolution diagonal removed and every remaining
kernel coefficient exposed as an explicit Ramanujan--sinc positive part. -/
theorem actualMajorOvershootSquaredMoment_le_explicitOffDiagonalKernelLeakageSquaredMoment
    (M P R : ℕ) (s : Finset ℕ)
    (hRange : ∀ N ∈ s, N <= M) (hscale : 2 * P * R < M) :
    GoldbachCircleMethodActualMajorOvershootIdentityV18630.actualMajorOvershootSquaredMoment
        M P R s <=
      explicitOffDiagonalKernelLeakageSquaredMoment M P R s := by
  unfold GoldbachCircleMethodActualMajorOvershootIdentityV18630.actualMajorOvershootSquaredMoment
    explicitOffDiagonalKernelLeakageSquaredMoment
  exact Finset.sum_le_sum fun N hN =>
    actualMajorOvershoot_sq_le_explicitOffDiagonalKernelLeakage_sq
      M P R N (hRange N hN) hscale

end GoldbachCircleMethodExplicitOffDiagonalKernelLeakageV18649
