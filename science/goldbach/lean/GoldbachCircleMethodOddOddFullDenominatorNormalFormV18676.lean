import GoldbachCircleMethodOddOddExactSignedBudgetV18669

/-!
# V1.8.676: exact full-denominator Odd-Odd normal form

This append-only module packages the already kernel-checked V1.8.649,
V1.8.665, V1.8.667, and V1.8.669 composition chain as one literal
project-normalized identity.

The right-hand side retains the exact diagonal reserve and the complete signed
Ramanujan--sinc denominator sum inside every off-diagonal Odd-Odd fiber.  No
denominator split, absolute value, triangle inequality, Cauchy inequality,
analytic estimate, or artificial residual is introduced.

The final equivalence only transports the unchanged V1.8.669 one-sided moment
target to this expanded normal form.  It does not inhabit that target.

`proof_status = NO_PROOF`.
-/

set_option autoImplicit false

open scoped BigOperators Classical

open GoldbachCircleMethodExceptionalTransferV1823
open GoldbachCircleMethodTwoScaleEvenBlockDefectReserveV1833
open GoldbachCircleMethodOddChannelEventualAbsorptionV18658
open GoldbachCircleMethodOriginalMaskModelBindingV1859
open GoldbachCircleMethodExplicitOffDiagonalKernelLeakageV18649
open GoldbachCircleMethodOddOddSignedFiberAdapterV18665
open GoldbachCircleMethodDiagonalCompensatedEvenSubchannelsV18667
open GoldbachCircleMethodOddOddExactSignedBudgetV18669

namespace GoldbachCircleMethodOddOddFullDenominatorNormalFormV18676

/-- The literal project-schedule normal form.  The diagonal zero mode remains
in its exact Minor-mask reserve, while every nonzero Odd-Odd fiber retains the
complete signed denominator kernel. -/
noncomputable def projectOddOddFullDenominatorNormalForm
    (M N : Nat) : Real :=
  explicitDiagonalOddOddReserve M
      (oddProjectWidth M) (oddProjectRadius M) N -
    ∑ t ∈ oddOddOffDiagonalSumCarrier M N,
      oddOddPairFiberMass M t *
        (explicitMajorMaskSincKernel M
          (oddProjectWidth M) (oddProjectRadius M)
          ((N : Int) - (t : Int))).re

/-- Definitional exposure of the complete denominator carrier.  Since
`Denominator R` is the subtype `q in Finset.Icc 1 R`, the sum contains every
and only denominator `1 <= q <= R`. -/
theorem explicitMajorMaskSincKernel_eq_fullDenominatorSum
    (M P R : Nat) (k : Int) :
    explicitMajorMaskSincKernel M P R k =
      ∑ q : Denominator R,
        explicitDenominatorSincTerm M P R k q := by
  rfl

/-- Exact full-denominator normal form for the canonical V1.8.669 project
coefficient.  This is only the existing composition chain in one theorem. -/
theorem projectOddOddCoefficient_eq_fullDenominatorNormalForm
    (M N : Nat)
    (hscale : 2 * oddProjectWidth M * oddProjectRadius M < M) :
    projectOddOddCoefficient M N =
      projectOddOddFullDenominatorNormalForm M N := by
  rw [← neg_compensatedOddOddDeficit_eq_projectCoefficient M N hscale]
  unfold projectOddOddFullDenominatorNormalForm compensatedOddOddDeficit
  rw [explicitOddOddSubchannelDeficit_eq_signed_fibers]
  ring

/-- The same identity with the inner `q=1,...,R` sum exposed syntactically.
No estimate or reordering of the two finite sums occurs. -/
theorem projectOddOddCoefficient_eq_expandedRamanujanSincSum
    (M N : Nat)
    (hscale : 2 * oddProjectWidth M * oddProjectRadius M < M) :
    projectOddOddCoefficient M N =
      explicitDiagonalOddOddReserve M
          (oddProjectWidth M) (oddProjectRadius M) N -
        ∑ t ∈ oddOddOffDiagonalSumCarrier M N,
          oddOddPairFiberMass M t *
            (∑ q : Denominator (oddProjectRadius M),
              explicitDenominatorSincTerm M
                (oddProjectWidth M) (oddProjectRadius M)
                ((N : Int) - (t : Int)) q).re := by
  rw [projectOddOddCoefficient_eq_fullDenominatorNormalForm M N hscale]
  unfold projectOddOddFullDenominatorNormalForm
  simp_rw [explicitMajorMaskSincKernel_eq_fullDenominatorSum]

/-- Exact transport of the canonical one-sided moment target to the complete
normal form.  The proof is function equality only: no pointwise or moment
inequality is used. -/
theorem projectOddOdd_moment_target_iff_fullDenominatorNormalForm
    (M : Nat)
    (hscale : 2 * oddProjectWidth M * oddProjectRadius M < M) :
    (negativePartSquaredMoment (evenTargetBlock M)
        (projectOddOddCoefficient M) < (M : Real) ^ 2 / 12544) <->
      (negativePartSquaredMoment (evenTargetBlock M)
        (projectOddOddFullDenominatorNormalForm M) <
          (M : Real) ^ 2 / 12544) := by
  have hfun :
      projectOddOddCoefficient M =
        projectOddOddFullDenominatorNormalForm M := by
    funext N
    exact projectOddOddCoefficient_eq_fullDenominatorNormalForm M N hscale
  rw [hfun]

end GoldbachCircleMethodOddOddFullDenominatorNormalFormV18676
