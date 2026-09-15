import GoldbachCircleMethodTotientFourthEulerExponentBoundV18570

/-!
# Goldbach V1.8.571: uniform linear fourth-moment prefix bound

This closes the finite reciprocal-kernel gate with the explicit, conservative
constant `exp 30`.  The result is a linear-in-`Q` upper bound for the fourth
moment of the totient-ratio envelope.  No source-energy absorption and no
Goldbach conclusion is asserted.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodTotientFourthLinearPrefixBoundV18571

open GoldbachCircleMethodCollisionTotientFourthMomentTransferV18560
open GoldbachCircleMethodTotientFourthSquarefreeKernelV18567
open GoldbachCircleMethodTotientFourthEulerExponentialV18569
open GoldbachCircleMethodTotientFourthEulerExponentBoundV18570

/-- Uniform finite squarefree-kernel prefix bound. -/
theorem squarefreeKernelPrefix_le_exp_thirty (Q : ℕ) :
    (∑ d ∈ Finset.Icc 1 Q,
      squarefreeReciprocalTotientFourthKernel d) ≤ Real.exp 30 := by
  calc
    (∑ d ∈ Finset.Icc 1 Q,
      squarefreeReciprocalTotientFourthKernel d) ≤
        Real.exp (primeFourthEulerExponent Q) :=
      squarefreeKernelPrefix_le_exp Q
    _ ≤ Real.exp 30 :=
      Real.exp_le_exp.mpr (primeFourthEulerExponent_le_thirty Q)

/-- Closed target of the V1.8.564--V1.8.571 chain: the fourth moment of the
totient-ratio envelope is at most `exp 30 * Q`. -/
theorem totientRatioFourthMoment_le_exp_thirty_mul_Q (Q : ℕ) :
    totientRatioFourthMoment Q ≤ Real.exp 30 * (Q : ℝ) := by
  calc
    totientRatioFourthMoment Q ≤
        (Q : ℝ) *
          ∑ d ∈ Finset.Icc 1 Q,
            squarefreeReciprocalTotientFourthKernel d :=
      totientRatioFourthMoment_le_Q_mul_squarefree_kernel Q
    _ ≤ (Q : ℝ) * Real.exp 30 := by
      exact mul_le_mul_of_nonneg_left
        (squarefreeKernelPrefix_le_exp_thirty Q) (Nat.cast_nonneg Q)
    _ = Real.exp 30 * (Q : ℝ) := by ring

end GoldbachCircleMethodTotientFourthLinearPrefixBoundV18571
