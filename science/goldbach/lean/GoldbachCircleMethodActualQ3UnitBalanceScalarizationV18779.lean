import GoldbachCircleMethodActualQ3SignedProfileVariationCorrelationV18777

/-!
# V1.8.779: scalarization of the actual q=3 unit-balance obstruction

The post-local-density q=3 discrepancy is not a three-class quantity.  Its
zero-class contribution vanishes identically and the two unit-class deviations
are opposite half-differences.  Consequently the complete L1 budget is exactly
the norm of one scalar arithmetic discrepancy.

This is an exact finite-source reduction.  It does not estimate the scalar
discrepancy and does not decide Goldbach.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

open scoped BigOperators Classical ArithmeticFunction.vonMangoldt

namespace GoldbachCircleMethodActualQ3UnitBalanceScalarizationV18779

open GoldbachCircleMethodActualOddLambdaQ3ResidueDiscrepancyV18752
open GoldbachCircleMethodActualQ3PrefixLocalDensityExtractionV18753
open GoldbachCircleMethodActualQ3SignedProfileVariationCorrelationV18777

/-- The sole scalar discrepancy left after exact q=3 local-density
extraction. -/
noncomputable def oddLambdaQ3UnitResidueDifference
    (M B : Nat) : Complex :=
  oddLambdaQ3ResidueMass M B (1 : ZMod 3) -
    oddLambdaQ3ResidueMass M B (2 : ZMod 3)

/-- Exact scalarization of the complete post-extraction L1 budget. -/
theorem oddLambdaQ3UnitBalanceL1_eq_norm_unitResidueDifference
    (M B : Nat) :
    oddLambdaQ3UnitBalanceL1 M B =
      ‖oddLambdaQ3UnitResidueDifference M B‖ := by
  classical
  unfold oddLambdaQ3UnitBalanceL1 oddLambdaQ3UnitResidueDifference
  have huniv : (Finset.univ : Finset (ZMod 3)) = {0, 1, 2} := by
    decide
  rw [huniv]
  rw [Finset.sum_insert (by decide : (0 : ZMod 3) ∉ ({1, 2} : Finset (ZMod 3)))]
  rw [Finset.sum_insert (by decide : (1 : ZMod 3) ∉ ({2} : Finset (ZMod 3)))]
  simp only [Finset.sum_singleton]
  norm_num [oddLambdaQ3LocalDensityReferenceMass, oddLambdaQ3UnitMean]
  rw [show
      oddLambdaQ3ResidueMass M B 1 -
          (oddLambdaQ3ResidueMass M B 1 +
            oddLambdaQ3ResidueMass M B 2) / 2 =
        (oddLambdaQ3ResidueMass M B 1 -
          oddLambdaQ3ResidueMass M B 2) / 2 by ring]
  rw [if_neg (by decide : (2 : ZMod 3) ≠ 0)]
  rw [show
      oddLambdaQ3ResidueMass M B 2 -
          (oddLambdaQ3ResidueMass M B 1 +
            oddLambdaQ3ResidueMass M B 2) / 2 =
        -(oddLambdaQ3ResidueMass M B 1 -
          oddLambdaQ3ResidueMass M B 2) / 2 by ring]
  rw [norm_div, norm_div, norm_neg]
  norm_num

/-- The scalar discrepancy is real on the literal von-Mangoldt source. -/
theorem oddLambdaQ3UnitResidueDifference_im_eq_zero
    (M B : Nat) :
    (oddLambdaQ3UnitResidueDifference M B).im = 0 := by
  simp [oddLambdaQ3UnitResidueDifference, Complex.sub_im,
    oddLambdaQ3ResidueMass_im_eq_zero]

/-- Real coordinate of the sole post-extraction arithmetic obstruction. -/
noncomputable def oddLambdaQ3UnitResidueDifferenceReal
    (M B : Nat) : Real :=
  (oddLambdaQ3UnitResidueDifference M B).re

theorem oddLambdaQ3UnitResidueDifference_eq_ofReal
    (M B : Nat) :
    oddLambdaQ3UnitResidueDifference M B =
      (oddLambdaQ3UnitResidueDifferenceReal M B : Complex) := by
  apply Complex.ext
  · rfl
  · simpa [oddLambdaQ3UnitResidueDifferenceReal] using
      oddLambdaQ3UnitResidueDifference_im_eq_zero M B

/-- Fully real scalar form of the exact L1 discrepancy. -/
theorem oddLambdaQ3UnitBalanceL1_eq_abs_unitResidueDifferenceReal
    (M B : Nat) :
    oddLambdaQ3UnitBalanceL1 M B =
      |oddLambdaQ3UnitResidueDifferenceReal M B| := by
  rw [oddLambdaQ3UnitBalanceL1_eq_norm_unitResidueDifference,
    oddLambdaQ3UnitResidueDifference_eq_ofReal]
  simp

/-- Scalar ceiling contract equivalent to the former three-class L1
interface.  This definition introduces no new hypothesis. -/
def ActualOddLambdaQ3UnitResidueDifferenceCeiling
    (M : Nat) (D : Real) : Prop :=
  0 ≤ D ∧ ∀ B : Nat,
    |oddLambdaQ3UnitResidueDifferenceReal M B| ≤ D

theorem actualOddLambdaQ3UnitBalanceCeiling_iff_scalarCeiling
    (M : Nat) (D : Real) :
    ActualOddLambdaQ3UnitBalanceCeiling M D ↔
      ActualOddLambdaQ3UnitResidueDifferenceCeiling M D := by
  constructor
  · rintro ⟨hD, h⟩
    exact ⟨hD, fun B => by
      rw [← oddLambdaQ3UnitBalanceL1_eq_abs_unitResidueDifferenceReal]
      exact h B⟩
  · rintro ⟨hD, h⟩
    exact ⟨hD, fun B => by
      rw [oddLambdaQ3UnitBalanceL1_eq_abs_unitResidueDifferenceReal]
      exact h B⟩

end GoldbachCircleMethodActualQ3UnitBalanceScalarizationV18779
