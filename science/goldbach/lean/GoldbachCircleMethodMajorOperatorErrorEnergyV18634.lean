import GoldbachCircleMethodMajorOperatorErrorBesselV18633

/-!
# V1.8.634: Local-to-global energy bound for the actual Major-operator error

The original rational arcs are disjoint at the fixed scale.  Consequently the
assembled local model has exactly one active summand on the Major mask and no
active summand off the mask.  A uniform local approximation therefore bounds
the frequency-independent error function pointwise, and hence bounds its exact
`L²` energy without a target-carrier cardinality factor.

The approximation hypothesis remains open.  No estimate for it is asserted.

`proof_status = NO_PROOF`.
-/
set_option autoImplicit false

open scoped BigOperators Classical
open MeasureTheory AddCircle
open GoldbachCircleMethodFourierIdentityV171
open GoldbachCircleMethodMajorMinorPartitionV172
open GoldbachCircleMethodFixedScaleTransferV1824
open GoldbachCircleMethodTwoScaleMaskAdapterV1829
open GoldbachCircleMethodDiscreteMainKernelV1852
open GoldbachCircleMethodDiscreteArcModelReserveV1855
open GoldbachCircleMethodOriginalMaskDisjointnessV1860
open GoldbachCircleMethodActualOperatorErrorTransferV1861
open GoldbachCircleMethodMajorOperatorErrorBesselV18633

namespace GoldbachCircleMethodMajorOperatorErrorEnergyV18634

/-- The uniform pointwise square-error envelope induced by a local
approximation error `ε`. -/
def majorOperatorErrorEnvelope (M : ℕ) (ε : ℝ) : ℝ :=
  2 * (M : ℝ) * ε + ε ^ 2

/-- On a disjoint original arc, the assembled model collapses to its unique
local summand. -/
theorem assembledArcModelSquare_eq_local_of_mem (M P R : ℕ)
    (hscale : 2 * P * R < M) (i : ReducedRationalIndex R)
    (x : UnitAddCircle)
    (hx : x ∈ Metric.closedBall (majorArcCenter i) (twoScaleArcRadius M P i)) :
    assembledArcModelSquare M P R x = localArcModelSquare M P R i x := by
  classical
  unfold assembledArcModelSquare
  simp only [Finset.sum_apply]
  rw [Finset.sum_eq_single i]
  · intro j _hj hji
    have hdisjoint := original_closed_arcs_pairwise_disjoint M P R hscale hji
    have hxj : x ∉ Metric.closedBall (majorArcCenter j) (twoScaleArcRadius M P j) := by
      intro hxj
      exact Set.disjoint_left.mp hdisjoint hxj hx
    simp [localArcModelSquare, Set.indicator_of_notMem hxj]
  · simp

/-- Off the Major mask, every local model summand vanishes. -/
theorem assembledArcModelSquare_eq_zero_of_not_mem (M P R : ℕ)
    (x : UnitAddCircle) (hx : x ∉ twoScaleMajorMask M P R) :
    assembledArcModelSquare M P R x = 0 := by
  classical
  unfold assembledArcModelSquare
  simp only [Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro i _hi
  have hxi : x ∉ Metric.closedBall (majorArcCenter i) (twoScaleArcRadius M P i) := by
    intro hxi
    apply hx
    exact Set.mem_iUnion.mpr ⟨i, hxi⟩
  simp [localArcModelSquare, Set.indicator_of_notMem hxi]

/-- The operator-error function is supported on the unchanged Major mask. -/
theorem majorOperatorErrorFunction_eq_zero_of_not_mem (M P R : ℕ)
    (x : UnitAddCircle) (hx : x ∉ twoScaleMajorMask M P R) :
    majorOperatorErrorFunction M P R x = 0 := by
  unfold majorOperatorErrorFunction
  rw [Pi.sub_apply, assembledArcModelSquare_eq_zero_of_not_mem M P R x hx]
  simp [actualMajorSquare, Set.indicator_of_notMem hx]

/-- A uniform local approximation on every original arc gives a global
pointwise bound for the fixed error function. -/
theorem majorOperatorErrorFunction_norm_le_envelope
    (M P R : ℕ) (hscale : 2 * P * R < M) (ε : ℝ) (hε : 0 ≤ ε)
    (happrox : ∀ i : ReducedRationalIndex R,
      ∀ x ∈ Metric.closedBall (majorArcCenter i) (twoScaleArcRadius M P i),
        ‖exponentialSum M.succ x -
          (((ArithmeticFunction.moebius i.val.1 : ℤ) : ℂ) /
            (Nat.totient i.val.1 : ℂ)) *
              discreteMainPolynomial M (x - majorArcCenter i)‖ ≤ ε) :
    ∀ x : UnitAddCircle,
      ‖majorOperatorErrorFunction M P R x‖ ≤
        majorOperatorErrorEnvelope M ε := by
  intro x
  by_cases hx : x ∈ twoScaleMajorMask M P R
  · obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
    rw [show majorOperatorErrorFunction M P R x =
        exponentialSum M.succ x ^ 2 -
          (((((ArithmeticFunction.moebius i.val.1 : ℤ) : ℂ) /
              (Nat.totient i.val.1 : ℂ)) *
                discreteMainPolynomial M (x - majorArcCenter i)) ^ 2) by
      unfold majorOperatorErrorFunction
      rw [Pi.sub_apply, assembledArcModelSquare_eq_local_of_mem M P R hscale i x hxi]
      simp [actualMajorSquare, localArcModelSquare,
        Set.indicator_of_mem hx, Set.indicator_of_mem hxi, pow_two]]
    exact square_error_bound (exponentialSum M.succ x)
      ((((ArithmeticFunction.moebius i.val.1 : ℤ) : ℂ) /
          (Nat.totient i.val.1 : ℂ)) *
        discreteMainPolynomial M (x - majorArcCenter i)) (M : ℝ) ε
      (local_model_norm_le_cutoff M i.val.1 (index_denominator_pos i)
        (x - majorArcCenter i))
      (happrox i x hxi)
  · rw [majorOperatorErrorFunction_eq_zero_of_not_mem M P R x hx, norm_zero]
    unfold majorOperatorErrorEnvelope
    positivity

/-- The exact Major-operator error energy is controlled by the square of the
local envelope.  Bessel can therefore use this bound without multiplying by
the number of target frequencies. -/
theorem majorOperatorErrorEnergy_le_envelope_sq
    (M P R : ℕ) (hscale : 2 * P * R < M) (ε : ℝ) (hε : 0 ≤ ε)
    (happrox : ∀ i : ReducedRationalIndex R,
      ∀ x ∈ Metric.closedBall (majorArcCenter i) (twoScaleArcRadius M P i),
        ‖exponentialSum M.succ x -
          (((ArithmeticFunction.moebius i.val.1 : ℤ) : ℂ) /
            (Nat.totient i.val.1 : ℂ)) *
              discreteMainPolynomial M (x - majorArcCenter i)‖ ≤ ε) :
    majorOperatorErrorEnergy M P R ≤
      (majorOperatorErrorEnvelope M ε) ^ 2 := by
  unfold majorOperatorErrorEnergy
  calc
    _ ≤ ∫ _x : UnitAddCircle, majorOperatorErrorEnvelope M ε ^ 2
        ∂haarAddCircle := by
      apply integral_mono
        (majorOperatorErrorFunction_memLp_two M P R).integrable_norm_pow'
        (integrable_const (majorOperatorErrorEnvelope M ε ^ 2))
      intro x
      have h := majorOperatorErrorFunction_norm_le_envelope M P R hscale ε hε happrox x
      have hnorm := norm_nonneg (majorOperatorErrorFunction M P R x)
      have henvelope : 0 ≤ majorOperatorErrorEnvelope M ε := hnorm.trans h
      nlinarith
    _ = majorOperatorErrorEnvelope M ε ^ 2 := by simp

end GoldbachCircleMethodMajorOperatorErrorEnergyV18634
