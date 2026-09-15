import GoldbachCircleMethodTotientFourthLinearPrefixBoundV18571

/-!
# Goldbach V1.8.572: collision transfer using the closed linear moment bound

The V1.8.571 arithmetic moment estimate is inserted into the literal
common-denominator collision chain.  The result exposes one remaining source
product energy and the explicit polynomial cost `Q^4`.  No smallness or
absorption of that source energy is asserted.
-/

set_option autoImplicit false

open scoped BigOperators Classical ComplexConjugate

namespace GoldbachCircleMethodCollisionLinearMomentTransferV18572

open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodCollisionCommonDenominatorTransferV18558
open GoldbachCircleMethodCollisionCommonDenominatorTotientRatioV18557
open GoldbachCircleMethodCollisionOneDimensionalDenominatorEnergyV18559
open GoldbachCircleMethodCollisionTotientFourthMomentTransferV18560
open GoldbachCircleMethodCrossDenominatorCollisionPartitionV18547
open GoldbachCircleMethodLogCutoffPresieveBindingV18120
open GoldbachCircleMethodPrimitiveBaseSlotEnergyV18474
open GoldbachCircleMethodTotientFourthLinearPrefixBoundV18571

/-- The exact source-product energy left after removing the arithmetic
totient-ratio moment. -/
noncomputable def collisionPrimitiveSourceProductEnergy
    (Q B : ℕ) (H V : ℝ) (r s : PositiveLevel Q) : ℝ :=
  ∑ N ∈ blockCarrier B,
    ∑ ψ : {ψ : DirichletCharacter ℂ s.val // ψ.IsPrimitive},
      ∑ χ : {χ : DirichletCharacter ℂ r.val // χ.IsPrimitive},
        V ^ 4 *
          ‖primitiveBaseSlotSource Q B N H ⟨r, χ⟩‖ ^ 2 *
          ‖primitiveBaseSlotSource Q B N H ⟨s, ψ⟩‖ ^ 2

theorem collisionPrimitiveSourceProductEnergy_nonneg
    (Q B : ℕ) (H V : ℝ) (r s : PositiveLevel Q) :
    0 ≤ collisionPrimitiveSourceProductEnergy Q B H V r s := by
  unfold collisionPrimitiveSourceProductEnergy
  positivity

/-- The moment envelope is bounded by the closed linear moment constant times
the unchanged source-product energy. -/
theorem collisionTotientFourthMomentEnvelopeEnergy_le_linear_source_product
    (Q B : ℕ) (H V : ℝ) (r s : PositiveLevel Q) :
    collisionTotientFourthMomentEnvelopeEnergy Q B H V r s ≤
      (Real.exp 30 * (Q : ℝ)) *
        collisionPrimitiveSourceProductEnergy Q B H V r s := by
  have hfactor :
      collisionTotientFourthMomentEnvelopeEnergy Q B H V r s =
        GoldbachCircleMethodCollisionTotientFourthMomentTransferV18560.totientRatioFourthMoment Q *
          collisionPrimitiveSourceProductEnergy Q B H V r s := by
    unfold collisionTotientFourthMomentEnvelopeEnergy
      collisionPrimitiveSourceProductEnergy
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro N _hN
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ψ _hψ
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro χ _hχ
    ring
  rw [hfactor]
  exact mul_le_mul_of_nonneg_right
    (totientRatioFourthMoment_le_exp_thirty_mul_Q Q)
    (collisionPrimitiveSourceProductEnergy_nonneg Q B H V r s)

/-- End-to-end collision bound after the uniform arithmetic moment closure.
The only unabsorbed object is the explicit source-product energy. -/
theorem collisionLiteralCrossBlockCorrelation_sq_le_exp_thirty_Q_four_source
    (Q B : ℕ) (H V : ℝ) (w : ℕ → ℂ)
    (r s : PositiveLevel Q)
    (hw : ∀ n, ‖w n‖ ≤ V) :
    (collisionLiteralCrossBlockCorrelation Q B H w r s) ^ 2 ≤
      Real.exp 30 * (B : ℝ) * (Q : ℝ) ^ 4 *
        collisionPrimitiveSourceProductEnergy Q B H V r s := by
  have hfactor : 0 ≤ (B : ℝ) * (Q : ℝ) ^ 3 := by positivity
  calc
    (collisionLiteralCrossBlockCorrelation Q B H w r s) ^ 2 ≤
        (B : ℝ) * (Q : ℝ) ^ 3 *
          collisionCommonDenominatorRatioEnvelopeEnergy Q B H V r s :=
      collisionLiteralCrossBlockCorrelation_sq_le_commonDenominatorEnvelope
        Q B H V w r s hw
    _ ≤ (B : ℝ) * (Q : ℝ) ^ 3 *
          collisionOneDimensionalDenominatorRatioEnvelopeEnergy Q B H V r s :=
      mul_le_mul_of_nonneg_left
        (collisionCommonDenominatorRatioEnvelopeEnergy_le_oneDimensional
          Q B H V r s) hfactor
    _ ≤ (B : ℝ) * (Q : ℝ) ^ 3 *
          collisionTotientFourthMomentEnvelopeEnergy Q B H V r s :=
      mul_le_mul_of_nonneg_left
        (collisionOneDimensionalDenominatorRatioEnvelopeEnergy_le_moment
          Q B H V r s) hfactor
    _ ≤ (B : ℝ) * (Q : ℝ) ^ 3 *
          ((Real.exp 30 * (Q : ℝ)) *
            collisionPrimitiveSourceProductEnergy Q B H V r s) :=
      mul_le_mul_of_nonneg_left
        (collisionTotientFourthMomentEnvelopeEnergy_le_linear_source_product
          Q B H V r s) hfactor
    _ = Real.exp 30 * (B : ℝ) * (Q : ℝ) ^ 4 *
          collisionPrimitiveSourceProductEnergy Q B H V r s := by ring

end GoldbachCircleMethodCollisionLinearMomentTransferV18572
