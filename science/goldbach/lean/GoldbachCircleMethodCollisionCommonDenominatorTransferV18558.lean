import GoldbachCircleMethodCollisionCommonDenominatorTotientRatioV18557

/-!
# Goldbach V1.8.558: end-to-end collision transfer to the common denominator

This module composes the already checked carrier-sparsity, literal-atom,
weight-factorization, coefficient-envelope, and common-denominator steps.
The actual collision block is thereby reduced to an explicit finite energy
whose only arithmetic loss is the fourth power of `d / phi(d)` on the common
product denominator `d = r*l = s*k`.  No bound for that final energy is
claimed here.
-/

set_option autoImplicit false

open scoped BigOperators Classical ComplexConjugate

namespace GoldbachCircleMethodCollisionCommonDenominatorTransferV18558

open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodCollisionCommonDenominatorTotientRatioV18557
open GoldbachCircleMethodCollisionLiteralAtomEnvelopeV18554
open GoldbachCircleMethodCollisionLiteralBlockEnergyV18552
open GoldbachCircleMethodCollisionLiteralCutoffEnvelopeV18553
open GoldbachCircleMethodCollisionLiteralSliceEnergyV18551
open GoldbachCircleMethodCollisionLiteralWeightFactorizationV18555
open GoldbachCircleMethodCollisionTotientRatioEnvelopeV18556
open GoldbachCircleMethodCrossDenominatorCollisionPartitionV18547
open GoldbachCircleMethodPrimitiveBaseSlotEnergyV18474

/-- The genuine literal collision energy is bounded by the exact
common-denominator totient-ratio envelope. -/
theorem collisionLiteralBlockEnergy_le_commonDenominatorRatioEnvelope
    (Q B : ℕ) (H V : ℝ) (w : ℕ → ℂ)
    (r s : PositiveLevel Q)
    (hw : ∀ n, ‖w n‖ ≤ V) :
    collisionLiteralBlockEnergy Q B H w r s ≤
      collisionCommonDenominatorRatioEnvelopeEnergy Q B H V r s := by
  calc
    collisionLiteralBlockEnergy Q B H w r s ≤
        collisionLiteralAtomEnvelopeEnergy Q B H w r s :=
      collisionLiteralBlockEnergy_le_atomEnvelope Q B H w r s
    _ = collisionLiteralFactoredEnvelopeEnergy Q B H w r s :=
      collisionLiteralAtomEnvelopeEnergy_eq_factored Q B H w r s
    _ ≤ collisionLiteralTotientRatioEnvelopeEnergy Q B H V r s :=
      collisionLiteralFactoredEnvelopeEnergy_le_totientRatioEnvelope
        Q B H V w r s hw
    _ = collisionCommonDenominatorRatioEnvelopeEnergy Q B H V r s :=
      collisionLiteralTotientRatioEnvelopeEnergy_eq_commonDenominator
        Q B H V r s

/-- The actual conductor-pair correlation inherits the earlier `B*Q^3`
carrier factor and no additional complement-level polynomial loss. -/
theorem collisionLiteralCrossBlockCorrelation_sq_le_commonDenominatorEnvelope
    (Q B : ℕ) (H V : ℝ) (w : ℕ → ℂ)
    (r s : PositiveLevel Q)
    (hw : ∀ n, ‖w n‖ ≤ V) :
    (collisionLiteralCrossBlockCorrelation Q B H w r s) ^ 2 ≤
      (B : ℝ) * (Q : ℝ) ^ 3 *
        collisionCommonDenominatorRatioEnvelopeEnergy Q B H V r s := by
  have hfactor : 0 ≤ (B : ℝ) * (Q : ℝ) ^ 3 := by positivity
  calc
    _ ≤ (B : ℝ) * (Q : ℝ) ^ 3 *
        collisionLiteralBlockEnergy Q B H w r s :=
      collisionLiteralCrossBlockCorrelation_sq_le_B_mul_Q_cubed_energy
        Q B H w r s
    _ ≤ (B : ℝ) * (Q : ℝ) ^ 3 *
        collisionCommonDenominatorRatioEnvelopeEnergy Q B H V r s :=
      mul_le_mul_of_nonneg_left
        (collisionLiteralBlockEnergy_le_commonDenominatorRatioEnvelope
          Q B H V w r s hw) hfactor

end GoldbachCircleMethodCollisionCommonDenominatorTransferV18558
