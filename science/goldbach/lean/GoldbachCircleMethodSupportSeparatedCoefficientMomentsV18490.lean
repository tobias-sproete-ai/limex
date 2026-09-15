import GoldbachCircleMethodSupportSeparatedSingleSourceGateV18489
import GoldbachCircleMethodPrimitiveBaseSpanEnvelopeV18478
import GoldbachCircleMethodPrincipalCoefficientAtomV18487

/-!
# Goldbach V1.8.490: support-separated coefficient moments

The remaining source budget is projected onto three explicit coefficient
moments.  Only the primitive-base channel retains the span envelope.  The
principal and exceptional corrections remain on their true sparse supports.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodSupportSeparatedCoefficientMomentsV18490

open GoldbachCircleMethodActiveExceptionalCenteringV18129
open GoldbachCircleMethodAdjustedCharacterSlotL2AdapterV18449
open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodLogCutoffPresieveBindingV18120
open GoldbachCircleMethodPrimitiveBaseSlotEnergyV18474
open GoldbachCircleMethodPrimitiveBaseSpanEnvelopeV18478
open GoldbachCircleMethodPrincipalSupportEnergySplitV18483
open GoldbachCircleMethodPrincipalWindowBoundaryV18121
open GoldbachCircleMethodSupportSeparatedSourceBudgetV18484

noncomputable def blockAdjustedCoefficientMoment
    (Q B : ℕ) (w : ℕ → ℂ) : ℝ :=
  ∑ n ∈ blockCarrier B, adjustedCoefficientEnergy Q n w

noncomputable def blockPrincipalCoefficientMoment
    (Q B : ℕ) (w : ℕ → ℂ) : ℝ :=
  ∑ n ∈ blockCarrier B, principalCoefficientEnergy Q n w

noncomputable def blockExceptionalCoefficientMoment
    (B : ℕ) (w : ℕ → ℂ) {Q : ℕ} (e : CharacterSlot Q) : ℝ :=
  ∑ n ∈ blockCarrier B, ‖windowCoefficient e.1 n w e.2‖ ^ 2

/-- The fully aggregated three-channel coefficient envelope. -/
noncomputable def supportSeparatedCoefficientEnvelope
    (Q B : ℕ) (H : ℝ) (w : ℕ → ℂ) (e : CharacterSlot Q) : ℝ :=
  primitiveBaseSpanEnvelope Q B H * blockAdjustedCoefficientMoment Q B w +
    (9 / 4 : ℝ) * blockPrincipalCoefficientMoment Q B w +
    (9 / 4 : ℝ) * blockExceptionalCoefficientMoment B w e

/-- Replacing the target-dependent primitive source energy by its sharp span
envelope leaves the sparse correction channels unchanged. -/
theorem supportSeparatedSourceBudget_le_coefficientEnvelope
    (B : ℕ) (rho b : ℝ)
    (e : CharacterSlot ⌊((B : ℝ) ^ rho) ^ 2⌋₊)
    (hB : 2 ≤ B)
    (hH : 0 ≤ (B : ℝ) / ((B : ℝ) ^ rho) ^ 4) :
    supportSeparatedSourceBudget B rho b e ≤
      supportSeparatedCoefficientEnvelope
        ⌊((B : ℝ) ^ rho) ^ 2⌋₊ B
        ((B : ℝ) / ((B : ℝ) ^ rho) ^ 4)
        (logWeight ((B : ℝ) ^ rho)
          GoldbachCircleMethodCanonicalBumpPrincipalFloorV18220.canonicalLogBump)
        e := by
  let Q := ⌊((B : ℝ) ^ rho) ^ 2⌋₊
  let H := (B : ℝ) / ((B : ℝ) ^ rho) ^ 4
  let w := logWeight ((B : ℝ) ^ rho)
    GoldbachCircleMethodCanonicalBumpPrincipalFloorV18220.canonicalLogBump
  have hprimitive (n : ℕ) :
      primitiveBaseSourceEnergy Q B n H ≤
        primitiveBaseSpanEnvelope Q B H :=
    primitiveBaseSourceEnergy_le_span_envelope Q B n H hB hH
  have hcoefficientNonneg (n : ℕ) :
      0 ≤ adjustedCoefficientEnergy Q n w := by
    unfold adjustedCoefficientEnergy
    positivity
  unfold supportSeparatedSourceBudget supportSeparatedCoefficientEnvelope
    blockAdjustedCoefficientMoment blockPrincipalCoefficientMoment
    blockExceptionalCoefficientMoment
  dsimp only [Q, H, w]
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro n _hn
  have hmul :
      adjustedCoefficientEnergy Q n w * primitiveBaseSourceEnergy Q B n H ≤
        adjustedCoefficientEnergy Q n w * primitiveBaseSpanEnvelope Q B H :=
    mul_le_mul_of_nonneg_left (hprimitive n) (hcoefficientNonneg n)
  calc
    adjustedCoefficientEnergy Q n w * primitiveBaseSourceEnergy Q B n H +
          (9 / 4 : ℝ) * principalCoefficientEnergy Q n w +
          (9 / 4 : ℝ) * ‖windowCoefficient e.1 n w e.2‖ ^ 2 ≤
        adjustedCoefficientEnergy Q n w * primitiveBaseSpanEnvelope Q B H +
          (9 / 4 : ℝ) * principalCoefficientEnergy Q n w +
          (9 / 4 : ℝ) * ‖windowCoefficient e.1 n w e.2‖ ^ 2 := by
      linarith
    _ = primitiveBaseSpanEnvelope Q B H * adjustedCoefficientEnergy Q n w +
          (9 / 4 : ℝ) * principalCoefficientEnergy Q n w +
          (9 / 4 : ℝ) * ‖windowCoefficient e.1 n w e.2‖ ^ 2 := by ring

/-- On a nonempty conductor cutoff, the principal block moment is exactly the
sum of squared canonical finite companions. -/
theorem blockPrincipalCoefficientMoment_eq_finiteCompanion
    (Q B : ℕ) (hQ : 1 ≤ Q) (w : ℕ → ℂ) :
    blockPrincipalCoefficientMoment Q B w =
      ∑ n ∈ blockCarrier B, ‖GoldbachCircleMethodFiniteCompanionBindingV18118.finiteCompanion
        (GoldbachCircleMethodPrincipalWindowBoundaryV18121.oneLevel hQ) n w‖ ^ 2 := by
  unfold blockPrincipalCoefficientMoment
  apply Finset.sum_congr rfl
  intro n _hn
  exact GoldbachCircleMethodPrincipalCoefficientAtomV18487.principalCoefficientEnergy_eq_finiteCompanion_sq
    Q n hQ w

end GoldbachCircleMethodSupportSeparatedCoefficientMomentsV18490
