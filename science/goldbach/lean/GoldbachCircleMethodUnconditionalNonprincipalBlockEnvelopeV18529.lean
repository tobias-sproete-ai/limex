import GoldbachCircleMethodNonprincipalAlignedBlockEnergyV18528
import GoldbachCircleMethodActualPrimitiveSourceEnergyV18473

/-!
# Goldbach V1.8.529: unconditional nonprincipal block envelope

The conductor-local primitive source energy is identified with the existing
raw source energy and bounded by the unconditional finite residue-collision
estimate.  Substitution into V1.8.528 closes an unconditional but deliberately
coarse nonprincipal block envelope.  No claim is made that this envelope is
small enough for Goldbach or for exceptional-set decay.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodUnconditionalNonprincipalBlockEnvelopeV18529

open GoldbachCircleMethodActualPrimitiveSourceEnergyV18473
open GoldbachCircleMethodActualPrimitiveSourceNormalizationV18470
open GoldbachCircleMethodActualWindowInputEnergyV18469
open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodFiniteWindowConvolutionV18119
open GoldbachCircleMethodLogCutoffPresieveBindingV18120
open GoldbachCircleMethodNonprincipalAlignedBlockEnergyV18528
open GoldbachCircleMethodNonprincipalConductorAlignedCorrelationV18527
open GoldbachCircleMethodNonprincipalConductorIntervalEnergyV18520
open GoldbachCircleMethodPrimitiveBaseSlotEnergyV18474

/-- Literal unconditional source cap inherited from the finite
residue-collision estimate. -/
noncomputable def explicitPrimitiveSourceCap
    {Q : ℕ} (B : ℕ) (H : ℝ) (q : PositiveLevel Q) : ℝ :=
  ‖(2 * (H : ℂ))⁻¹‖ ^ 2 *
    ((q.val.totient : ℝ) * (((B + 1) / q.val + 1 : ℕ) : ℝ) *
      ((2 * H + 1) * (Real.log (B : ℝ)) ^ 2))

/-- The conductor-local slot sum is exactly the pre-existing raw primitive
source energy at that conductor. -/
theorem conductorPrimitiveSourceEnergy_eq_raw
    (Q B N : ℕ) (H : ℝ) (q : PositiveLevel Q) :
    conductorPrimitiveSourceEnergy Q B N H q =
      rawPrimitiveSourceEnergy q.val B N H := by
  unfold conductorPrimitiveSourceEnergy primitiveBaseSlotSource
    rawPrimitiveSourceEnergy
  rw [← Finset.sum_subtype
    (Finset.univ.filter
      (fun chi : DirichletCharacter ℂ q.val => chi.IsPrimitive))
    (by simp)
    (fun chi =>
      ‖(2 * (H : ℂ))⁻¹ *
        ∑ U ∈ centeredWindow (blockCarrier B) N H,
          blockInput B U * star (chi (U : ZMod q.val))‖ ^ 2)]
  apply Finset.sum_congr rfl
  intro chi _hchi
  apply congrArg (fun z : ℂ => ‖(2 * (H : ℂ))⁻¹ * z‖ ^ 2)
  change (∑ U ∈ actualWindowCarrier B N H,
      blockInput B U * star (chi (U : ZMod q.val))) =
    ∑ i : ↑(actualWindowCarrier B N H),
      blockInput B i.val * star (chi (i.val : ZMod q.val))
  rw [Finset.sum_subtype]
  intro x
  rfl

theorem conductorPrimitiveSourceEnergy_le_explicit_cap
    (Q B N : ℕ) (H : ℝ) (q : PositiveLevel Q)
    (hB : 2 ≤ B) (hH : 0 ≤ H) :
    conductorPrimitiveSourceEnergy Q B N H q ≤
      explicitPrimitiveSourceCap B H q := by
  rw [conductorPrimitiveSourceEnergy_eq_raw]
  exact rawPrimitiveSourceEnergy_le_actual_budget
    q.val B N H hB hH

theorem explicitPrimitiveSourceCap_nonneg
    {Q B : ℕ} (H : ℝ) (q : PositiveLevel Q) (hH : 0 ≤ H) :
    0 ≤ explicitPrimitiveSourceCap B H q := by
  unfold explicitPrimitiveSourceCap
  positivity

/-- Fully explicit unconditional substitution.  This is a baseline envelope,
not a power-saving theorem: the conductor sum and every normalization cost
remain visible in the conclusion. -/
theorem nonprincipalPrimitiveCorrelation_block_energy_le_unconditional_envelope
    (Q B : ℕ) (H : ℝ) (w : ℕ → ℂ)
    (hB : 2 ≤ B) (hH : 0 ≤ H)
    (hwReal : ∀ n : ℕ, star (w n) = w n)
    (V : ℝ) (hV : 0 ≤ V)
    (hwBound : ∀ r q : PositiveLevel Q,
      r.val * q.val ≤ Q ∧ Nat.Coprime r.val q.val →
        ‖w (r.val * q.val)‖ ≤ V) :
    (∑ N ∈ blockCarrier B,
      ‖GoldbachCircleMethodHybridCenteredCorrelationEnergyV18501.nonprincipalPrimitiveCorrelation
        Q B N H w‖ ^ 2) ≤
      (Q : ℝ) *
        ∑ r : PositiveLevel Q,
          explicitPrimitiveSourceCap B H r * primitiveFamilyScale r *
            (((B + 1 : ℕ) : ℝ) *
                (∑ q : PositiveLevel Q,
                  ‖GoldbachCircleMethodActualCompanionCompleteDiagonalV18204.literalCoefficient
                    r q w‖ ^ 2 * (q.val.totient : ℝ)) +
              2 * (Q : ℝ) ^ 4 * V * V) := by
  exact nonprincipalPrimitiveCorrelation_block_energy_le_companion_envelope
    Q B H w (explicitPrimitiveSourceCap B H)
    (fun q => explicitPrimitiveSourceCap_nonneg H q hH)
    (fun q N _hN =>
      conductorPrimitiveSourceEnergy_le_explicit_cap Q B N H q hB hH)
    hwReal V hV hwBound

end GoldbachCircleMethodUnconditionalNonprincipalBlockEnvelopeV18529
