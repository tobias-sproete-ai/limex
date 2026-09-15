import GoldbachCircleMethodUnconditionalNonprincipalBlockEnvelopeV18529
import GoldbachCircleMethodActualWindowCharacterEnergySharpV18477
import GoldbachCircleMethodPrimitiveBaseSpanEnvelopeV18478

/-!
# Goldbach V1.8.530: sharp nonprincipal block envelope

The unconditional V1.8.529 source cap is sharpened from whole-block residue
multiplicity to the actual centered-window span `2 * floor(H)`.  The resulting
bound is inserted into the conductor-aligned correlation from V1.8.528.  The
coarser predecessor remains unchanged as an append-only baseline.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodSharpNonprincipalBlockEnvelopeV18530

open GoldbachCircleMethodActualWindowCharacterEnergySharpV18477
open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodLogCutoffPresieveBindingV18120
open GoldbachCircleMethodNonprincipalAlignedBlockEnergyV18528
open GoldbachCircleMethodNonprincipalConductorAlignedCorrelationV18527
open GoldbachCircleMethodNonprincipalConductorIntervalEnergyV18520
open GoldbachCircleMethodPrimitiveBaseSpanEnvelopeV18478
open GoldbachCircleMethodUnconditionalNonprincipalBlockEnvelopeV18529

/-- Sharp conductor-local cap using only the actual window span. -/
noncomputable def sharpPrimitiveSourceCap
    {Q : ℕ} (B : ℕ) (H : ℝ) (q : PositiveLevel Q) : ℝ :=
  ‖(2 * (H : ℂ))⁻¹‖ ^ 2 *
    ((q.val.totient : ℝ) *
      (((2 * ⌊H⌋₊) / q.val + 1 : ℕ) : ℝ) *
      ((2 * H + 1) * (Real.log (B : ℝ)) ^ 2))

/-- A conductor-independent version of the sharp cap. -/
noncomputable def uniformSharpPrimitiveSourceCap
    (Q B : ℕ) (H : ℝ) : ℝ :=
  ‖(2 * (H : ℂ))⁻¹‖ ^ 2 *
    (((2 * ⌊H⌋₊ + Q : ℕ) : ℝ) *
      ((2 * H + 1) * (Real.log (B : ℝ)) ^ 2))

theorem conductorPrimitiveSourceEnergy_le_sharp_cap
    (Q B N : ℕ) (H : ℝ) (q : PositiveLevel Q)
    (hB : 2 ≤ B) (hH : 0 ≤ H) :
    conductorPrimitiveSourceEnergy Q B N H q ≤
      sharpPrimitiveSourceCap B H q := by
  rw [conductorPrimitiveSourceEnergy_eq_raw]
  exact rawPrimitiveSourceEnergy_le_span_budget
    q.val B N H hB hH

theorem sharpPrimitiveSourceCap_nonneg
    {Q B : ℕ} (H : ℝ) (q : PositiveLevel Q) (hH : 0 ≤ H) :
    0 ≤ sharpPrimitiveSourceCap B H q := by
  unfold sharpPrimitiveSourceCap
  positivity

theorem sharpPrimitiveSourceCap_le_uniform
    {Q B : ℕ} (H : ℝ) (q : PositiveLevel Q) (hH : 0 ≤ H) :
    sharpPrimitiveSourceCap B H q ≤
      uniformSharpPrimitiveSourceCap Q B H := by
  exact sharp_level_term_le_uniform Q B H hH q

theorem uniformSharpPrimitiveSourceCap_nonneg
    (Q B : ℕ) (H : ℝ) (hH : 0 ≤ H) :
    0 ≤ uniformSharpPrimitiveSourceCap Q B H := by
  unfold uniformSharpPrimitiveSourceCap
  positivity

/-- Conductor-aligned nonprincipal block envelope with the sharp actual-window
source cap. -/
theorem nonprincipalPrimitiveCorrelation_block_energy_le_sharp_envelope
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
          sharpPrimitiveSourceCap B H r * primitiveFamilyScale r *
            (((B + 1 : ℕ) : ℝ) *
                (∑ q : PositiveLevel Q,
                  ‖GoldbachCircleMethodActualCompanionCompleteDiagonalV18204.literalCoefficient
                    r q w‖ ^ 2 * (q.val.totient : ℝ)) +
              2 * (Q : ℝ) ^ 4 * V * V) := by
  exact nonprincipalPrimitiveCorrelation_block_energy_le_companion_envelope
    Q B H w (sharpPrimitiveSourceCap B H)
    (fun q => sharpPrimitiveSourceCap_nonneg H q hH)
    (fun q N _hN =>
      conductorPrimitiveSourceEnergy_le_sharp_cap Q B N H q hB hH)
    hwReal V hV hwBound

/-- Uniformized sharp envelope.  The common source factor remains exact and
can now be simplified under the canonical inequalities `1 ≤ H` and `Q ≤ H`.
-/
theorem nonprincipalPrimitiveCorrelation_block_energy_le_uniform_sharp_envelope
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
      (Q : ℝ) * uniformSharpPrimitiveSourceCap Q B H *
        ∑ r : PositiveLevel Q,
          primitiveFamilyScale r *
            (((B + 1 : ℕ) : ℝ) *
                (∑ q : PositiveLevel Q,
                  ‖GoldbachCircleMethodActualCompanionCompleteDiagonalV18204.literalCoefficient
                    r q w‖ ^ 2 * (q.val.totient : ℝ)) +
              2 * (Q : ℝ) ^ 4 * V * V) := by
  apply (nonprincipalPrimitiveCorrelation_block_energy_le_sharp_envelope
    Q B H w hB hH hwReal V hV hwBound).trans
  let E : PositiveLevel Q → ℝ := fun r =>
    primitiveFamilyScale r *
      (((B + 1 : ℕ) : ℝ) *
          (∑ q : PositiveLevel Q,
            ‖GoldbachCircleMethodActualCompanionCompleteDiagonalV18204.literalCoefficient
              r q w‖ ^ 2 * (q.val.totient : ℝ)) +
        2 * (Q : ℝ) ^ 4 * V * V)
  have hinner :
      (∑ r : PositiveLevel Q, sharpPrimitiveSourceCap B H r * E r) ≤
        uniformSharpPrimitiveSourceCap Q B H *
          ∑ r : PositiveLevel Q, E r := by
    calc
      _ ≤ ∑ r : PositiveLevel Q,
          uniformSharpPrimitiveSourceCap Q B H * E r := by
        apply Finset.sum_le_sum
        intro r _hr
        exact mul_le_mul_of_nonneg_right
          (sharpPrimitiveSourceCap_le_uniform H r hH) (by
            unfold E
            exact mul_nonneg (primitiveFamilyScale_nonneg r) (by positivity))
      _ = _ := by rw [Finset.mul_sum]
  have hfinal :
      (Q : ℝ) *
          (∑ r : PositiveLevel Q, sharpPrimitiveSourceCap B H r * E r) ≤
        (Q : ℝ) * uniformSharpPrimitiveSourceCap Q B H *
          ∑ r : PositiveLevel Q, E r := by
    calc
    _ ≤ (Q : ℝ) *
        (uniformSharpPrimitiveSourceCap Q B H *
          ∑ r : PositiveLevel Q, E r) :=
      mul_le_mul_of_nonneg_left hinner (Nat.cast_nonneg Q)
    _ = _ := by ring
  simpa only [E, mul_assoc] using hfinal

end GoldbachCircleMethodSharpNonprincipalBlockEnvelopeV18530
