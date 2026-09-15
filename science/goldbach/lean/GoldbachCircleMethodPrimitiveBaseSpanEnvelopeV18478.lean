import GoldbachCircleMethodActualWindowCharacterEnergySharpV18477

/-!
# Goldbach V1.8.478: primitive base span envelope

The sharp fixed-conductor window estimate is summed over all positive levels.
The conductor arithmetic is retained as `Q*(2*floor(H)+Q)` rather than being
inflated back to the dyadic block length.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodPrimitiveBaseSpanEnvelopeV18478

open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodActualPrimitiveSourceNormalizationV18470
open GoldbachCircleMethodActualWindowCharacterEnergySharpV18477
open GoldbachCircleMethodPrimitiveBaseSlotEnergyV18474

noncomputable def primitiveBaseSpanEnvelope
    (Q B : ℕ) (H : ℝ) : ℝ :=
  ‖(2 * (H : ℂ))⁻¹‖ ^ 2 *
    ((Q : ℝ) * ((2 * ⌊H⌋₊ + Q : ℕ) : ℝ)) *
      ((2 * H + 1) * (Real.log (B : ℝ)) ^ 2)

theorem totient_mul_span_quotient_le
    (Q D q : ℕ) (hqQ : q ≤ Q) :
    q.totient * (D / q + 1) ≤ D + Q := by
  calc
    q.totient * (D / q + 1) ≤ q * (D / q + 1) :=
      Nat.mul_le_mul_right (D / q + 1) (Nat.totient_le q)
    _ = (D / q) * q + q := by ring
    _ ≤ D + q := Nat.add_le_add_right (Nat.div_mul_le_self D q) q
    _ ≤ D + Q := Nat.add_le_add_left hqQ D

theorem sharp_level_term_le_uniform
    (Q B : ℕ) (H : ℝ) (hH : 0 ≤ H) (q : PositiveLevel Q) :
    ‖(2 * (H : ℂ))⁻¹‖ ^ 2 *
        ((q.val.totient : ℝ) *
          (((2 * ⌊H⌋₊) / q.val + 1 : ℕ) : ℝ) *
            ((2 * H + 1) * (Real.log (B : ℝ)) ^ 2)) ≤
      ‖(2 * (H : ℂ))⁻¹‖ ^ 2 *
        (((2 * ⌊H⌋₊ + Q : ℕ) : ℝ) *
          ((2 * H + 1) * (Real.log (B : ℝ)) ^ 2)) := by
  have hqQ : q.val ≤ Q := (Finset.mem_Icc.mp q.property).2
  have hnat := totient_mul_span_quotient_le Q (2 * ⌊H⌋₊) q.val hqQ
  have hreal : (q.val.totient : ℝ) *
      (((2 * ⌊H⌋₊) / q.val + 1 : ℕ) : ℝ) ≤
      ((2 * ⌊H⌋₊ + Q : ℕ) : ℝ) := by
    exact_mod_cast hnat
  have hwindow : 0 ≤ (2 * H + 1) * (Real.log (B : ℝ)) ^ 2 := by
    positivity
  gcongr

/-- Closed sharp span envelope for the literal unadjusted source energy. -/
theorem primitiveBaseSourceEnergy_le_span_envelope
    (Q B N : ℕ) (H : ℝ) (hB : 2 ≤ B) (hH : 0 ≤ H) :
    primitiveBaseSourceEnergy Q B N H ≤
      primitiveBaseSpanEnvelope Q B H := by
  rw [primitiveBaseSourceEnergy_eq_sum_raw]
  let C : ℝ := ‖(2 * (H : ℂ))⁻¹‖ ^ 2 *
    (((2 * ⌊H⌋₊ + Q : ℕ) : ℝ) *
      ((2 * H + 1) * (Real.log (B : ℝ)) ^ 2))
  calc
    (∑ q : PositiveLevel Q, rawPrimitiveSourceEnergy q.val B N H) ≤
        ∑ q : PositiveLevel Q,
          ‖(2 * (H : ℂ))⁻¹‖ ^ 2 *
            ((q.val.totient : ℝ) *
              (((2 * ⌊H⌋₊) / q.val + 1 : ℕ) : ℝ) *
                ((2 * H + 1) * (Real.log (B : ℝ)) ^ 2)) := by
      apply Finset.sum_le_sum
      intro q _hq
      exact rawPrimitiveSourceEnergy_le_span_budget q.val B N H hB hH
    _ ≤ ∑ _q : PositiveLevel Q, C := by
      apply Finset.sum_le_sum
      intro q _hq
      exact sharp_level_term_le_uniform Q B H hH q
    _ = (Q : ℝ) * C := by simp
    _ = primitiveBaseSpanEnvelope Q B H := by
      unfold C primitiveBaseSpanEnvelope
      ring

end GoldbachCircleMethodPrimitiveBaseSpanEnvelopeV18478
