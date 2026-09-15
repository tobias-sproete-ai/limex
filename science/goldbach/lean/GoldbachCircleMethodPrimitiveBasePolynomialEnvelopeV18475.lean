import GoldbachCircleMethodPrimitiveBaseSlotEnergyV18474

/-!
# Goldbach V1.8.475: primitive base polynomial envelope

The exact finite conductor sum is reduced to a closed polynomial envelope.
Only `Nat.totient_le`, finite interval cardinality, and monotonicity of the
nonnegative factors are used.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodPrimitiveBasePolynomialEnvelopeV18475

open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodPrimitiveBaseSlotEnergyV18474

theorem positiveLevel_card (Q : ℕ) :
    Fintype.card (PositiveLevel Q) = Q := by
  simp [PositiveLevel]

noncomputable def primitiveBasePolynomialEnvelope
    (Q B : ℕ) (H : ℝ) : ℝ :=
  ‖(2 * (H : ℂ))⁻¹‖ ^ 2 * (Q : ℝ) ^ 2 * (B + 2 : ℝ) *
    ((2 * H + 1) * (Real.log (B : ℝ)) ^ 2)

theorem level_term_le_uniform
    (Q B : ℕ) (H : ℝ) (hH : 0 ≤ H) (q : PositiveLevel Q) :
    ‖(2 * (H : ℂ))⁻¹‖ ^ 2 *
        ((q.val.totient : ℝ) *
          (((B + 1) / q.val + 1 : ℕ) : ℝ) *
            ((2 * H + 1) * (Real.log (B : ℝ)) ^ 2)) ≤
      ‖(2 * (H : ℂ))⁻¹‖ ^ 2 *
        ((Q : ℝ) * (B + 2 : ℝ) *
          ((2 * H + 1) * (Real.log (B : ℝ)) ^ 2)) := by
  have hqQ : q.val ≤ Q := (Finset.mem_Icc.mp q.property).2
  have hphiNat : q.val.totient ≤ Q := (Nat.totient_le q.val).trans hqQ
  have hdivNat : (B + 1) / q.val + 1 ≤ B + 2 := by
    have hself : (B + 1) / q.val ≤ B + 1 := Nat.div_le_self _ _
    omega
  have hphi : (q.val.totient : ℝ) ≤ (Q : ℝ) := by
    exact_mod_cast hphiNat
  have hdiv : (((B + 1) / q.val + 1 : ℕ) : ℝ) ≤ (B + 2 : ℝ) := by
    exact_mod_cast hdivNat
  have hwindow : 0 ≤ (2 * H + 1) * (Real.log (B : ℝ)) ^ 2 := by
    positivity
  gcongr

/-- The literal unadjusted source energy has a finite polynomial envelope. -/
theorem primitiveBaseSourceEnergy_le_polynomial
    (Q B N : ℕ) (H : ℝ) (hB : 2 ≤ B) (hH : 0 ≤ H) :
    primitiveBaseSourceEnergy Q B N H ≤
      primitiveBasePolynomialEnvelope Q B H := by
  let C : ℝ := ‖(2 * (H : ℂ))⁻¹‖ ^ 2 *
    ((Q : ℝ) * (B + 2 : ℝ) *
      ((2 * H + 1) * (Real.log (B : ℝ)) ^ 2))
  calc
    primitiveBaseSourceEnergy Q B N H ≤
        ∑ q : PositiveLevel Q,
          ‖(2 * (H : ℂ))⁻¹‖ ^ 2 *
            ((q.val.totient : ℝ) *
              (((B + 1) / q.val + 1 : ℕ) : ℝ) *
                ((2 * H + 1) * (Real.log (B : ℝ)) ^ 2)) :=
      primitiveBaseSourceEnergy_le_level_sum Q B N H hB hH
    _ ≤ ∑ _q : PositiveLevel Q, C := by
      apply Finset.sum_le_sum
      intro q _hq
      exact level_term_le_uniform Q B H hH q
    _ = (Q : ℝ) * C := by
      simp
    _ = primitiveBasePolynomialEnvelope Q B H := by
      unfold C primitiveBasePolynomialEnvelope
      ring

end GoldbachCircleMethodPrimitiveBasePolynomialEnvelopeV18475
