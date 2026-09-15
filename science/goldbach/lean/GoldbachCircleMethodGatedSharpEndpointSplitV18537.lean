import GoldbachCircleMethodGatedSharpConductorEnvelopeV18536

/-!
# Goldbach V1.8.537: gated sharp diagonal/endpoint split

The exact nonprincipal conductor gate and the conductor-dependent sharp source
cap are retained while the coefficient envelope is split into its diagonal
and endpoint components.  This exposes two arithmetic targets without
replacing either by an asymptotic hypothesis.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodGatedSharpEndpointSplitV18537

open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodCoupledConductorEndpointSplitV18534
open GoldbachCircleMethodGatedSharpConductorEnvelopeV18536
open GoldbachCircleMethodLiteralCoefficientDiagonalMajorantV18533
open GoldbachCircleMethodNonprincipalConductorIntervalEnergyV18520
open GoldbachCircleMethodSharpNonprincipalBlockEnvelopeV18530

/-- Diagonal arithmetic kernel with both the exact nonprincipal gate and the
sharp conductor-local source normalization. -/
noncomputable def gatedSharpConductorDiagonalKernel
    (Q B : ℕ) (H : ℝ) : ℝ :=
  ∑ r : PositiveLevel Q,
    (sharpPrimitiveSourceCap B H r * nonprincipalPrimitiveFamilyScale r) *
      ∑ q : PositiveLevel Q, coupledReciprocalTotientKernel r q

/-- Endpoint normalization with the same exact support and source weight. -/
noncomputable def gatedSharpPrimitiveFamilyMass
    (Q B : ℕ) (H : ℝ) : ℝ :=
  ∑ r : PositiveLevel Q,
    sharpPrimitiveSourceCap B H r * nonprincipalPrimitiveFamilyScale r

theorem gatedSharpConductorDiagonalKernel_nonneg
    (Q B : ℕ) (H : ℝ) (hH : 0 ≤ H) :
    0 ≤ gatedSharpConductorDiagonalKernel Q B H := by
  unfold gatedSharpConductorDiagonalKernel
  apply Finset.sum_nonneg
  intro r _hr
  apply mul_nonneg
  · exact mul_nonneg
      (sharpPrimitiveSourceCap_nonneg (B := B) H r hH)
      (nonprincipalPrimitiveFamilyScale_nonneg r)
  · apply Finset.sum_nonneg
    intro q _hq
    unfold coupledReciprocalTotientKernel
    split_ifs
    · positivity
    · norm_num

theorem gatedSharpPrimitiveFamilyMass_nonneg
    (Q B : ℕ) (H : ℝ) (hH : 0 ≤ H) :
    0 ≤ gatedSharpPrimitiveFamilyMass Q B H := by
  unfold gatedSharpPrimitiveFamilyMass
  exact Finset.sum_nonneg (fun r _hr =>
    mul_nonneg (sharpPrimitiveSourceCap_nonneg (B := B) H r hH)
      (nonprincipalPrimitiveFamilyScale_nonneg r))

/-- Exact algebraic split of the sharp gated majorant. -/
theorem gated_sharp_envelope_exact_split
    (Q B : ℕ) (H V : ℝ) :
    (∑ r : PositiveLevel Q,
      sharpPrimitiveSourceCap B H r *
        nonprincipalPrimitiveFamilyScale r *
          ((((B + 1 : ℕ) : ℝ) *
              (∑ q : PositiveLevel Q,
                literalCoefficientDiagonalMajorant r q V)) +
            2 * (Q : ℝ) ^ 4 * V * V)) =
      ((((B + 1 : ℕ) : ℝ) * V ^ 2) *
          gatedSharpConductorDiagonalKernel Q B H) +
        ((2 * (Q : ℝ) ^ 4 * V * V) *
          gatedSharpPrimitiveFamilyMass Q B H) := by
  unfold gatedSharpConductorDiagonalKernel gatedSharpPrimitiveFamilyMass
  simp_rw [literalCoefficientDiagonalMajorant_sum_eq]
  calc
    _ = ∑ r : PositiveLevel Q,
        (((((B + 1 : ℕ) : ℝ) * V ^ 2) *
            ((sharpPrimitiveSourceCap B H r *
                nonprincipalPrimitiveFamilyScale r) *
              ∑ q : PositiveLevel Q, coupledReciprocalTotientKernel r q)) +
          ((2 * (Q : ℝ) ^ 4 * V * V) *
            (sharpPrimitiveSourceCap B H r *
              nonprincipalPrimitiveFamilyScale r))) := by
      apply Finset.sum_congr rfl
      intro r _hr
      ring
    _ = (∑ r : PositiveLevel Q,
          (((B + 1 : ℕ) : ℝ) * V ^ 2) *
            ((sharpPrimitiveSourceCap B H r *
                nonprincipalPrimitiveFamilyScale r) *
              ∑ q : PositiveLevel Q, coupledReciprocalTotientKernel r q)) +
        ∑ r : PositiveLevel Q,
          (2 * (Q : ℝ) ^ 4 * V * V) *
            (sharpPrimitiveSourceCap B H r *
              nonprincipalPrimitiveFamilyScale r) := by
      rw [Finset.sum_add_distrib]
    _ = _ := by
      rw [← Finset.mul_sum, ← Finset.mul_sum]

/-- The current sharp nonprincipal block envelope with its diagonal and
endpoint arithmetic costs exposed separately. -/
theorem nonprincipalPrimitiveCorrelation_block_energy_le_gated_sharp_split
    (Q B : ℕ) (H : ℝ) (w : ℕ → ℂ)
    (hB : 2 ≤ B) (hH : 0 ≤ H)
    (hwReal : ∀ n : ℕ, star (w n) = w n)
    (V : ℝ) (hV : 0 ≤ V)
    (hwBound : ∀ r q : PositiveLevel Q,
      r.val * q.val ≤ Q ∧ Nat.Coprime r.val q.val →
        ‖w (r.val * q.val)‖ ≤ V) :
    (∑ N ∈ GoldbachCircleMethodLogCutoffPresieveBindingV18120.blockCarrier B,
      ‖GoldbachCircleMethodHybridCenteredCorrelationEnergyV18501.nonprincipalPrimitiveCorrelation
        Q B N H w‖ ^ 2) ≤
      (Q : ℝ) *
        (((((B + 1 : ℕ) : ℝ) * V ^ 2) *
            gatedSharpConductorDiagonalKernel Q B H) +
          ((2 * (Q : ℝ) ^ 4 * V * V) *
            gatedSharpPrimitiveFamilyMass Q B H)) := by
  have hbase :=
    nonprincipalPrimitiveCorrelation_block_energy_le_gated_sharp_envelope
      Q B H w hB hH hwReal V hV hwBound
  have hdiag : ∀ r : PositiveLevel Q,
      (∑ q : PositiveLevel Q,
        ‖GoldbachCircleMethodActualCompanionCompleteDiagonalV18204.literalCoefficient
          r q w‖ ^ 2 * (q.val.totient : ℝ)) ≤
        ∑ q : PositiveLevel Q,
          literalCoefficientDiagonalMajorant r q V := by
    intro r
    exact literalCoefficient_diagonal_sum_le_majorant_sum
      r w V (fun q => hwBound r q)
  have hinner :
      (∑ r : PositiveLevel Q,
        sharpPrimitiveSourceCap B H r *
          nonprincipalPrimitiveFamilyScale r *
            ((((B + 1 : ℕ) : ℝ) *
                (∑ q : PositiveLevel Q,
                  ‖GoldbachCircleMethodActualCompanionCompleteDiagonalV18204.literalCoefficient
                    r q w‖ ^ 2 * (q.val.totient : ℝ))) +
              2 * (Q : ℝ) ^ 4 * V * V)) ≤
        ∑ r : PositiveLevel Q,
          sharpPrimitiveSourceCap B H r *
            nonprincipalPrimitiveFamilyScale r *
              ((((B + 1 : ℕ) : ℝ) *
                  (∑ q : PositiveLevel Q,
                    literalCoefficientDiagonalMajorant r q V)) +
                2 * (Q : ℝ) ^ 4 * V * V) := by
    apply Finset.sum_le_sum
    intro r _hr
    apply mul_le_mul_of_nonneg_left
    · exact add_le_add
        (mul_le_mul_of_nonneg_left (hdiag r) (by positivity)) (le_refl _)
    · exact mul_nonneg
        (sharpPrimitiveSourceCap_nonneg (B := B) H r hH)
        (nonprincipalPrimitiveFamilyScale_nonneg r)
  calc
    _ ≤ (Q : ℝ) *
        (∑ r : PositiveLevel Q,
          sharpPrimitiveSourceCap B H r *
            nonprincipalPrimitiveFamilyScale r *
              ((((B + 1 : ℕ) : ℝ) *
                  (∑ q : PositiveLevel Q,
                    ‖GoldbachCircleMethodActualCompanionCompleteDiagonalV18204.literalCoefficient
                      r q w‖ ^ 2 * (q.val.totient : ℝ))) +
                2 * (Q : ℝ) ^ 4 * V * V)) := hbase
    _ ≤ (Q : ℝ) *
        (∑ r : PositiveLevel Q,
          sharpPrimitiveSourceCap B H r *
            nonprincipalPrimitiveFamilyScale r *
              ((((B + 1 : ℕ) : ℝ) *
                  (∑ q : PositiveLevel Q,
                    literalCoefficientDiagonalMajorant r q V)) +
                2 * (Q : ℝ) ^ 4 * V * V)) :=
      mul_le_mul_of_nonneg_left hinner (Nat.cast_nonneg Q)
    _ = _ := by
      rw [gated_sharp_envelope_exact_split]

end GoldbachCircleMethodGatedSharpEndpointSplitV18537
