import GoldbachCircleMethodExactCrossConductorResidualV18538

/-!
# Goldbach V1.8.539: sharp split plus exact cross residual

The conductor-local source cap and literal coefficient majorant are composed
with the exact cross-conductor residual from V1.8.538.  The diagonal channel
therefore carries no outer conductor-cardinality loss.  The only remaining
inter-conductor obligation is the explicitly signed residual.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodCrossResidualSharpSplitV18539

open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodExactCrossConductorResidualV18538
open GoldbachCircleMethodGatedSharpConductorEnvelopeV18536
open GoldbachCircleMethodGatedSharpEndpointSplitV18537
open GoldbachCircleMethodLiteralCoefficientDiagonalMajorantV18533
open GoldbachCircleMethodNonprincipalConductorIntervalEnergyV18520
open GoldbachCircleMethodSharpNonprincipalBlockEnvelopeV18530

/-- Sharp conductor-local source normalization and coefficient block energy,
with the exact cross-conductor residual retained and no outer `Q`. -/
theorem nonprincipal_block_energy_le_gated_sharp_add_cross_residual
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
      (∑ r : PositiveLevel Q,
        sharpPrimitiveSourceCap B H r *
          nonprincipalPrimitiveFamilyScale r *
            ((((B + 1 : ℕ) : ℝ) *
                (∑ q : PositiveLevel Q,
                  ‖GoldbachCircleMethodActualCompanionCompleteDiagonalV18204.literalCoefficient
                    r q w‖ ^ 2 * (q.val.totient : ℝ))) +
              2 * (Q : ℝ) ^ 4 * V * V)) +
        blockCrossConductorResidual Q B H w := by
  apply (nonprincipal_block_energy_le_source_caps_add_cross_residual
    Q B H w (sharpPrimitiveSourceCap B H)
    (fun r N _hN =>
      conductorPrimitiveSourceEnergy_le_sharp_cap Q B N H r hB hH)).trans
  apply add_le_add_left
  apply Finset.sum_le_sum
  intro r _hr
  calc
    sharpPrimitiveSourceCap B H r *
        (∑ N ∈ GoldbachCircleMethodLogCutoffPresieveBindingV18120.blockCarrier B,
          GoldbachCircleMethodNonprincipalConductorOneGateV18535.nonprincipalConductorCoefficientEnergy
            N w r) ≤
      sharpPrimitiveSourceCap B H r *
        (nonprincipalPrimitiveFamilyScale r *
          ((((B + 1 : ℕ) : ℝ) *
              (∑ q : PositiveLevel Q,
                ‖GoldbachCircleMethodActualCompanionCompleteDiagonalV18204.literalCoefficient
                  r q w‖ ^ 2 * (q.val.totient : ℝ))) +
            2 * (Q : ℝ) ^ 4 * V * V)) :=
      mul_le_mul_of_nonneg_left
        (gatedConductorCoefficient_block_energy_le
          r B w hwReal V hV (hwBound r))
        (sharpPrimitiveSourceCap_nonneg (B := B) H r hH)
    _ = _ := by ring

/-- Final exact split at the present gate.  The diagonal and endpoint
arithmetic objects are explicit; all cross-conductor interaction is confined
to `blockCrossConductorResidual`. -/
theorem nonprincipal_block_energy_le_sharp_split_add_cross_residual
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
      (((((B + 1 : ℕ) : ℝ) * V ^ 2) *
          gatedSharpConductorDiagonalKernel Q B H) +
        ((2 * (Q : ℝ) ^ 4 * V * V) *
          gatedSharpPrimitiveFamilyMass Q B H)) +
        blockCrossConductorResidual Q B H w := by
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
    _ ≤ (∑ r : PositiveLevel Q,
        sharpPrimitiveSourceCap B H r *
          nonprincipalPrimitiveFamilyScale r *
            ((((B + 1 : ℕ) : ℝ) *
                (∑ q : PositiveLevel Q,
                  ‖GoldbachCircleMethodActualCompanionCompleteDiagonalV18204.literalCoefficient
                    r q w‖ ^ 2 * (q.val.totient : ℝ))) +
              2 * (Q : ℝ) ^ 4 * V * V)) +
        blockCrossConductorResidual Q B H w :=
      nonprincipal_block_energy_le_gated_sharp_add_cross_residual
        Q B H w hB hH hwReal V hV hwBound
    _ ≤ (∑ r : PositiveLevel Q,
        sharpPrimitiveSourceCap B H r *
          nonprincipalPrimitiveFamilyScale r *
            ((((B + 1 : ℕ) : ℝ) *
                (∑ q : PositiveLevel Q,
                  literalCoefficientDiagonalMajorant r q V)) +
              2 * (Q : ℝ) ^ 4 * V * V)) +
        blockCrossConductorResidual Q B H w :=
      add_le_add_left hinner _
    _ = _ := by
      rw [gated_sharp_envelope_exact_split]

end GoldbachCircleMethodCrossResidualSharpSplitV18539
