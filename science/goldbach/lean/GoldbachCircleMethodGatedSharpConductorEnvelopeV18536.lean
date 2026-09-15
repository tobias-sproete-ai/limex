import GoldbachCircleMethodNonprincipalConductorOneGateV18535

/-!
# Goldbach V1.8.536: gated sharp conductor envelope

The exact conductor-one exclusion from V1.8.535 is propagated through the
central block.  The sharp source cap remains conductor-dependent; no uniform
replacement is made.  Thus the statement preserves both the genuine
nonprincipal support and the local source normalization.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodGatedSharpConductorEnvelopeV18536

open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodLogCutoffPresieveBindingV18120
open GoldbachCircleMethodNonprincipalAlignedBlockEnergyV18528
open GoldbachCircleMethodNonprincipalConductorAlignedCorrelationV18527
open GoldbachCircleMethodNonprincipalConductorIntervalEnergyV18520
open GoldbachCircleMethodNonprincipalConductorOneGateV18535
open GoldbachCircleMethodSharpNonprincipalBlockEnvelopeV18530

/-- The primitive-family scale with the principal conductor removed. -/
noncomputable def nonprincipalPrimitiveFamilyScale
    {Q : ℕ} (r : PositiveLevel Q) : ℝ :=
  if r.val = 1 then 0 else primitiveFamilyScale r

theorem nonprincipalPrimitiveFamilyScale_nonneg
    {Q : ℕ} (r : PositiveLevel Q) :
    0 ≤ nonprincipalPrimitiveFamilyScale r := by
  by_cases hrOne : r.val = 1
  · simp [nonprincipalPrimitiveFamilyScale, hrOne]
  · simp only [nonprincipalPrimitiveFamilyScale, if_neg hrOne]
    exact primitiveFamilyScale_nonneg r

/-- Summing the pointwise gated estimate retains conductor alignment. -/
theorem nonprincipalPrimitiveCorrelation_block_energy_le_gated_aligned
    (Q B : ℕ) (H : ℝ) (w : ℕ → ℂ) :
    (∑ N ∈ blockCarrier B,
      ‖GoldbachCircleMethodHybridCenteredCorrelationEnergyV18501.nonprincipalPrimitiveCorrelation
        Q B N H w‖ ^ 2) ≤
      (Q : ℝ) *
        ∑ r : PositiveLevel Q,
          ∑ N ∈ blockCarrier B,
            nonprincipalConductorCoefficientEnergy N w r *
              conductorPrimitiveSourceEnergy Q B N H r := by
  calc
    _ ≤ ∑ N ∈ blockCarrier B,
        (Q : ℝ) *
          ∑ r : PositiveLevel Q,
            nonprincipalConductorCoefficientEnergy N w r *
              conductorPrimitiveSourceEnergy Q B N H r := by
      exact Finset.sum_le_sum (fun N _hN =>
        nonprincipalPrimitiveCorrelation_sq_le_gated_conductor_aligned
          Q B N H w)
    _ = _ := by
      rw [← Finset.mul_sum]
      congr 1
      rw [Finset.sum_comm]

/-- Conductor-local source caps are inserted without losing the exact
conductor-one gate. -/
theorem nonprincipalPrimitiveCorrelation_block_energy_le_gated_source_caps
    (Q B : ℕ) (H : ℝ) (w : ℕ → ℂ)
    (S : PositiveLevel Q → ℝ)
    (hSource : ∀ (r : PositiveLevel Q) (N : ℕ), N ∈ blockCarrier B →
      conductorPrimitiveSourceEnergy Q B N H r ≤ S r) :
    (∑ N ∈ blockCarrier B,
      ‖GoldbachCircleMethodHybridCenteredCorrelationEnergyV18501.nonprincipalPrimitiveCorrelation
        Q B N H w‖ ^ 2) ≤
      (Q : ℝ) *
        ∑ r : PositiveLevel Q,
          S r * ∑ N ∈ blockCarrier B,
            nonprincipalConductorCoefficientEnergy N w r := by
  apply (nonprincipalPrimitiveCorrelation_block_energy_le_gated_aligned
    Q B H w).trans
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg Q)
  apply Finset.sum_le_sum
  intro r _hr
  calc
    (∑ N ∈ blockCarrier B,
      nonprincipalConductorCoefficientEnergy N w r *
        conductorPrimitiveSourceEnergy Q B N H r) ≤
        ∑ N ∈ blockCarrier B,
          nonprincipalConductorCoefficientEnergy N w r * S r := by
      exact Finset.sum_le_sum (fun N hN =>
        mul_le_mul_of_nonneg_left (hSource r N hN)
          (nonprincipalConductorCoefficientEnergy_nonneg N w r))
    _ = S r * ∑ N ∈ blockCarrier B,
          nonprincipalConductorCoefficientEnergy N w r := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro N _hN
      ring

/-- The incomplete-companion coefficient estimate with the same
conductor-one gate as the correlation. -/
theorem gatedConductorCoefficient_block_energy_le
    {Q : ℕ} (r : PositiveLevel Q) (B : ℕ) (w : ℕ → ℂ)
    (hwReal : ∀ n : ℕ, star (w n) = w n)
    (V : ℝ) (hV : 0 ≤ V)
    (hwBound : ∀ q : PositiveLevel Q,
      r.val * q.val ≤ Q ∧ Nat.Coprime r.val q.val →
        ‖w (r.val * q.val)‖ ≤ V) :
    (∑ N ∈ blockCarrier B,
      nonprincipalConductorCoefficientEnergy N w r) ≤
      nonprincipalPrimitiveFamilyScale r *
        (((B + 1 : ℕ) : ℝ) *
            (∑ q : PositiveLevel Q,
              ‖GoldbachCircleMethodActualCompanionCompleteDiagonalV18204.literalCoefficient
                r q w‖ ^ 2 * (q.val.totient : ℝ)) +
          2 * (Q : ℝ) ^ 4 * V * V) := by
  by_cases hrOne : r.val = 1
  · simp [nonprincipalConductorCoefficientEnergy,
      nonprincipalPrimitiveFamilyScale, hrOne]
  · simp only [nonprincipalConductorCoefficientEnergy,
      nonprincipalPrimitiveFamilyScale, if_neg hrOne]
    unfold conductorCoefficientEnergy
    exact primitive_windowCoefficient_block_energy_le
      r B w hwReal V hV hwBound

/-- Final sharp block envelope at this gate.  The source cap is not
uniformized and the conductor-one contribution is exactly absent. -/
theorem nonprincipalPrimitiveCorrelation_block_energy_le_gated_sharp_envelope
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
          sharpPrimitiveSourceCap B H r *
            nonprincipalPrimitiveFamilyScale r *
              (((B + 1 : ℕ) : ℝ) *
                  (∑ q : PositiveLevel Q,
                    ‖GoldbachCircleMethodActualCompanionCompleteDiagonalV18204.literalCoefficient
                      r q w‖ ^ 2 * (q.val.totient : ℝ)) +
                2 * (Q : ℝ) ^ 4 * V * V) := by
  apply (nonprincipalPrimitiveCorrelation_block_energy_le_gated_source_caps
    Q B H w (sharpPrimitiveSourceCap B H)
    (fun r N _hN =>
      conductorPrimitiveSourceEnergy_le_sharp_cap Q B N H r hB hH)).trans
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg Q)
  apply Finset.sum_le_sum
  intro r _hr
  calc
    sharpPrimitiveSourceCap B H r *
        (∑ N ∈ blockCarrier B,
          nonprincipalConductorCoefficientEnergy N w r) ≤
      sharpPrimitiveSourceCap B H r *
        (nonprincipalPrimitiveFamilyScale r *
          (((B + 1 : ℕ) : ℝ) *
              (∑ q : PositiveLevel Q,
                ‖GoldbachCircleMethodActualCompanionCompleteDiagonalV18204.literalCoefficient
                  r q w‖ ^ 2 * (q.val.totient : ℝ)) +
            2 * (Q : ℝ) ^ 4 * V * V)) :=
      mul_le_mul_of_nonneg_left
        (gatedConductorCoefficient_block_energy_le
          r B w hwReal V hV (hwBound r))
        (sharpPrimitiveSourceCap_nonneg (B := B) H r hH)
    _ = _ := by ring

end GoldbachCircleMethodGatedSharpConductorEnvelopeV18536
