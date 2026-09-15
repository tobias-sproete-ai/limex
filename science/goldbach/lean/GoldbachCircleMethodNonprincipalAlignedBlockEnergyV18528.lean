import GoldbachCircleMethodNonprincipalConductorAlignedCorrelationV18527
import GoldbachCircleMethodNonprincipalConductorIntervalEnergyV18520

/-!
# Goldbach V1.8.528: conductor-aligned block energy

The pointwise aligned conductor estimate from V1.8.527 is summed over the
actual central block.  A conductor-local source cap can then be paired with
the already kernel-checked incomplete-companion coefficient estimate from
V1.8.520.  The source caps remain explicit hypotheses; no large-sieve or
prime-distribution estimate is smuggled into this algebraic bridge.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodNonprincipalAlignedBlockEnergyV18528

open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodLogCutoffPresieveBindingV18120
open GoldbachCircleMethodNonprincipalConductorAlignedCorrelationV18527
open GoldbachCircleMethodNonprincipalConductorIntervalEnergyV18520

theorem conductorCoefficientEnergy_nonneg
    {Q : ℕ} (N : ℕ) (w : ℕ → ℂ) (q : PositiveLevel Q) :
    0 ≤ conductorCoefficientEnergy N w q := by
  unfold conductorCoefficientEnergy
  exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem conductorPrimitiveSourceEnergy_nonneg
    (Q B N : ℕ) (H : ℝ) (q : PositiveLevel Q) :
    0 ≤ conductorPrimitiveSourceEnergy Q B N H q := by
  unfold conductorPrimitiveSourceEnergy
  exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)

/-- The block sum preserves conductor alignment.  The only outer-family cost
at this stage is the literal conductor count `Q`. -/
theorem nonprincipalPrimitiveCorrelation_block_energy_le_aligned
    (Q B : ℕ) (H : ℝ) (w : ℕ → ℂ) :
    (∑ N ∈ blockCarrier B,
      ‖GoldbachCircleMethodHybridCenteredCorrelationEnergyV18501.nonprincipalPrimitiveCorrelation
        Q B N H w‖ ^ 2) ≤
      (Q : ℝ) *
        ∑ q : PositiveLevel Q,
          ∑ N ∈ blockCarrier B,
            conductorCoefficientEnergy N w q *
              conductorPrimitiveSourceEnergy Q B N H q := by
  calc
    _ ≤ ∑ N ∈ blockCarrier B,
        (Q : ℝ) *
          ∑ q : PositiveLevel Q,
            conductorCoefficientEnergy N w q *
              conductorPrimitiveSourceEnergy Q B N H q := by
      exact Finset.sum_le_sum (fun N _hN =>
        nonprincipalPrimitiveCorrelation_sq_le_conductor_aligned Q B N H w)
    _ = _ := by
      rw [← Finset.mul_sum]
      congr 1
      rw [Finset.sum_comm]

/-- If the source energy is capped separately at each conductor, only the
matching coefficient family is charged against that cap. -/
theorem nonprincipalPrimitiveCorrelation_block_energy_le_source_caps
    (Q B : ℕ) (H : ℝ) (w : ℕ → ℂ)
    (S : PositiveLevel Q → ℝ)
    (hSource : ∀ (q : PositiveLevel Q) (N : ℕ), N ∈ blockCarrier B →
      conductorPrimitiveSourceEnergy Q B N H q ≤ S q) :
    (∑ N ∈ blockCarrier B,
      ‖GoldbachCircleMethodHybridCenteredCorrelationEnergyV18501.nonprincipalPrimitiveCorrelation
        Q B N H w‖ ^ 2) ≤
      (Q : ℝ) *
        ∑ q : PositiveLevel Q,
          S q * ∑ N ∈ blockCarrier B,
            conductorCoefficientEnergy N w q := by
  apply (nonprincipalPrimitiveCorrelation_block_energy_le_aligned Q B H w).trans
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg Q)
  apply Finset.sum_le_sum
  intro q _hq
  calc
    (∑ N ∈ blockCarrier B,
      conductorCoefficientEnergy N w q *
        conductorPrimitiveSourceEnergy Q B N H q) ≤
        ∑ N ∈ blockCarrier B,
          conductorCoefficientEnergy N w q * S q := by
      exact Finset.sum_le_sum (fun N hN =>
        mul_le_mul_of_nonneg_left (hSource q N hN)
          (conductorCoefficientEnergy_nonneg N w q))
    _ = S q * ∑ N ∈ blockCarrier B,
          conductorCoefficientEnergy N w q := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro N _hN
      ring

/-- V1.8.520 is inserted without altering its signature.  The resulting
statement exposes the remaining conductor-local source-cap obligation and
retains the literal companion coefficients and `Q^4` boundary term. -/
theorem nonprincipalPrimitiveCorrelation_block_energy_le_companion_envelope
    (Q B : ℕ) (H : ℝ) (w : ℕ → ℂ)
    (S : PositiveLevel Q → ℝ)
    (hS : ∀ q : PositiveLevel Q, 0 ≤ S q)
    (hSource : ∀ (q : PositiveLevel Q) (N : ℕ), N ∈ blockCarrier B →
      conductorPrimitiveSourceEnergy Q B N H q ≤ S q)
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
          S r * primitiveFamilyScale r *
            (((B + 1 : ℕ) : ℝ) *
                (∑ q : PositiveLevel Q,
                  ‖GoldbachCircleMethodActualCompanionCompleteDiagonalV18204.literalCoefficient
                    r q w‖ ^ 2 * (q.val.totient : ℝ)) +
              2 * (Q : ℝ) ^ 4 * V * V) := by
  apply (nonprincipalPrimitiveCorrelation_block_energy_le_source_caps
    Q B H w S hSource).trans
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg Q)
  apply Finset.sum_le_sum
  intro r _hr
  have hcoeff :
      (∑ N ∈ blockCarrier B, conductorCoefficientEnergy N w r) ≤
        primitiveFamilyScale r *
          (((B + 1 : ℕ) : ℝ) *
              (∑ q : PositiveLevel Q,
                ‖GoldbachCircleMethodActualCompanionCompleteDiagonalV18204.literalCoefficient
                  r q w‖ ^ 2 * (q.val.totient : ℝ)) +
            2 * (Q : ℝ) ^ 4 * V * V) := by
    unfold conductorCoefficientEnergy
    exact primitive_windowCoefficient_block_energy_le
      r B w hwReal V hV (hwBound r)
  calc
    S r * ∑ N ∈ blockCarrier B, conductorCoefficientEnergy N w r ≤
        S r * (primitiveFamilyScale r *
          (((B + 1 : ℕ) : ℝ) *
              (∑ q : PositiveLevel Q,
                ‖GoldbachCircleMethodActualCompanionCompleteDiagonalV18204.literalCoefficient
                  r q w‖ ^ 2 * (q.val.totient : ℝ)) +
            2 * (Q : ℝ) ^ 4 * V * V)) :=
      mul_le_mul_of_nonneg_left hcoeff (hS r)
    _ = _ := by ring

end GoldbachCircleMethodNonprincipalAlignedBlockEnergyV18528
