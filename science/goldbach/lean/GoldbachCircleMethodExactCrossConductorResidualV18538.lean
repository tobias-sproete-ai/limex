import GoldbachCircleMethodGatedSharpEndpointSplitV18537

/-!
# Goldbach V1.8.538: exact cross-conductor residual

The outer conductor Cauchy--Schwarz loss is not applied.  Instead, the exact
difference between the squared norm of the conductor sum and the sum of the
individual squared norms is retained as a signed residual.  This isolates the
precise cross-conductor analytic obligation and removes the artificial factor
`Q` from the diagonal part of the algebraic reduction.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodExactCrossConductorResidualV18538

open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodLogCutoffPresieveBindingV18120
open GoldbachCircleMethodNonprincipalConductorAlignedCorrelationV18527
open GoldbachCircleMethodNonprincipalConductorOneGateV18535

/-- Signed cross-conductor residual at one target.  No sign or smallness is
assumed. -/
noncomputable def crossConductorResidual
    (Q B N : ℕ) (H : ℝ) (w : ℕ → ℂ) : ℝ :=
  ‖GoldbachCircleMethodHybridCenteredCorrelationEnergyV18501.nonprincipalPrimitiveCorrelation
      Q B N H w‖ ^ 2 -
    ∑ r : PositiveLevel Q,
      ‖nonprincipalConductorCorrelation Q B N H w r‖ ^ 2

/-- Definitionally exact replacement for the outer conductor
Cauchy--Schwarz step. -/
theorem nonprincipal_energy_eq_conductor_diagonal_add_residual
    (Q B N : ℕ) (H : ℝ) (w : ℕ → ℂ) :
    ‖GoldbachCircleMethodHybridCenteredCorrelationEnergyV18501.nonprincipalPrimitiveCorrelation
        Q B N H w‖ ^ 2 =
      (∑ r : PositiveLevel Q,
        ‖nonprincipalConductorCorrelation Q B N H w r‖ ^ 2) +
        crossConductorResidual Q B N H w := by
  unfold crossConductorResidual
  ring

/-- Pointwise reduction with no cardinality loss.  All inter-conductor
interaction is retained in the signed residual. -/
theorem nonprincipal_energy_le_gated_local_products_add_residual
    (Q B N : ℕ) (H : ℝ) (w : ℕ → ℂ) :
    ‖GoldbachCircleMethodHybridCenteredCorrelationEnergyV18501.nonprincipalPrimitiveCorrelation
        Q B N H w‖ ^ 2 ≤
      (∑ r : PositiveLevel Q,
        nonprincipalConductorCoefficientEnergy N w r *
          conductorPrimitiveSourceEnergy Q B N H r) +
        crossConductorResidual Q B N H w := by
  rw [nonprincipal_energy_eq_conductor_diagonal_add_residual]
  apply add_le_add_left
  apply Finset.sum_le_sum
  intro r _hr
  exact nonprincipalConductorCorrelation_sq_le_gated_local_product
    Q B N H w r

/-- The exact residual accumulated on the actual central block. -/
noncomputable def blockCrossConductorResidual
    (Q B : ℕ) (H : ℝ) (w : ℕ → ℂ) : ℝ :=
  ∑ N ∈ blockCarrier B, crossConductorResidual Q B N H w

/-- Block reduction without an outer `Q`: the conductor diagonal is aligned
exactly, and the full cost of cross-conductor interaction is explicit. -/
theorem nonprincipal_block_energy_le_gated_products_add_cross_residual
    (Q B : ℕ) (H : ℝ) (w : ℕ → ℂ) :
    (∑ N ∈ blockCarrier B,
      ‖GoldbachCircleMethodHybridCenteredCorrelationEnergyV18501.nonprincipalPrimitiveCorrelation
        Q B N H w‖ ^ 2) ≤
      (∑ r : PositiveLevel Q,
        ∑ N ∈ blockCarrier B,
          nonprincipalConductorCoefficientEnergy N w r *
            conductorPrimitiveSourceEnergy Q B N H r) +
        blockCrossConductorResidual Q B H w := by
  calc
    _ ≤ ∑ N ∈ blockCarrier B,
        ((∑ r : PositiveLevel Q,
            nonprincipalConductorCoefficientEnergy N w r *
              conductorPrimitiveSourceEnergy Q B N H r) +
          crossConductorResidual Q B N H w) := by
      exact Finset.sum_le_sum (fun N _hN =>
        nonprincipal_energy_le_gated_local_products_add_residual
          Q B N H w)
    _ = _ := by
      unfold blockCrossConductorResidual
      rw [Finset.sum_add_distrib, Finset.sum_comm]

/-- Conductor-local source caps preserve the exact signed cross residual and
still incur no outer conductor-cardinality factor. -/
theorem nonprincipal_block_energy_le_source_caps_add_cross_residual
    (Q B : ℕ) (H : ℝ) (w : ℕ → ℂ)
    (S : PositiveLevel Q → ℝ)
    (hSource : ∀ (r : PositiveLevel Q) (N : ℕ), N ∈ blockCarrier B →
      conductorPrimitiveSourceEnergy Q B N H r ≤ S r) :
    (∑ N ∈ blockCarrier B,
      ‖GoldbachCircleMethodHybridCenteredCorrelationEnergyV18501.nonprincipalPrimitiveCorrelation
        Q B N H w‖ ^ 2) ≤
      (∑ r : PositiveLevel Q,
        S r * ∑ N ∈ blockCarrier B,
          nonprincipalConductorCoefficientEnergy N w r) +
        blockCrossConductorResidual Q B H w := by
  apply (nonprincipal_block_energy_le_gated_products_add_cross_residual
    Q B H w).trans
  apply add_le_add_left
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

end GoldbachCircleMethodExactCrossConductorResidualV18538
