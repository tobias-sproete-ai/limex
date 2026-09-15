import GoldbachCircleMethodCoupledConductorEndpointSplitV18534

/-!
# Goldbach V1.8.535: exact conductor-one gate

The conductor-one atom of the nonprincipal correlation is definitionally zero.
This module carries that fact into the local coefficient-energy factor before
the outer conductor Cauchy--Schwarz step.  It therefore removes an artificial
principal contribution from the aligned envelope without asserting any new
analytic decay estimate.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodNonprincipalConductorOneGateV18535

open GoldbachCircleMethodActiveExceptionalCenteringV18129
open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodNonprincipalConductorAlignedCorrelationV18527
open GoldbachCircleMethodRemovedConvolutionNormV18123

/-- The coefficient energy used by the nonprincipal channel.  At conductor
one it is exactly zero, matching the definition of the correlation itself. -/
noncomputable def nonprincipalConductorCoefficientEnergy
    {Q : ℕ} (N : ℕ) (w : ℕ → ℂ) (q : PositiveLevel Q) : ℝ :=
  if q.val = 1 then 0 else conductorCoefficientEnergy N w q

theorem nonprincipalConductorCoefficientEnergy_nonneg
    {Q : ℕ} (N : ℕ) (w : ℕ → ℂ) (q : PositiveLevel Q) :
    0 ≤ nonprincipalConductorCoefficientEnergy N w q := by
  by_cases hqOne : q.val = 1
  · simp [nonprincipalConductorCoefficientEnergy, hqOne]
  · simp only [nonprincipalConductorCoefficientEnergy, if_neg hqOne]
    unfold conductorCoefficientEnergy
    exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)

/-- Local Cauchy--Schwarz with the conductor-one coefficient factor removed
literally rather than bounded by a positive surrogate. -/
theorem nonprincipalConductorCorrelation_sq_le_gated_local_product
    (Q B N : ℕ) (H : ℝ) (w : ℕ → ℂ) (q : PositiveLevel Q) :
    ‖nonprincipalConductorCorrelation Q B N H w q‖ ^ 2 ≤
      nonprincipalConductorCoefficientEnergy N w q *
        conductorPrimitiveSourceEnergy Q B N H q := by
  by_cases hqOne : q.val = 1
  · simp [nonprincipalConductorCorrelation,
      nonprincipalConductorCoefficientEnergy, hqOne]
  · simpa [nonprincipalConductorCoefficientEnergy, hqOne] using
      nonprincipalConductorCorrelation_sq_le_local_product Q B N H w q

/-- The aligned conductor envelope with exact nonprincipal gating at
conductor one.  The outer factor is retained; eliminating it would require a
genuine cross-conductor orthogonality input not claimed here. -/
theorem nonprincipalPrimitiveCorrelation_sq_le_gated_conductor_aligned
    (Q B N : ℕ) (H : ℝ) (w : ℕ → ℂ) :
    ‖GoldbachCircleMethodHybridCenteredCorrelationEnergyV18501.nonprincipalPrimitiveCorrelation
        Q B N H w‖ ^ 2 ≤
      (Q : ℝ) *
        ∑ q : PositiveLevel Q,
          nonprincipalConductorCoefficientEnergy N w q *
            conductorPrimitiveSourceEnergy Q B N H q := by
  rw [nonprincipalPrimitiveCorrelation_eq_sum_conductors]
  have htriangle :
      ‖∑ q : PositiveLevel Q,
          nonprincipalConductorCorrelation Q B N H w q‖ ≤
        ∑ q : PositiveLevel Q,
          ‖nonprincipalConductorCorrelation Q B N H w q‖ :=
    norm_sum_le _ _
  have hsq := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr htriangle
  apply hsq.trans
  have hcs := sq_sum_le_card_mul_sum_sq
    (s := Finset.univ)
    (f := fun q : PositiveLevel Q =>
      ‖nonprincipalConductorCorrelation Q B N H w q‖)
  apply hcs.trans
  rw [Finset.card_univ, positive_level_card]
  gcongr with q
  exact nonprincipalConductorCorrelation_sq_le_gated_local_product Q B N H w q

end GoldbachCircleMethodNonprincipalConductorOneGateV18535
