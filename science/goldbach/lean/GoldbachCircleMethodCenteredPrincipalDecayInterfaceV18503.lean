import GoldbachCircleMethodHybridPrincipalAtomsV18502
import GoldbachCircleMethodExactPrincipalBoundaryCostV18126

/-!
# Goldbach V1.8.503: centered-principal decay interface

The repaired principal channel is connected to one literal short-interval
`Lambda - 1` discrepancy.  The analytic decay is an explicit parameter, not
an axiom or a consequence claimed from the existing Vaughan interface.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodCenteredPrincipalDecayInterfaceV18503

open GoldbachCircleMethodActiveExceptionalCenteringV18129
open GoldbachCircleMethodCenteredPrincipalDecayInterfaceV18503
open GoldbachCircleMethodExactPrincipalBoundaryCostV18126
open GoldbachCircleMethodFiniteCompanionBindingV18118
open GoldbachCircleMethodFiniteIntervalRemainderReserveV18229
open GoldbachCircleMethodFiniteWindowConvolutionV18119
open GoldbachCircleMethodHybridCenteredCorrelationEnergyV18501
open GoldbachCircleMethodHybridPrincipalAtomsV18502
open GoldbachCircleMethodLogCutoffPresieveBindingV18120
open GoldbachCircleMethodPrincipalWindowBoundaryV18121
open GoldbachCircleMethodCanonicalBumpPrincipalFloorV18220

/-- Canonical centered-window scale used in the active central construction. -/
noncomputable def centeredPrincipalScale (B : ℕ) (rho : ℝ) : ℝ :=
  (B : ℝ) / ((B : ℝ) ^ rho) ^ 4

/-- The exact normalized local `Lambda - 1` discrepancy exposed by V1.8.502. -/
noncomputable def centeredPrincipalDiscrepancy
    (B N : ℕ) (rho : ℝ) : ℂ :=
  let H := centeredPrincipalScale B rho
  (2 * (H : ℂ))⁻¹ *
    ∑ U ∈ centeredWindow (blockCarrier B) N H,
      (blockInput B U - 1)

/-- Minimal analytic interface for the repaired principal channel.  This type
is intentionally uninhabited in this module. -/
def CenteredPrincipalDiscrepancyEstimate
    (C rho sigma : ℝ) : Prop :=
  ∀ (B N : ℕ), 3 ≤ B → N ∈ blockCarrier B →
    ‖centeredPrincipalDiscrepancy B N rho‖ ≤
      C * (B : ℝ) ^ (-sigma)

/-- The source energy is exactly the square of the declared discrepancy; no
analytic estimate is used. -/
theorem centeredPrincipalSourceEnergy_eq_discrepancy_sq
    (Q B N : ℕ) (rho : ℝ) (hQ : 1 ≤ Q) :
    centeredPrincipalSourceEnergy Q B N (centeredPrincipalScale B rho) =
      ‖centeredPrincipalDiscrepancy B N rho‖ ^ 2 := by
  rw [centeredPrincipalSourceEnergy_eq_centered_discrepancy_sq
    Q B N (centeredPrincipalScale B rho) hQ]
  rfl

/-- A declared discrepancy estimate bounds the exact source atom. -/
theorem centeredPrincipalSourceEnergy_le_of_estimate
    (C rho sigma : ℝ) (hC : 0 ≤ C)
    (hestimate : CenteredPrincipalDiscrepancyEstimate C rho sigma)
    (Q B N : ℕ) (hQ : 1 ≤ Q) (hB : 3 ≤ B)
    (hN : N ∈ blockCarrier B) :
    centeredPrincipalSourceEnergy Q B N (centeredPrincipalScale B rho) ≤
      (C * (B : ℝ) ^ (-sigma)) ^ 2 := by
  rw [centeredPrincipalSourceEnergy_eq_discrepancy_sq Q B N rho hQ]
  have hbound := hestimate B N hB hN
  have hright : 0 ≤ C * (B : ℝ) ^ (-sigma) := by positivity
  exact (sq_le_sq₀ (norm_nonneg _) hright).mpr hbound

/-- For a norm-one coefficient weight, the unique principal coefficient atom
costs at most `Q^2`. -/
theorem centeredPrincipalCoefficientEnergy_le_cutoff_sq
    (Q N : ℕ) (hQ : 1 ≤ Q) (w : ℕ → ℂ)
    (hw : ∀ n, ‖w n‖ ≤ 1) :
    centeredPrincipalCoefficientEnergy Q N w ≤ (Q : ℝ) ^ 2 := by
  rw [centeredPrincipalCoefficientEnergy_eq_finiteCompanion_sq Q N hQ w]
  have hnorm : ‖finiteCompanion (oneLevel hQ) N w‖ ≤ (Q : ℝ) := by
    simpa only [one_mul] using
      finite_companion_norm_le_linear Q N (oneLevel hQ) w 1 zero_le_one hw
  exact (sq_le_sq₀ (norm_nonneg _) (Nat.cast_nonneg Q)).mpr hnorm

/-- Exact conditional decay of the repaired principal correlation.  The
coefficient price is explicit and the short-interval estimate remains visible
in the signature. -/
theorem centeredPrincipalCorrelation_sq_le_of_discrepancy_estimate
    (C rho sigma : ℝ) (hC : 0 ≤ C)
    (hestimate : CenteredPrincipalDiscrepancyEstimate C rho sigma)
    (Q B N : ℕ) (hQ : 1 ≤ Q) (hB : 3 ≤ B)
    (hN : N ∈ blockCarrier B) :
    ‖centeredPrincipalCorrelation Q B N
        (centeredPrincipalScale B rho)
        (logWeight ((B : ℝ) ^ rho) canonicalLogBump)‖ ^ 2 ≤
      (Q : ℝ) ^ 2 * (C * (B : ℝ) ^ (-sigma)) ^ 2 := by
  calc
    _ ≤ centeredPrincipalCoefficientEnergy Q N
          (logWeight ((B : ℝ) ^ rho) canonicalLogBump) *
        centeredPrincipalSourceEnergy Q B N
          (centeredPrincipalScale B rho) :=
      centeredPrincipalCorrelation_sq_le Q B N
        (centeredPrincipalScale B rho)
        (logWeight ((B : ℝ) ^ rho) canonicalLogBump)
    _ ≤ (Q : ℝ) ^ 2 * (C * (B : ℝ) ^ (-sigma)) ^ 2 := by
      apply mul_le_mul
      · exact centeredPrincipalCoefficientEnergy_le_cutoff_sq Q N hQ
          (logWeight ((B : ℝ) ^ rho) canonicalLogBump)
          (norm_logWeight_canonical_le_one ((B : ℝ) ^ rho))
      · exact centeredPrincipalSourceEnergy_le_of_estimate C rho sigma hC
          hestimate Q B N hQ hB hN
      · unfold centeredPrincipalSourceEnergy
        positivity
      · positivity

end GoldbachCircleMethodCenteredPrincipalDecayInterfaceV18503
