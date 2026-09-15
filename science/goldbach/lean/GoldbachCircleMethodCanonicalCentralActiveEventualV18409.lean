import GoldbachCircleMethodCanonicalCentralActiveScaleAbsorptionV18408

/-!
# Goldbach V1.8.409: eventual central active-residual absorption

V1.8.406's source-matched active moment estimate and V1.8.408's elementary
scale absorption are composed at the existing explicit block threshold.  For
every admitted Vaughan estimate and every fixed positive `rho <= 1/10000`, the
entire central active-residual aggregate is eventually below `B^2 / 256`.

The Vaughan estimate remains a named external analytic premise.  This theorem
does not close the centered-correction channel and is not a Goldbach theorem.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodCanonicalCentralActiveEventualV18409

open GoldbachCircleMethodCanonicalCentralActiveResidualV18406
open GoldbachCircleMethodCanonicalCentralActiveScaleAbsorptionV18408
open GoldbachCircleMethodCanonicalCentralSourceTransferV18404
open GoldbachCircleMethodLogCutoffPresieveBindingV18120
open GoldbachCircleMethodRealApproximationMinorAdapterV1873
open GoldbachCircleMethodResidualScaleAdmissionV18196
open GoldbachCircleMethodStructurallyAdmissibleActiveSlotV18258

/-- Once the external Vaughan estimate is supplied, the full central active
residual aggregate is eventually absorbed.  No separate numerical power-budget
hypothesis remains in the conclusion. -/
theorem eventual_central_active_residual_target_sum_abs_lt_one_over_256
    (C rho : ℝ) (hC : 0 ≤ C) (hV : RealVaughanEstimate C)
    (hrho : 0 < rho) (hrhoUpper : rho ≤ (1 : ℝ) / 10000) :
    ∃ Crho : ℝ, 0 ≤ Crho ∧ ∃ m₀ : ℕ, ∀ (m : ℕ), m₀ ≤ m →
      ∀ (hR2 : 2 ≤ ((8 * m : ℕ) : ℝ) ^ rho),
      ∀ b : ℝ, 0 ≤ b → b ≤ 1 →
      ∀ e : StructurallyAdmissibleActiveSlot
        ⌊(((8 * m : ℕ) : ℝ) ^ rho) ^ 2⌋₊,
      |centralActiveResidualTargetSum m rho hR2 b e| <
        ((8 * m : ℕ) : ℝ) ^ 2 / 256 := by
  obtain ⟨Crho, hCrho, hmoment⟩ :=
    central_active_residual_target_sum_sq_power_bound C rho hC hV hrho
  obtain ⟨m₁, hbudget⟩ := eventual_central_active_power_budget rho Crho hrho hCrho
  let m₀ := max m₁ (blockThreshold rho)
  refine ⟨Crho, hCrho, m₀, ?_⟩
  intro m hm hR2 b hb hb1 e
  have hm₁ : m₁ ≤ m := (le_max_left _ _).trans hm
  have hthreshold_m : blockThreshold rho ≤ m := (le_max_right _ _).trans hm
  have hthreshold_B : blockThreshold rho ≤ 8 * m := by omega
  obtain ⟨hB6, _hR2canonical, hlower, hupper⟩ :=
    actual_scale_admission rho hrho hrhoUpper (8 * m) hthreshold_B
  have hsq := hmoment m hB6 hR2 hlower hupper b hb hb1 e
  exact central_active_residual_target_sum_abs_lt_one_over_256
    m rho Crho b hR2 e hsq (hbudget m hm₁)

end GoldbachCircleMethodCanonicalCentralActiveEventualV18409
