import GoldbachCircleMethodPrincipalCoefficientAtomV18487
import GoldbachCircleMethodCentralL2SubcriticalAbsorptionV18454

/-!
# Goldbach V1.8.488: support-separated subcritical witness

This module proves the scalar absorption theorem for the sparse three-channel
source budget and composes it with the pure-prime witness transfer.  It leaves
the analytic polynomial bounds and active residual estimate as explicit
premises.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodSupportSeparatedSubcriticalWitnessV18488

open GoldbachCircleMethodActiveResidualExactDecompositionV18251
open GoldbachCircleMethodAdjustedCorrectionL2CompositionV18451
open GoldbachCircleMethodCanonicalCentralAdjustedPositiveV18403
open GoldbachCircleMethodCanonicalCentralSourceTransferV18404
open GoldbachCircleMethodCentralAdjustedCorrectionL2MomentV18452
open GoldbachCircleMethodCentralL2SubcriticalAbsorptionV18454
open GoldbachCircleMethodStructurallyAdmissibleActiveSlotV18258
open GoldbachCircleMethodSupportSeparatedSourceBudgetV18484
open GoldbachCircleMethodSupportSeparatedWitnessTransferV18486

/-- Polynomial majorants with exponent sum below three satisfy the exact
support-separated squared reserve eventually. -/
theorem eventual_supportSeparated_energy_budget_of_subcritical_bounds
    (Cs Cp s p : ℝ) (hCs : 0 ≤ Cs) (hCp : 0 ≤ Cp)
    (hgap : s + p < 3) :
    ∃ m₀ : ℕ, ∀ (m : ℕ), m₀ ≤ m →
      ∀ (rho b : ℝ),
      ∀ (e : StructurallyAdmissibleActiveSlot
        ⌊(((8 * m : ℕ) : ℝ) ^ rho) ^ 2⌋₊),
      supportSeparatedSourceBudget (8 * m) rho b e.val ≤
          Cs * ((8 * m : ℕ) : ℝ) ^ s →
      centralAdjustedPartnerEnergy m rho b e ≤
          Cp * ((8 * m : ℕ) : ℝ) ^ p →
      (2 * m + 1 : ℕ) *
          (3 * supportSeparatedSourceBudget (8 * m) rho b e.val *
            centralAdjustedPartnerEnergy m rho b e) <
        (((8 * m : ℕ) : ℝ) ^ 2 / 2048) ^ 2 := by
  obtain ⟨m₀, hscalar⟩ :=
    subcritical_energy_powers_fit_squared_quadratic_reserve
      (3 * Cs) Cp s p (by positivity) hCp hgap
  refine ⟨max m₀ 1, ?_⟩
  intro m hm rho b e hsource hpartner
  have hm₀ : m₀ ≤ m := (le_max_left m₀ 1).trans hm
  have hmOne : 1 ≤ m := (le_max_right m₀ 1).trans hm
  have hcard : ((2 * m + 1 : ℕ) : ℝ) ≤ ((8 * m : ℕ) : ℝ) := by
    exact_mod_cast (show 2 * m + 1 ≤ 8 * m by omega)
  have hsourceNonneg :
      0 ≤ supportSeparatedSourceBudget (8 * m) rho b e.val :=
    supportSeparatedSourceBudget_nonneg (8 * m) rho b e.val
  have hpartnerNonneg : 0 ≤ centralAdjustedPartnerEnergy m rho b e := by
    unfold centralAdjustedPartnerEnergy adjustedCorrectionPartnerEnergy
    positivity
  have hthreeSource :
      3 * supportSeparatedSourceBudget (8 * m) rho b e.val ≤
        (3 * Cs) * ((8 * m : ℕ) : ℝ) ^ s := by
    calc
      3 * supportSeparatedSourceBudget (8 * m) rho b e.val ≤
          3 * (Cs * ((8 * m : ℕ) : ℝ) ^ s) :=
        mul_le_mul_of_nonneg_left hsource (by norm_num)
      _ = (3 * Cs) * ((8 * m : ℕ) : ℝ) ^ s := by ring
  have hthreeSourceNonneg :
      0 ≤ 3 * supportSeparatedSourceBudget (8 * m) rho b e.val := by
    positivity
  have hproductNonneg :
      0 ≤ (3 * supportSeparatedSourceBudget (8 * m) rho b e.val) *
        centralAdjustedPartnerEnergy m rho b e :=
    mul_nonneg hthreeSourceNonneg hpartnerNonneg
  calc
    (2 * m + 1 : ℕ) *
        (3 * supportSeparatedSourceBudget (8 * m) rho b e.val *
          centralAdjustedPartnerEnergy m rho b e) ≤
      ((8 * m : ℕ) : ℝ) *
        (3 * supportSeparatedSourceBudget (8 * m) rho b e.val *
          centralAdjustedPartnerEnergy m rho b e) :=
      mul_le_mul_of_nonneg_right hcard hproductNonneg
    _ ≤ ((8 * m : ℕ) : ℝ) *
        (((3 * Cs) * ((8 * m : ℕ) : ℝ) ^ s) *
          (Cp * ((8 * m : ℕ) : ℝ) ^ p)) := by
      gcongr
    _ = ((8 * m : ℕ) : ℝ) *
          ((3 * Cs) * ((8 * m : ℕ) : ℝ) ^ s) *
          (Cp * ((8 * m : ℕ) : ℝ) ^ p) := by ring
    _ < (((8 * m : ℕ) : ℝ) ^ 2 / 2048) ^ 2 :=
      hscalar m hm₀

/-- Full conditional composition through the support-separated source budget.
The theorem proves the reduction, not the analytic majorants. -/
theorem eventual_exists_goldbach_central_target_of_supportSeparated_subcritical_bounds
    (Cs Cp s p : ℝ) (hCs : 0 ≤ Cs) (hCp : 0 ≤ Cp)
    (hgap : s + p < 3) :
    ∃ m₀ : ℕ, ∀ {K : ℕ} [NeZero K],
      ∀ (m : ℕ), m₀ ≤ m →
      ∀ (rho b : ℝ),
      ∀ (hR2 : 2 ≤ ((8 * m : ℕ) : ℝ) ^ rho),
      ∀ (e : StructurallyAdmissibleActiveSlot
        ⌊(((8 * m : ℕ) : ℝ) ^ rho) ^ 2⌋₊),
      (∀ q : GoldbachCircleMethodBoundedConductorReindexV18117.PositiveLevel
        ⌊(((8 * m : ℕ) : ℝ) ^ rho) ^ 2⌋₊, q.val ∣ K) →
      0 < rho → rho ≤ (1 : ℝ) / 10000 →
      GoldbachCircleMethodResidualScaleAdmissionV18196.blockThreshold rho ≤ 8 * m →
      0 ≤ b → b ≤ 1 →
      1 < ((8 * m : ℕ) : ℝ) ^ rho →
      |centralActiveResidualTargetSum m rho hR2 b e| <
        ((8 * m : ℕ) : ℝ) ^ 2 / 256 →
      supportSeparatedSourceBudget (8 * m) rho b e.val ≤
        Cs * ((8 * m : ℕ) : ℝ) ^ s →
      centralAdjustedPartnerEnergy m rho b e ≤
        Cp * ((8 * m : ℕ) : ℝ) ^ p →
      ∃ i ∈ Finset.range (2 * m + 1),
        GoldbachPurePrimeAdequacyV15.GoldbachAt (centralTargetNat m i) := by
  obtain ⟨mEnergy, hEnergy⟩ :=
    eventual_supportSeparated_energy_budget_of_subcritical_bounds
      Cs Cp s p hCs hCp hgap
  obtain ⟨mWitness, hWitness⟩ :=
    eventual_exists_goldbach_central_target_of_supportSeparated_budget
  refine ⟨max mEnergy mWitness, ?_⟩
  intro K hKinst m hm rho b hR2 e hK hrho hrhoUpper hScale hb hbUpper hR
    hResidual hSource hPartner
  have hmEnergy : mEnergy ≤ m := (le_max_left mEnergy mWitness).trans hm
  have hmWitness : mWitness ≤ m := (le_max_right mEnergy mWitness).trans hm
  have hFactored := hEnergy m hmEnergy rho b e hSource hPartner
  exact hWitness m hmWitness rho b hR2 e hK hrho hrhoUpper hScale hb hbUpper hR
    hResidual hFactored

end GoldbachCircleMethodSupportSeparatedSubcriticalWitnessV18488
