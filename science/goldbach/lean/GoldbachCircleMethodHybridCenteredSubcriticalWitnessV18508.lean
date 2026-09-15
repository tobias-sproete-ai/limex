import GoldbachCircleMethodNonprincipalPrimitiveConductorDecompositionV18507
import GoldbachCircleMethodCentralL2SubcriticalAbsorptionV18454

/-!
# Goldbach V1.8.508: hybrid-centered subcritical witness

Polynomial majorants for the repaired hybrid source and the actual partner
energy are composed with the pure-prime witness gate.  The theorem proves the
logical reduction under explicit bounds; it supplies none of those analytic
bounds and therefore leaves `proof_status = NO_PROOF` unchanged.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodHybridCenteredSubcriticalWitnessV18508

open GoldbachCircleMethodActiveResidualExactDecompositionV18251
open GoldbachCircleMethodCanonicalCentralAdjustedPositiveV18403
open GoldbachCircleMethodCanonicalCentralSourceTransferV18404
open GoldbachCircleMethodCentralAdjustedCorrectionL2MomentV18452
open GoldbachCircleMethodCentralL2SubcriticalAbsorptionV18454
open GoldbachCircleMethodHybridCenteredCentralMomentV18505
open GoldbachCircleMethodHybridCenteredWitnessTransferV18506
open GoldbachCircleMethodStructurallyAdmissibleActiveSlotV18258

/-- Source and partner exponents with sum below three satisfy the exact
squared correction reserve eventually. -/
theorem eventual_hybridCentered_energy_budget_of_subcritical_bounds
    (Cs Cp s p : ℝ) (hCs : 0 ≤ Cs) (hCp : 0 ≤ Cp)
    (hgap : s + p < 3) :
    ∃ m₀ : ℕ, ∀ (m : ℕ), m₀ ≤ m →
      ∀ (rho b : ℝ),
      ∀ (e : StructurallyAdmissibleActiveSlot
        ⌊(((8 * m : ℕ) : ℝ) ^ rho) ^ 2⌋₊),
      hybridCenteredSourceBudget (8 * m) rho b e.val ≤
          Cs * ((8 * m : ℕ) : ℝ) ^ s →
      centralAdjustedPartnerEnergy m rho b e ≤
          Cp * ((8 * m : ℕ) : ℝ) ^ p →
      (2 * m + 1 : ℕ) *
          (3 * hybridCenteredSourceBudget (8 * m) rho b e.val *
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
      0 ≤ hybridCenteredSourceBudget (8 * m) rho b e.val :=
    hybridCenteredSourceBudget_nonneg (8 * m) rho b e.val
  have hpartnerNonneg : 0 ≤ centralAdjustedPartnerEnergy m rho b e := by
    unfold centralAdjustedPartnerEnergy
      GoldbachCircleMethodAdjustedCorrectionL2CompositionV18451.adjustedCorrectionPartnerEnergy
    positivity
  have hthreeSource :
      3 * hybridCenteredSourceBudget (8 * m) rho b e.val ≤
        (3 * Cs) * ((8 * m : ℕ) : ℝ) ^ s := by
    calc
      3 * hybridCenteredSourceBudget (8 * m) rho b e.val ≤
          3 * (Cs * ((8 * m : ℕ) : ℝ) ^ s) :=
        mul_le_mul_of_nonneg_left hsource (by norm_num)
      _ = (3 * Cs) * ((8 * m : ℕ) : ℝ) ^ s := by ring
  have hthreeSourceNonneg :
      0 ≤ 3 * hybridCenteredSourceBudget (8 * m) rho b e.val := by
    positivity
  have hproductNonneg :
      0 ≤ (3 * hybridCenteredSourceBudget (8 * m) rho b e.val) *
        centralAdjustedPartnerEnergy m rho b e :=
    mul_nonneg hthreeSourceNonneg hpartnerNonneg
  calc
    (2 * m + 1 : ℕ) *
        (3 * hybridCenteredSourceBudget (8 * m) rho b e.val *
          centralAdjustedPartnerEnergy m rho b e) ≤
      ((8 * m : ℕ) : ℝ) *
        (3 * hybridCenteredSourceBudget (8 * m) rho b e.val *
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

/-- Full conditional composition through the repaired hybrid source budget.
The residual, source, and partner bounds remain premises. -/
theorem eventual_exists_goldbach_central_target_of_hybridCentered_subcritical_bounds
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
      hybridCenteredSourceBudget (8 * m) rho b e.val ≤
        Cs * ((8 * m : ℕ) : ℝ) ^ s →
      centralAdjustedPartnerEnergy m rho b e ≤
        Cp * ((8 * m : ℕ) : ℝ) ^ p →
      ∃ i ∈ Finset.range (2 * m + 1),
        GoldbachPurePrimeAdequacyV15.GoldbachAt (centralTargetNat m i) := by
  obtain ⟨mEnergy, hEnergy⟩ :=
    eventual_hybridCentered_energy_budget_of_subcritical_bounds
      Cs Cp s p hCs hCp hgap
  obtain ⟨mWitness, hWitness⟩ :=
    eventual_exists_goldbach_central_target_of_hybridCentered_budget
  refine ⟨max mEnergy mWitness, ?_⟩
  intro K hKinst m hm rho b hR2 e hK hrho hrhoUpper hScale hb hbUpper hR
    hResidual hSource hPartner
  have hmEnergy : mEnergy ≤ m := (le_max_left mEnergy mWitness).trans hm
  have hmWitness : mWitness ≤ m := (le_max_right mEnergy mWitness).trans hm
  have hFactored := hEnergy m hmEnergy rho b e hSource hPartner
  exact hWitness m hmWitness rho b hR2 e hK hrho hrhoUpper hScale hb hbUpper hR
    hResidual hFactored

end GoldbachCircleMethodHybridCenteredSubcriticalWitnessV18508
