import GoldbachCircleMethodCentralL2SubcriticalAbsorptionV18454

/-!
# Goldbach V1.8.455: subcritical L2 energy-to-witness closure

This module composes the exact finite L2 correction interface with the scalar
subcritical absorption theorem and the already verified central pure-prime
witness transfer.

The result is conditional on actual polynomial energy majorants with exponent
sum strictly below three, as well as the unchanged active-residual budget.
The critical exponent identity records why exponent sum exactly three supplies
no asymptotic gain by itself.  No such analytic bounds are asserted here.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodCentralL2SubcriticalWitnessV18455

open GoldbachCircleMethodAdjustedCorrectionL2CompositionV18451
open GoldbachCircleMethodActiveResidualExactDecompositionV18251
open GoldbachCircleMethodCentralAdjustedCorrectionL2MomentV18452
open GoldbachCircleMethodCentralL2CorrectionWitnessTransferV18453
open GoldbachCircleMethodCentralL2SubcriticalAbsorptionV18454
open GoldbachCircleMethodCanonicalCentralAdjustedPositiveV18403
open GoldbachCircleMethodCanonicalCentralSourceTransferV18404
open GoldbachCircleMethodStructurallyAdmissibleActiveSlotV18258

/-- At the critical exponent split `1 + 2 = 3`, the entire scale dependence
cancels against the squared quadratic reserve.  Therefore only the numerical
constant, not large-block asymptotics, can close that boundary case. -/
theorem critical_exponent_product_identity (x Cs Cp : ℝ) :
    x * (Cs * x) * (Cp * x ^ 2) =
      (x ^ 2 / 2048) ^ 2 * ((2048 : ℝ) ^ 2 * Cs * Cp) := by
  ring

/-- Full conditional composition: subcritical polynomial bounds for the two
literal finite energies imply an eventual genuine pure-prime witness in every
canonical central block, provided the independent active-residual budget also
holds.  The theorem proves the reduction, not either analytic premise. -/
theorem eventual_exists_goldbach_central_target_of_subcritical_energy_bounds
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
      adjustedSlotEnergyProductSourceSum (8 * m) rho b e.val ≤
        Cs * ((8 * m : ℕ) : ℝ) ^ s →
      centralAdjustedPartnerEnergy m rho b e ≤
        Cp * ((8 * m : ℕ) : ℝ) ^ p →
      ∃ i ∈ Finset.range (2 * m + 1),
        GoldbachPurePrimeAdequacyV15.GoldbachAt
          (GoldbachCircleMethodCanonicalCentralAdjustedPositiveV18403.centralTargetNat m i) := by
  obtain ⟨mEnergy, hEnergy⟩ :=
    eventual_central_factored_energy_budget_of_subcritical_bounds
      Cs Cp s p hCs hCp hgap
  obtain ⟨mWitness, hWitness⟩ :=
    eventual_exists_goldbach_central_target_of_l2_centered_budget
  refine ⟨max mEnergy mWitness, ?_⟩
  intro K hKinst m hm rho b hR2 e hK hrho hrhoUpper hScale hb hbUpper hR
    hResidual hSource hPartner
  have hmEnergy : mEnergy ≤ m := (le_max_left mEnergy mWitness).trans hm
  have hmWitness : mWitness ≤ m := (le_max_right mEnergy mWitness).trans hm
  have hFactored := hEnergy m hmEnergy rho b e hSource hPartner
  exact hWitness m hmWitness rho b hR2 e hK hrho hrhoUpper hScale hb hbUpper hR
    hResidual hFactored

end GoldbachCircleMethodCentralL2SubcriticalWitnessV18455
