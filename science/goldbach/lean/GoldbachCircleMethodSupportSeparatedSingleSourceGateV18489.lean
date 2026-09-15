import GoldbachCircleMethodSupportSeparatedSubcriticalWitnessV18488
import GoldbachCircleMethodCentralPartnerPolynomialEnvelopeV18458

/-!
# Goldbach V1.8.489: support-separated single-source gate

The actual partner-energy chain is substituted into the support-separated
witness theorem.  The new correction branch is reduced to one explicit
source-energy exponent gate.  The independent active-residual estimate remains
the pre-existing second analytic premise.

This theorem is conditional and does not prove Goldbach.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodSupportSeparatedSingleSourceGateV18489

open GoldbachCircleMethodActiveResidualExactDecompositionV18251
open GoldbachCircleMethodCanonicalCentralAdjustedPositiveV18403
open GoldbachCircleMethodCanonicalCentralSourceTransferV18404
open GoldbachCircleMethodCentralAdjustedCorrectionL2MomentV18452
open GoldbachCircleMethodCentralPartnerActualAmplitudeV18457
open GoldbachCircleMethodCentralPartnerPolynomialEnvelopeV18458
open GoldbachCircleMethodStructurallyAdmissibleActiveSlotV18258
open GoldbachCircleMethodSupportSeparatedSourceBudgetV18484
open GoldbachCircleMethodSupportSeparatedSubcriticalWitnessV18488

/-- Once the actual partner branch is discharged, one explicit
support-separated source exponent gate remains.  Together with the unchanged
active-residual budget it yields a genuine prime-pair witness eventually. -/
theorem eventual_exists_goldbach_central_target_of_supportSeparated_source_gate :
    ∃ CB : ℝ, 0 ≤ CB ∧ ∀ eps : ℝ, 0 < eps →
      ∃ Kdiv : ℝ, 1 ≤ Kdiv ∧ ∀ eta : ℝ, 0 < eta →
        ∀ (Cs s : ℝ), 0 ≤ Cs → s + 2 * (eps + eta) < 1 →
        ∃ m₀ : ℕ, ∀ {K : ℕ} [NeZero K],
          ∀ (m : ℕ), m₀ ≤ m →
          ∀ (rho b : ℝ),
          ∀ (hR2 : 2 ≤ ((8 * m : ℕ) : ℝ) ^ rho),
          ((8 * m : ℕ) : ℝ) ^ rho ≤ ((8 * m : ℕ) : ℝ) →
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
          ∃ i ∈ Finset.range (2 * m + 1),
            GoldbachPurePrimeAdequacyV15.GoldbachAt (centralTargetNat m i) := by
  obtain ⟨CB, hCB, hActualPartner⟩ := actual_central_partner_energy_bound
  refine ⟨CB, hCB, ?_⟩
  intro eps heps
  obtain ⟨Kdiv, hKdiv, hPartnerForBlock⟩ := hActualPartner eps heps
  refine ⟨Kdiv, hKdiv, ?_⟩
  intro eta heta Cs s hCs hSourceGap
  let Cp : ℝ := canonicalPartnerPolynomialConstant eta Kdiv CB
  let p : ℝ := 2 + 2 * (eps + eta)
  have hCp : 0 ≤ Cp := by
    dsimp [Cp]
    exact canonicalPartnerPolynomialConstant_nonneg eta Kdiv CB
  have hgap : s + p < 3 := by
    dsimp [p]
    linarith
  obtain ⟨mWitness, hWitness⟩ :=
    eventual_exists_goldbach_central_target_of_supportSeparated_subcritical_bounds
      Cs Cp s p hCs hCp hgap
  refine ⟨max mWitness 1, ?_⟩
  intro K hKinst m hm rho b hR2 hRB e hConductor hrho hrhoUpper hScale
    hb hbUpper hR hResidual hSource
  have hmWitness : mWitness ≤ m := (le_max_left mWitness 1).trans hm
  have hmOne : 1 ≤ m := (le_max_right mWitness 1).trans hm
  have hPartnerRaw := hPartnerForBlock m hmOne rho b hR2 hRB hb e
  have hPartnerPoly := central_partner_energy_le_polynomial
    m hmOne rho b eps eta Kdiv CB heta (by linarith) hCB e hPartnerRaw
  have hPartner : centralAdjustedPartnerEnergy m rho b e ≤
      Cp * ((8 * m : ℕ) : ℝ) ^ p := by
    simpa only [Cp, p] using hPartnerPoly
  exact hWitness m hmWitness rho b hR2 e hConductor hrho hrhoUpper hScale
    hb hbUpper hR hResidual hSource hPartner

end GoldbachCircleMethodSupportSeparatedSingleSourceGateV18489
