import GoldbachCircleMethodCentralPartnerPolynomialEnvelopeV18458

/-!
# Goldbach V1.8.459: single adjusted-source energy gate

The actual central partner energy is now composed through its canonical bump,
divisor subpower bound, logarithm absorption and the central L2 witness
transfer.  All of those layers are discharged here.

The only new analytic correction premise left in this path is a polynomial
bound for `adjustedSlotEnergyProductSourceSum` with exponent
`s + 2*(eps+eta) < 1`.  The independent active-residual budget remains the
pre-existing second premise.  Consequently this is a conditional reduction
and the top-level proof status remains `NO_PROOF`.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodCentralSingleSourceEnergyGateV18459

open GoldbachCircleMethodAdjustedCorrectionL2CompositionV18451
open GoldbachCircleMethodCanonicalCentralAdjustedPositiveV18403
open GoldbachCircleMethodCanonicalCentralSourceTransferV18404
open GoldbachCircleMethodCentralAdjustedCorrectionL2MomentV18452
open GoldbachCircleMethodCentralL2SubcriticalWitnessV18455
open GoldbachCircleMethodCentralPartnerActualAmplitudeV18457
open GoldbachCircleMethodCentralPartnerPolynomialEnvelopeV18458
open GoldbachCircleMethodStructurallyAdmissibleActiveSlotV18258

/-- The fully actual partner branch leaves one explicit adjusted-source energy
exponent gate.  Closing that gate and the independent active residual produces
a genuine prime-pair witness in each sufficiently large central block. -/
theorem eventual_exists_goldbach_central_target_of_single_source_energy_gate :
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
          adjustedSlotEnergyProductSourceSum (8 * m) rho b e.val ≤
            Cs * ((8 * m : ℕ) : ℝ) ^ s →
          ∃ i ∈ Finset.range (2 * m + 1),
            GoldbachPurePrimeAdequacyV15.GoldbachAt
              (centralTargetNat m i) := by
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
    eventual_exists_goldbach_central_target_of_subcritical_energy_bounds
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

end GoldbachCircleMethodCentralSingleSourceEnergyGateV18459
