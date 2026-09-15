import GoldbachCircleMethodHybridRemainingChannelInterfacesV18512
import GoldbachCircleMethodHybridCenteredSingleSourceGateV18509

/-!
# Goldbach V1.8.513: hybrid-channel end-to-end reduction

The three explicit source-channel estimates are connected to the actual
partner-energy theorem and the pure-prime witness transfer.  The active
residual estimate remains a separate pointwise premise.  This theorem is a
complete conditional reduction, not an inhabitant of any analytic interface.
`proof_status = NO_PROOF` remains mandatory.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodHybridChannelEndToEndReductionV18513

open GoldbachCircleMethodActiveResidualExactDecompositionV18251
open GoldbachCircleMethodCanonicalCentralAdjustedPositiveV18403
open GoldbachCircleMethodCanonicalCentralSourceTransferV18404
open GoldbachCircleMethodCenteredPrincipalDecayInterfaceV18503
open GoldbachCircleMethodCenteredPrincipalNetExponentV18504
open GoldbachCircleMethodHybridCenteredCentralMomentV18505
open GoldbachCircleMethodHybridCenteredChannelBudgetSplitV18510
open GoldbachCircleMethodHybridCenteredSingleSourceGateV18509
open GoldbachCircleMethodHybridRemainingChannelInterfacesV18512
open GoldbachCircleMethodStructurallyAdmissibleActiveSlotV18258

/-- End-to-end conditional reduction from the three named hybrid source
interfaces plus the active residual bound to a true Goldbach witness in every
sufficiently large central block. -/
theorem eventual_exists_goldbach_central_target_of_hybrid_channel_estimates :
    ∃ CB : ℝ, 0 ≤ CB ∧ ∀ eps : ℝ, 0 < eps →
      ∃ Kdiv : ℝ, 1 ≤ Kdiv ∧ ∀ eta : ℝ, 0 < eta →
        ∀ (C Cn Ce rho sigma s : ℝ),
        0 ≤ C → 0 ≤ Cn → 0 ≤ Ce → 0 < rho →
        CenteredPrincipalDiscrepancyEstimate C rho sigma →
        NonprincipalPrimitiveBlockEstimate Cn rho s →
        ExceptionalCharacterBlockEstimate Ce rho s →
        1 + 4 * rho - 2 * sigma ≤ s →
        s + 2 * (eps + eta) < 1 →
        ∃ m₀ : ℕ, ∀ {K : ℕ} [NeZero K],
          ∀ (m : ℕ), m₀ ≤ m →
          ∀ (b : ℝ),
          ∀ (hR2 : 2 ≤ ((8 * m : ℕ) : ℝ) ^ rho),
          ((8 * m : ℕ) : ℝ) ^ rho ≤ ((8 * m : ℕ) : ℝ) →
          ∀ (e : StructurallyAdmissibleActiveSlot
            ⌊(((8 * m : ℕ) : ℝ) ^ rho) ^ 2⌋₊),
          (∀ q : GoldbachCircleMethodBoundedConductorReindexV18117.PositiveLevel
            ⌊(((8 * m : ℕ) : ℝ) ^ rho) ^ 2⌋₊, q.val ∣ K) →
          rho ≤ (1 : ℝ) / 10000 →
          GoldbachCircleMethodResidualScaleAdmissionV18196.blockThreshold rho ≤ 8 * m →
          0 ≤ b → b ≤ 1 →
          1 < ((8 * m : ℕ) : ℝ) ^ rho →
          |centralActiveResidualTargetSum m rho hR2 b e| <
            ((8 * m : ℕ) : ℝ) ^ 2 / 256 →
          ∃ i ∈ Finset.range (2 * m + 1),
            GoldbachPurePrimeAdequacyV15.GoldbachAt (centralTargetNat m i) := by
  obtain ⟨CB, hCB, hGate⟩ :=
    eventual_exists_goldbach_central_target_of_hybridCentered_source_gate
  refine ⟨CB, hCB, ?_⟩
  intro eps heps
  obtain ⟨Kdiv, hKdiv, hGateEps⟩ := hGate eps heps
  refine ⟨Kdiv, hKdiv, ?_⟩
  intro eta heta C Cn Ce rho sigma s hC hCn hCe hrho hPrincipal
    hNonprincipal hExceptional hPrincipalExponent hSourceGap
  let Cs : ℝ := C ^ 2 + Cn + Ce
  have hCs : 0 ≤ Cs := by
    dsimp [Cs]
    exact hybridSourceConstant_nonneg C Cn Ce hCn hCe
  obtain ⟨mBase, hBase⟩ := hGateEps eta heta Cs s hCs hSourceGap
  refine ⟨max mBase 1, ?_⟩
  intro K hKinst m hm b hR2 hRB e hConductor hrhoUpper hScale hb hbUpper hR
    hResidual
  have hmBase : mBase ≤ m := (le_max_left mBase 1).trans hm
  have hmOne : 1 ≤ m := (le_max_right mBase 1).trans hm
  have hB : 3 ≤ 8 * m := by omega
  have hSource :
      hybridCenteredSourceBudget (8 * m) rho b e.val ≤
        Cs * ((8 * m : ℕ) : ℝ) ^ s := by
    exact hybridCenteredSourceBudget_le_of_channel_estimates
      C Cn Ce rho sigma s hC hrho hPrincipal hNonprincipal hExceptional
      hPrincipalExponent (8 * m) hB b e.val
  exact hBase m hmBase rho b hR2 hRB e hConductor hrho hrhoUpper hScale hb
    hbUpper hR hResidual hSource

end GoldbachCircleMethodHybridChannelEndToEndReductionV18513
