import GoldbachCircleMethodHybridAugmentedNonprincipalChannelV18514
import GoldbachCircleMethodHybridCenteredSingleSourceGateV18509

/-!
# Goldbach V1.8.515: hybrid two-channel end-to-end reduction

Structural admissibility absorbs the selected exceptional coefficient into
the augmented nonprincipal channel.  Consequently, only two source estimates
are required in the end-to-end reduction: the principal `Lambda - 1`
discrepancy and the augmented nonprincipal block estimate.  The active
residual remains an independent premise.  No estimate is inhabited here.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodHybridTwoChannelEndToEndReductionV18515

open GoldbachCircleMethodActiveResidualExactDecompositionV18251
open GoldbachCircleMethodCanonicalCentralAdjustedPositiveV18403
open GoldbachCircleMethodCanonicalCentralSourceTransferV18404
open GoldbachCircleMethodCenteredPrincipalDecayInterfaceV18503
open GoldbachCircleMethodCenteredPrincipalNetExponentV18504
open GoldbachCircleMethodHybridAugmentedNonprincipalChannelV18514
open GoldbachCircleMethodHybridCenteredCentralMomentV18505
open GoldbachCircleMethodHybridCenteredSingleSourceGateV18509
open GoldbachCircleMethodStructurallyAdmissibleActiveSlotV18258

/-- Kernel-checked end-to-end reduction with the minimal two-channel source
interface exposed. -/
theorem eventual_exists_goldbach_central_target_of_hybrid_two_channel_estimates :
    ∃ CB : ℝ, 0 ≤ CB ∧ ∀ eps : ℝ, 0 < eps →
      ∃ Kdiv : ℝ, 1 ≤ Kdiv ∧ ∀ eta : ℝ, 0 < eta →
        ∀ (C Ca rho sigma s : ℝ),
        0 ≤ C → 0 ≤ Ca → 0 < rho →
        CenteredPrincipalDiscrepancyEstimate C rho sigma →
        AugmentedNonprincipalBlockEstimate Ca rho s →
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
  intro eta heta C Ca rho sigma s hC hCa hrho hPrincipal hAugmented
    hPrincipalExponent hSourceGap
  let Cs : ℝ := C ^ 2 + Ca
  have hCs : 0 ≤ Cs := by
    dsimp [Cs]
    positivity
  obtain ⟨mBase, hBase⟩ := hGateEps eta heta Cs s hCs hSourceGap
  refine ⟨max mBase 1, ?_⟩
  intro K hKinst m hm b hR2 hRB e hConductor hrhoUpper hScale hb hbUpper hR
    hResidual
  have hmBase : mBase ≤ m := (le_max_left mBase 1).trans hm
  have hB : 3 ≤ 8 * m := by
    have hmOne : 1 ≤ m := (le_max_right mBase 1).trans hm
    omega
  have hSource :
      hybridCenteredSourceBudget (8 * m) rho b e.val ≤
        Cs * ((8 * m : ℕ) : ℝ) ^ s := by
    exact hybridCenteredSourceBudget_le_of_two_channel_estimates
      C Ca rho sigma s hC hrho hPrincipal hAugmented hPrincipalExponent
      (8 * m) hB b e
  exact hBase m hmBase rho b hR2 hRB e hConductor hrho hrhoUpper hScale hb
    hbUpper hR hResidual hSource

end GoldbachCircleMethodHybridTwoChannelEndToEndReductionV18515
