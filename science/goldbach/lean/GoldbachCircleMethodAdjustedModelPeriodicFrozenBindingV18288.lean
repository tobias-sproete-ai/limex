import GoldbachCircleMethodNormalizedToAmplitudeTransferObstructionV18287
import GoldbachCircleMethodActualFrozenModelCompleteDiagonalV18213

/-!
# Goldbach V1.8.288: adjusted-model periodic frozen binding

This module binds each natural-input adjusted model factor to the already
audited periodic frozen coefficient on a proof-carrying common period.  The
spatial power remains evaluated at the actual natural input; it is not frozen
across an interval.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodAdjustedModelPeriodicFrozenBindingV18288

open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodFiniteCompanionBindingV18118
open GoldbachCircleMethodLogCutoffPresieveBindingV18120
open GoldbachCircleMethodPrincipalWindowBoundaryV18121
open GoldbachCircleMethodExceptionalWeightBoundaryV18128
open GoldbachCircleMethodActiveExceptionalCenteringV18129
open GoldbachCircleMethodActualCompanionPeriodicLiftV18202
open GoldbachCircleMethodActualPrincipalTwistCrossDiagonalV18210
open GoldbachCircleMethodActualFrozenModelCompleteDiagonalV18213
open GoldbachCircleMethodSupportedModelErrorConvolutionV18182
open GoldbachCircleMethodActualResidualExactDecompositionV18225
open GoldbachCircleMethodBlockPairCarrierV18227
open GoldbachCircleMethodActiveResidualExactDecompositionV18251
open GoldbachCircleMethodCanonicalBumpPrincipalFloorV18220
open GoldbachCircleMethodSupportedAdjustedModelBindingAuditV18285

/-- Exact pointwise readback of the natural adjusted model as the periodic
frozen coefficient with the literal spatial power at `N`. -/
theorem adjustedModel_eq_frozenCoefficient_natCast
    {Q K : ℕ} [NeZero K]
    (hK : ∀ l : PositiveLevel Q, l.val ∣ K)
    (N : ℕ) (hQ : 1 ≤ Q) (b : ℝ) (w : ℕ → ℂ)
    (e : CharacterSlot Q) :
    adjustedModel Q N hQ b w e =
      frozenCoefficient hQ e.1 e.2 w (powerWeight b N : ℂ)
        (N : ZMod K) := by
  have hCoeffReadback := periodic_windowCoefficient_readback
    hK e.1 e.2 w (N : ZMod K)
  have hCoeff :
      windowCoefficient e.1 (N : ZMod K).val w e.2 =
        windowCoefficient e.1 N w e.2 := by
    rw [hCoeffReadback]
    unfold windowCoefficient
    rw [periodicCompanion_natCast hK]
    simp only [map_natCast]
  unfold adjustedModel frozenCoefficient
  rw [periodicCompanion_natCast hK, hCoeff]
  ring

/-- The actual canonical adjusted convolution is therefore an exact finite
sum of periodic frozen coefficients carrying variable spatial powers. -/
theorem canonicalAdjustedModelAt_nat_eq_variableFrozenPairSum
    {K : ℕ} [NeZero K]
    (B N : ℕ) (rho b : ℝ)
    (e : CharacterSlot ⌊((B : ℝ)^rho)^2⌋₊)
    (hK : ∀ l : PositiveLevel ⌊((B : ℝ)^rho)^2⌋₊, l.val ∣ K)
    (hR : 1 < (B : ℝ)^rho) (hBN : B ≤ N) :
    canonicalAdjustedModelAt B rho b e (N : ℤ) =
      ∑ n ∈ pairFirstCarrier (blockCarrier B) N,
        frozenCoefficient
            (log_cutoff_contains_one ((B : ℝ)^rho) hR)
            e.1 e.2 (logWeight ((B : ℝ)^rho) canonicalLogBump)
            (powerWeight b n : ℂ) (n : ZMod K) *
          frozenCoefficient
            (log_cutoff_contains_one ((B : ℝ)^rho) hR)
            e.1 e.2 (logWeight ((B : ℝ)^rho) canonicalLogBump)
            (powerWeight b (N-n) : ℂ) ((N-n : ℕ) : ZMod K) := by
  rw [canonicalAdjustedModelAt_nat_eq_amplitudeAdjustedFullPairSum
    B N rho b e hR hBN]
  unfold amplitudeAdjustedFullPairSum amplitudeAdjustedPairKernel
  apply Finset.sum_congr rfl
  intro n _hn
  rw [← adjustedModel_eq_amplitudeAdjustedFactor,
    ← adjustedModel_eq_amplitudeAdjustedFactor]
  rw [adjustedModel_eq_frozenCoefficient_natCast hK,
    adjustedModel_eq_frozenCoefficient_natCast hK]

end GoldbachCircleMethodAdjustedModelPeriodicFrozenBindingV18288

