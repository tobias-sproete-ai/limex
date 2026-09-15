import GoldbachCircleMethodCentralArithmeticMeanBudgetV18424
import GoldbachCircleMethodAdjustedCenteredCorrectionV182CompositionV18253

/-!
# Goldbach V1.8.425: central correction mean majorant

The literal targetwise V1.8.253 correction bounds are summed *before*
numerical absorption.  The resulting central correction is controlled by the
exact V1.8.424 aggregate budget and therefore exposes an arithmetic-factor
mean rather than a targetwise worst case.

All source, correlation, Mertens, and fluctuation-mass inputs remain explicit.
No analytic mean-value theorem is supplied here and `proof_status = NO_PROOF`.
-/

set_option autoImplicit false

open scoped BigOperators Classical ArithmeticFunction

namespace GoldbachCircleMethodCentralCorrectionMeanMajorantV18425

open GoldbachCircleMethodActiveCharacterRadicalErrorV18158
open GoldbachCircleMethodActiveExceptionalCenteringV18129
open GoldbachCircleMethodActiveResidualExactDecompositionV18251
open GoldbachCircleMethodAdjustedCenteredCorrectionV182CompositionV18253
open GoldbachCircleMethodAdjustedCenteredCorrectionNumericAbsorptionV18254
open GoldbachCircleMethodBadPrimeProductComparisonV18165
open GoldbachCircleMethodBlockPairCarrierV18227
open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodCanonicalCentralAdjustedPositiveV18403
open GoldbachCircleMethodCanonicalCentralSourceTransferV18404
open GoldbachCircleMethodCanonicalCentralCenteredErrorAggregateV18405
open GoldbachCircleMethodCentralArithmeticMeanBudgetV18424
open GoldbachCircleMethodDirectLambdaRadicalDominationV18178
open GoldbachCircleMethodDisjointPrimeFactorCompositionV18171
open GoldbachCircleMethodFiniteCompanionBindingV18118
open GoldbachCircleMethodGlobalSieveFiniteFactorV18173
open GoldbachCircleMethodLogCutoffPresieveBindingV18120
open GoldbachCircleMethodMertensUniformConstantsV18168
open GoldbachCircleMethodRadicalCorrelationTransferV18161
open GoldbachCircleMethodStructurallyAdmissibleActiveSlotV18258

/-- Exact aggregate form of V1.8.253.  No pointwise numerical budget is used:
the complete correction is bounded by the sum of its literal majorants. -/
theorem eventual_central_adjusted_centered_error_le_mean_budget :
    ∃ CE : ℝ, 0 ≤ CE ∧ ∃ CB : ℝ, 0 ≤ CB ∧
      ∀ (D c CH : ℝ) (_hD : 0 ≤ D) (_hCH : 0 ≤ CH)
        (_hweighted : ∀ (X : ℕ), 2 ≤ X → ∀ t : ℝ, 2 ≤ t → t ≤ (X : ℝ) →
          |prefixLogMoment X t - Real.log t| ≤ D)
        (_hharmonic : ∀ (X : ℕ), 2 ≤ X → ∀ t : ℝ, 2 ≤ t → t ≤ (X : ℝ) →
          |prefixHarmonicMoment X t - Real.log (Real.log t) - c| ≤
            D / Real.log t)
        (rho : ℝ) (_hrho : 0 < rho) (_hrho1 : rho ≤ 1),
      ∃ B₀ : ℕ, ∀ (m : ℕ) (_hm : 1 ≤ m) (b eta : ℝ)
        (e : StructurallyAdmissibleActiveSlot
          ⌊(((8 * m : ℕ) : ℝ) ^ rho) ^ 2⌋₊),
        B₀ ≤ 8 * m → 0 ≤ b → 0 ≤ eta →
        (∀ i ∈ Finset.range (2 * m + 1), ∀ ξ eta' : ℝ,
          arithmeticCorrelation (((8 * m : ℕ) : ℝ) ^ rho) ξ eta'
              (Finset.Ioc ((8 * m) / 2) (8 * m)) (centralTargetNat m i) ≤
            CH * (((8 * m : ℕ) : ℝ) / 2) *
              finiteSieveProduct (centralTargetNat m i) ((8 * m) / 2) *
              goodBadProduct (((8 * m : ℕ) : ℝ) ^ rho) ξ eta'
                (centralTargetNat m i) ((8 * m) / 2)) →
        (∀ n ∈ blockCarrier (8 * m),
          activeFluctuationMass ⌊(((8 * m : ℕ) : ℝ) ^ rho) ^ 2⌋₊
            (8 * m) n
            (((8 * m : ℕ) : ℝ) /
              (((8 * m : ℕ) : ℝ) ^ rho) ^ 4)
            b (blockInput (8 * m)) e.val ≤ eta) →
        |centralAdjustedCenteredErrorTargetSum m rho b e| ≤
          centralAdjustedCenteredBudgetSum CE CB D c CH rho eta m := by
  obtain ⟨CE, hCE, CB, hCB, hcore⟩ :=
    eventual_canonicalAdjustedCenteredErrorCorrectionAt_bound
  refine ⟨CE, hCE, CB, hCB, ?_⟩
  intro D c CH hD hCH hweighted hharmonic rho hrho hrho1
  obtain ⟨B₀, hbound⟩ :=
    hcore D c CH hD hCH hweighted hharmonic rho hrho hrho1
  refine ⟨B₀, ?_⟩
  intro m hm b eta e hB₀ hb heta hsource hmass
  have hpoint (i : ℕ) (hi : i ∈ Finset.range (2 * m + 1)) :
      |(canonicalAdjustedCenteredErrorCorrectionAt
          (8 * m) rho b e.val ((centralTargetNat m i : ℕ) : ℤ)).re| ≤
        adjustedCenteredCorrectionBudgetExpression
          CE CB D c CH rho eta (8 * m) (centralTargetNat m i) := by
    have hi' : i < 2 * m + 1 := Finset.mem_range.mp hi
    have hnorm := hbound b eta e.val hB₀
      (by simp only [centralTargetNat]; omega)
      (by simp only [centralTargetNat]; omega)
      hb heta (hsource i hi) hmass
    exact (Complex.abs_re_le_norm _).trans (by
      simpa only [adjustedCenteredCorrectionBudgetExpression] using hnorm)
  unfold centralAdjustedCenteredErrorTargetSum centralAdjustedCenteredBudgetSum
  calc
    |∑ i ∈ Finset.range (2 * m + 1),
        (canonicalAdjustedCenteredErrorCorrectionAt
          (8 * m) rho b e.val ((centralTargetNat m i : ℕ) : ℤ)).re| ≤
      ∑ i ∈ Finset.range (2 * m + 1),
        |(canonicalAdjustedCenteredErrorCorrectionAt
          (8 * m) rho b e.val ((centralTargetNat m i : ℕ) : ℤ)).re| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range (2 * m + 1),
        adjustedCenteredCorrectionBudgetExpression
          CE CB D c CH rho eta (8 * m) (centralTargetNat m i) :=
            Finset.sum_le_sum hpoint

end GoldbachCircleMethodCentralCorrectionMeanMajorantV18425
