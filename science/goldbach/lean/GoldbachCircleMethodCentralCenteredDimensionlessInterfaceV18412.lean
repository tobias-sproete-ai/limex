import GoldbachCircleMethodCenteredDimensionlessBudgetV18411

/-!
# Goldbach V1.8.412: central centered dimensionless interface

The V1.8.405 central centered-error theorem is re-expressed through the exact
dimensionless factorization of V1.8.411.  The targetwise numerical budget is
no longer an opaque expression involving the block scale.  Its remaining
analytic content is the explicit condition

`eta * arithmeticFactor(N) * centeredCoefficient < 1/2048`.

All Mertens, arithmetic-correlation, and active fluctuation-mass premises stay
visible.  No inhabitant of those source estimates is constructed here.
-/

set_option autoImplicit false

open scoped BigOperators Classical ArithmeticFunction

namespace GoldbachCircleMethodCentralCenteredDimensionlessInterfaceV18412

open GoldbachCircleMethodActiveCharacterRadicalErrorV18158
open GoldbachCircleMethodActiveExceptionalCenteringV18129
open GoldbachCircleMethodBadPrimeProductComparisonV18165
open GoldbachCircleMethodBlockPairCarrierV18227
open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodCanonicalCentralAdjustedPositiveV18403
open GoldbachCircleMethodCanonicalCentralCenteredErrorAggregateV18405
open GoldbachCircleMethodCanonicalCentralSourceTransferV18404
open GoldbachCircleMethodCenteredDimensionlessBudgetV18411
open GoldbachCircleMethodDirectLambdaRadicalDominationV18178
open GoldbachCircleMethodDisjointPrimeFactorCompositionV18171
open GoldbachCircleMethodFiniteCompanionBindingV18118
open GoldbachCircleMethodGlobalSieveFiniteFactorV18173
open GoldbachCircleMethodLogCutoffPresieveBindingV18120
open GoldbachCircleMethodMertensUniformConstantsV18168
open GoldbachCircleMethodRadicalCorrelationTransferV18161
open GoldbachCircleMethodStructurallyAdmissibleActiveSlotV18258

/-- Exact central centered-error interface with the numerical block scale
cancelled out of the final source condition. -/
theorem eventual_central_adjusted_centered_error_of_dimensionless_source :
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
        (∀ i ∈ Finset.range (2 * m + 1), ∀ ξ η' : ℝ,
          arithmeticCorrelation (((8 * m : ℕ) : ℝ) ^ rho) ξ η'
              (Finset.Ioc ((8 * m) / 2) (8 * m))
              (centralTargetNat m i) ≤
            CH * (((8 * m : ℕ) : ℝ) / 2) *
              finiteSieveProduct (centralTargetNat m i) ((8 * m) / 2) *
              goodBadProduct (((8 * m : ℕ) : ℝ) ^ rho) ξ η'
                (centralTargetNat m i) ((8 * m) / 2)) →
        (∀ n ∈ blockCarrier (8 * m),
          activeFluctuationMass ⌊(((8 * m : ℕ) : ℝ) ^ rho) ^ 2⌋₊
            (8 * m) n
            (((8 * m : ℕ) : ℝ) /
              (((8 * m : ℕ) : ℝ) ^ rho) ^ 4)
            b (blockInput (8 * m)) e.val ≤ eta) →
        (∀ i ∈ Finset.range (2 * m + 1),
          eta * arithmeticFactor (centralTargetNat m i) *
              centeredCorrectionDimensionlessCoefficient
                CE CB D c CH rho < (1 : ℝ) / 2048) →
        |centralAdjustedCenteredErrorTargetSum m rho b e| <
          ((8 * m : ℕ) : ℝ) ^ 2 / 2048 := by
  obtain ⟨CE, hCE, CB, hCB, hcore⟩ :=
    eventual_central_adjusted_centered_error_target_sum_lt_one_over_2048
  refine ⟨CE, hCE, CB, hCB, ?_⟩
  intro D c CH hD hCH hweighted hharmonic rho hrho hrho1
  obtain ⟨B₀, hbound⟩ :=
    hcore D c CH hD hCH hweighted hharmonic rho hrho hrho1
  refine ⟨B₀, ?_⟩
  intro m hm b eta e hB₀ hb heta hsource hmass hdimensionless
  apply hbound m hm b eta e hB₀ hb heta hsource hmass
  intro i hi
  exact adjusted_centered_budget_lt_one_over_2048_of_dimensionless
    CE CB D c CH rho eta (8 * m) (centralTargetNat m i)
    (by omega) (hdimensionless i hi)

end GoldbachCircleMethodCentralCenteredDimensionlessInterfaceV18412
