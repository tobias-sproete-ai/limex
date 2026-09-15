import GoldbachCircleMethodCentralCenteredDimensionlessInterfaceV18412

/-!
# Goldbach V1.8.413: central conditional source bridge

This module closes the complete logical composition of V1.8.403--V1.8.412.
Under the explicitly named Vaughan input, Mertens inputs, arithmetic-correlation
bound, active fluctuation-mass bound, and dimensionless smallness condition, a
sufficiently large central sweep has positive literal von-Mangoldt source
aggregate and hence contains one positive literal source target.

Every analytic input remains in the theorem signature.  This is a Class-IV
conditional reduction only.  It proves neither the analytic premises nor a
pure-prime witness, and the project status remains `NO_PROOF`.
-/

set_option autoImplicit false

open scoped BigOperators Classical ArithmeticFunction

namespace GoldbachCircleMethodCentralConditionalSourceBridgeV18413

open GoldbachCircleMethodActiveCharacterRadicalErrorV18158
open GoldbachCircleMethodActiveExceptionalCenteringV18129
open GoldbachCircleMethodBadPrimeProductComparisonV18165
open GoldbachCircleMethodBlockPairCarrierV18227
open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodCanonicalCentralAdjustedPositiveV18403
open GoldbachCircleMethodCanonicalCentralSingleObstructionV18410
open GoldbachCircleMethodCanonicalCentralSourceTransferV18404
open GoldbachCircleMethodCentralCenteredDimensionlessInterfaceV18412
open GoldbachCircleMethodCenteredDimensionlessBudgetV18411
open GoldbachCircleMethodDirectLambdaRadicalDominationV18178
open GoldbachCircleMethodDisjointPrimeFactorCompositionV18171
open GoldbachCircleMethodFiniteCompanionBindingV18118
open GoldbachCircleMethodGlobalSieveFiniteFactorV18173
open GoldbachCircleMethodLogCutoffPresieveBindingV18120
open GoldbachCircleMethodMertensUniformConstantsV18168
open GoldbachCircleMethodRadicalCorrelationTransferV18161
open GoldbachCircleMethodRealApproximationMinorAdapterV1873
open GoldbachCircleMethodStructurallyAdmissibleActiveSlotV18258

/-- Fully composed conditional central source bridge.  The conclusion remains
strictly at the literal von-Mangoldt source layer. -/
theorem conditional_eventual_positive_central_von_mangoldt_source :
    ∃ CE : ℝ, 0 ≤ CE ∧ ∃ CB : ℝ, 0 ≤ CB ∧
      ∀ (D c CH : ℝ) (_hD : 0 ≤ D) (_hCH : 0 ≤ CH)
        (_hweighted : ∀ (X : ℕ), 2 ≤ X → ∀ t : ℝ, 2 ≤ t → t ≤ (X : ℝ) →
          |prefixLogMoment X t - Real.log t| ≤ D)
        (_hharmonic : ∀ (X : ℕ), 2 ≤ X → ∀ t : ℝ, 2 ≤ t → t ≤ (X : ℝ) →
          |prefixHarmonicMoment X t - Real.log (Real.log t) - c| ≤
            D / Real.log t)
        (rho : ℝ) (_hrho : 0 < rho)
        (_hrhoUpper : rho ≤ (1 : ℝ) / 10000)
        (C : ℝ) (_hC : 0 ≤ C) (_hV : RealVaughanEstimate C),
      ∃ m₀ : ℕ, ∀ (m : ℕ), m₀ ≤ m →
        ∀ {K : ℕ} [NeZero K],
        ∀ b eta : ℝ, 0 ≤ b → b ≤ 1 → 0 ≤ eta →
        ∀ e : StructurallyAdmissibleActiveSlot
          ⌊(((8 * m : ℕ) : ℝ) ^ rho) ^ 2⌋₊,
        (∀ q : PositiveLevel ⌊(((8 * m : ℕ) : ℝ) ^ rho) ^ 2⌋₊,
          q.val ∣ K) →
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
        0 < centralBlockSourceTargetSum m ∧
          ∃ i ∈ Finset.range (2 * m + 1),
            0 < (GoldbachCircleMethodActualResidualExactDecompositionV18225.canonicalBlockSourceAt
              (8 * m) ((centralTargetNat m i : ℕ) : ℤ)).re := by
  obtain ⟨CE, hCE, CB, hCB, hcenteredCore⟩ :=
    eventual_central_adjusted_centered_error_of_dimensionless_source
  refine ⟨CE, hCE, CB, hCB, ?_⟩
  intro D c CH hD hCH hweighted hharmonic rho hrho hrhoUpper C hC hV
  obtain ⟨B₀, hcentered⟩ :=
    hcenteredCore D c CH hD hCH hweighted hharmonic rho hrho
      (hrhoUpper.trans (by norm_num : (1 : ℝ) / 10000 ≤ 1))
  obtain ⟨m₁, hsource⟩ :=
    eventual_central_source_positive_of_centered_error_bound
      C rho hC hV hrho hrhoUpper
  let m₀ := max (max m₁ B₀) 1
  refine ⟨m₀, ?_⟩
  intro m hm K hKinst b eta hb hb1 heta e hK hcorrelation hmass hdimensionless
  have hinner : max m₁ B₀ ≤ m₀ := le_max_left _ _
  have hm₁ : m₁ ≤ m := (le_max_left m₁ B₀).trans (hinner.trans hm)
  have hB₀m : B₀ ≤ m := (le_max_right m₁ B₀).trans (hinner.trans hm)
  have hm1 : 1 ≤ m := (le_max_right (max m₁ B₀) 1).trans hm
  have hCentered :
      |centralAdjustedCenteredErrorTargetSum m rho b e| <
        ((8 * m : ℕ) : ℝ) ^ 2 / 2048 := by
    exact hcentered m hm1 b eta e (by omega) hb heta
      hcorrelation hmass hdimensionless
  exact hsource m hm₁ b hb hb1 e hK hCentered

end GoldbachCircleMethodCentralConditionalSourceBridgeV18413
