import GoldbachCircleMethodCentralDivisorEnvelopeV18417

/-!
# Goldbach V1.8.418: central source bridge with one divisor envelope

The literal central von-Mangoldt source theorem is recomposed so that its
targetwise arithmetic-factor conditions are discharged by one scalar envelope
over the complete central sweep.  The divisor-function and character-family
bounds remain explicit analytic premises.

This is a conditional reduction.  It does not prove either premise, does not
extract a pure-prime witness, and leaves `proof_status = NO_PROOF`.
-/

set_option autoImplicit false

open scoped BigOperators Classical ArithmeticFunction

namespace GoldbachCircleMethodCentralDivisorEnvelopeSourceBridgeV18418

open GoldbachCircleMethodActiveExceptionalCenteringV18129
open GoldbachCircleMethodBadPrimeProductComparisonV18165
open GoldbachCircleMethodBlockPairCarrierV18227
open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodCanonicalCentralAdjustedPositiveV18403
open GoldbachCircleMethodCanonicalCentralSourceTransferV18404
open GoldbachCircleMethodCentralDivisorEnvelopeV18417
open GoldbachCircleMethodCentralLiteralSourceInterfaceV18414
open GoldbachCircleMethodCentralLiteralSourceScaleClosedV18415
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

/-- The fully composed central source bridge with a single scalar divisor
envelope replacing every targetwise arithmetic-factor smallness premise. -/
theorem conditional_eventual_positive_central_source_of_divisor_envelope :
    ∃ CE : ℝ, 0 ≤ CE ∧ ∃ CB : ℝ, 0 ≤ CB ∧
      ∀ (D c CH : ℝ) (_hD : 0 ≤ D) (_hCH : 0 ≤ CH)
        (_hweighted : ∀ (X : ℕ), 2 ≤ X → ∀ t : ℝ, 2 ≤ t → t ≤ (X : ℝ) →
          |prefixLogMoment X t - Real.log t| ≤ D)
        (_hharmonic : ∀ (X : ℕ), 2 ≤ X → ∀ t : ℝ, 2 ≤ t → t ≤ (X : ℝ) →
          |prefixHarmonicMoment X t - Real.log (Real.log t) - c| ≤
            D / Real.log t)
        (rho : ℝ) (_hrho : 0 < rho)
        (_hrhoUpper : rho ≤ (1 : ℝ) / 10000)
        (CV : ℝ) (_hCV : 0 ≤ CV) (_hV : RealVaughanEstimate CV),
      ∃ m₀ : ℕ, ∀ (m : ℕ), m₀ ≤ m →
        ∀ CT eps : ℝ, 0 ≤ CT → 0 ≤ eps →
        (∀ n : ℕ, 0 < n →
          (n.divisors.card : ℝ) ≤ CT * (n : ℝ) ^ eps) →
        ∀ {K : ℕ} [NeZero K],
        ∀ b A : ℝ, 0 ≤ b → b ≤ 1 → 0 ≤ A →
        ∀ e : StructurallyAdmissibleActiveSlot
          ⌊(((8 * m : ℕ) : ℝ) ^ rho) ^ 2⌋₊,
        (∀ q : PositiveLevel ⌊(((8 * m : ℕ) : ℝ) ^ rho) ^ 2⌋₊,
          q.val ∣ K) →
        (∀ i ∈ Finset.range (2 * m + 1), ∀ xi eta' : ℝ,
          arithmeticCorrelation (((8 * m : ℕ) : ℝ) ^ rho) xi eta'
              (Finset.Ioc ((8 * m) / 2) (8 * m))
              (centralTargetNat m i) ≤
            CH * (((8 * m : ℕ) : ℝ) / 2) *
              finiteSieveProduct (centralTargetNat m i) ((8 * m) / 2) *
              goodBadProduct (((8 * m : ℕ) : ℝ) ^ rho) xi eta'
                (centralTargetNat m i) ((8 * m) / 2)) →
        (∀ n ∈ blockCarrier (8 * m),
          exactUnstarredActiveSourceMass
            ⌊(((8 * m : ℕ) : ℝ) ^ rho) ^ 2⌋₊
            (8 * m) n
            (((8 * m : ℕ) : ℝ) /
              (((8 * m : ℕ) : ℝ) ^ rho) ^ 4)
            b e.val ≤ A) →
        ((2 * A) * (CT * ((14 * m : ℕ) : ℝ) ^ eps) *
            centeredCorrectionDimensionlessCoefficient
              CE CB D c CH rho < (1 : ℝ) / 2048) →
        0 < centralBlockSourceTargetSum m ∧
          ∃ i ∈ Finset.range (2 * m + 1),
            0 < (GoldbachCircleMethodActualResidualExactDecompositionV18225.canonicalBlockSourceAt
              (8 * m) ((centralTargetNat m i : ℕ) : ℤ)).re := by
  obtain ⟨CE, hCE, CB, hCB, hbridge⟩ :=
    conditional_eventual_positive_central_source_of_literal_family_bound_scale_closed
  refine ⟨CE, hCE, CB, hCB, ?_⟩
  intro D c CH hD hCH hweighted hharmonic rho hrho hrhoUpper CV hCV hV
  obtain ⟨m₁, hcore⟩ :=
    hbridge D c CH hD hCH hweighted hharmonic rho hrho hrhoUpper CV hCV hV
  let m₀ := max m₁ 1
  refine ⟨m₀, ?_⟩
  intro m hm CT eps hCT heps hdivisor K hKinst b A hb hb1 hA e hK
    hcorrelation hsource hscalar
  have hm₁ : m₁ ≤ m := (le_max_left m₁ 1).trans hm
  have hm1 : 1 ≤ m := (le_max_right m₁ 1).trans hm
  apply hcore m hm₁ b A hb hb1 hA e hK hcorrelation hsource
  exact central_targetwise_smallness_of_divisor_envelope
    CE CB D c CH rho A CT eps hCE hCB hCH hrho hA hCT heps
      hdivisor m hm1 hscalar

end GoldbachCircleMethodCentralDivisorEnvelopeSourceBridgeV18418
