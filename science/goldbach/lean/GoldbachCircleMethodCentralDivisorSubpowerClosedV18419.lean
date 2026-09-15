import GoldbachCircleMethodCentralDivisorEnvelopeSourceBridgeV18418
import GoldbachCircleMethodDivisorSubpowerExistenceV18191

/-!
# Goldbach V1.8.419: close the divisor subpower input

For every selected positive exponent, the previously kernel-checked elementary
divisor theorem supplies a fixed constant controlling the central arithmetic
factor.  The divisor estimate is therefore no longer an open premise of the
central source bridge.

The literal character-family bound and its required scalar decay remain open.
This module is conditional and does not prove Goldbach.
-/

set_option autoImplicit false

open scoped BigOperators Classical ArithmeticFunction

namespace GoldbachCircleMethodCentralDivisorSubpowerClosedV18419

open GoldbachCircleMethodActiveExceptionalCenteringV18129
open GoldbachCircleMethodBadPrimeProductComparisonV18165
open GoldbachCircleMethodBlockPairCarrierV18227
open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodCanonicalCentralAdjustedPositiveV18403
open GoldbachCircleMethodCanonicalCentralSourceTransferV18404
open GoldbachCircleMethodCentralDivisorEnvelopeSourceBridgeV18418
open GoldbachCircleMethodCentralLiteralSourceInterfaceV18414
open GoldbachCircleMethodCenteredDimensionlessBudgetV18411
open GoldbachCircleMethodDirectLambdaRadicalDominationV18178
open GoldbachCircleMethodDisjointPrimeFactorCompositionV18171
open GoldbachCircleMethodDivisorSubpowerExistenceV18191
open GoldbachCircleMethodFiniteCompanionBindingV18118
open GoldbachCircleMethodGlobalSieveFiniteFactorV18173
open GoldbachCircleMethodLogCutoffPresieveBindingV18120
open GoldbachCircleMethodMertensUniformConstantsV18168
open GoldbachCircleMethodRadicalCorrelationTransferV18161
open GoldbachCircleMethodRealApproximationMinorAdapterV1873
open GoldbachCircleMethodStructurallyAdmissibleActiveSlotV18258

/-- The divisor-function growth input is discharged by V1.8.191.  What remains
is one explicit source-decay condition at an arbitrarily chosen positive
subpower exponent. -/
theorem conditional_eventual_positive_central_source_with_divisor_closed :
    ∃ CE : ℝ, 0 ≤ CE ∧ ∃ CB : ℝ, 0 ≤ CB ∧
      ∀ (D c CH : ℝ) (_hD : 0 ≤ D) (_hCH : 0 ≤ CH)
        (_hweighted : ∀ (X : ℕ), 2 ≤ X → ∀ t : ℝ, 2 ≤ t → t ≤ (X : ℝ) →
          |prefixLogMoment X t - Real.log t| ≤ D)
        (_hharmonic : ∀ (X : ℕ), 2 ≤ X → ∀ t : ℝ, 2 ≤ t → t ≤ (X : ℝ) →
          |prefixHarmonicMoment X t - Real.log (Real.log t) - c| ≤
            D / Real.log t)
        (rho : ℝ) (_hrho : 0 < rho)
        (_hrhoUpper : rho ≤ (1 : ℝ) / 10000)
        (CV : ℝ) (_hCV : 0 ≤ CV) (_hV : RealVaughanEstimate CV)
        (eps : ℝ) (_heps : 0 < eps),
      ∃ CT : ℝ, 1 ≤ CT ∧
      ∃ m₀ : ℕ, ∀ (m : ℕ), m₀ ≤ m →
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
    conditional_eventual_positive_central_source_of_divisor_envelope
  refine ⟨CE, hCE, CB, hCB, ?_⟩
  intro D c CH hD hCH hweighted hharmonic rho hrho hrhoUpper CV hCV hV eps heps
  obtain ⟨CT, hCT, hdivisor⟩ := exists_divisors_card_le_const_mul_rpow heps
  obtain ⟨m₀, hcore⟩ :=
    hbridge D c CH hD hCH hweighted hharmonic rho hrho hrhoUpper CV hCV hV
  refine ⟨CT, hCT, m₀, ?_⟩
  intro m hm K hKinst b A hb hb1 hA e hK hcorrelation hsource hscalar
  exact hcore m hm CT eps (zero_le_one.trans hCT) heps.le hdivisor
    b A hb hb1 hA e hK hcorrelation hsource hscalar

end GoldbachCircleMethodCentralDivisorSubpowerClosedV18419
