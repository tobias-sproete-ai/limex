import GoldbachCircleMethodCentralConditionalSourceBridgeV18413
import GoldbachCircleMethodUnstarredIntervalSourceBindingV18188

/-!
# Goldbach V1.8.414: central literal source-family interface

The abstract active-fluctuation parameter in V1.8.413 is pulled back to the
literal, unstarred von-Mangoldt character sums on the exact clipped interval.
The normalization loss is exactly the already verified factor two.  Thus the
remaining centered-channel condition is displayed directly as

`(2*A) * arithmeticFactor(N) * centeredCoefficient < 1/2048`.

The source-family estimate itself remains an explicit analytic premise.  This
module neither proves that estimate nor extracts a pure-prime witness.
-/

set_option autoImplicit false

open scoped BigOperators Classical ArithmeticFunction

namespace GoldbachCircleMethodCentralLiteralSourceInterfaceV18414

open GoldbachCircleMethodActiveCharacterRadicalErrorV18158
open GoldbachCircleMethodActiveExceptionalCenteringV18129
open GoldbachCircleMethodActualCharacterFamilyInclusionV18186
open GoldbachCircleMethodBadPrimeProductComparisonV18165
open GoldbachCircleMethodBlockPairCarrierV18227
open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodCanonicalCentralAdjustedPositiveV18403
open GoldbachCircleMethodCentralConditionalSourceBridgeV18413
open GoldbachCircleMethodCanonicalCentralSourceTransferV18404
open GoldbachCircleMethodCenteredDimensionlessBudgetV18411
open GoldbachCircleMethodDirectLambdaRadicalDominationV18178
open GoldbachCircleMethodDisjointPrimeFactorCompositionV18171
open GoldbachCircleMethodExceptionalWeightBoundaryV18128
open GoldbachCircleMethodFiniteCompanionBindingV18118
open GoldbachCircleMethodFiniteWindowConvolutionV18119
open GoldbachCircleMethodGlobalSieveFiniteFactorV18173
open GoldbachCircleMethodLogCutoffPresieveBindingV18120
open GoldbachCircleMethodMertensUniformConstantsV18168
open GoldbachCircleMethodRadicalCorrelationTransferV18161
open GoldbachCircleMethodRealApproximationMinorAdapterV1873
open GoldbachCircleMethodStructurallyAdmissibleActiveSlotV18258
open GoldbachCircleMethodUnstarredIntervalSourceBindingV18188

/-- Literal unstarred active source mass on the exact clipped block interval.
The exceptional correction is retained inside the same whole norm. -/
noncomputable def exactUnstarredActiveSourceMass
    (Q B N : ℕ) (H b : ℝ) (e : CharacterSlot Q) : ℝ :=
  ∑ t : CharacterSlot Q,
    ‖∑ U ∈ Finset.Icc (max (B / 2 + 1) (N - ⌊H⌋₊))
        (min B (N + ⌊H⌋₊)),
      (((ArithmeticFunction.vonMangoldt U : ℂ) *
        t.2.val (U : ZMod t.1.val) -
        if t.1.val = 1 then 1 else 0) +
        if t = includeSlot (le_refl Q) e then
          (powerWeight b U : ℂ) else 0)‖ /
      (((Finset.Icc (max (B / 2 + 1) (N - ⌊H⌋₊))
        (min B (N + ⌊H⌋₊))).card : ℝ) + H)

/-- The literal same-cutoff source estimate controls the actual active mass
with the exact factor two from finite window normalization. -/
theorem active_mass_le_twice_exact_unstarred_source
    (Q B N : ℕ) (hB : 6 ≤ B) (hN : N ∈ blockCarrier B)
    {H A : ℝ} (hH : 1 ≤ H) (b : ℝ) (e : CharacterSlot Q)
    (hsource : exactUnstarredActiveSourceMass Q B N H b e ≤ A) :
    activeFluctuationMass Q B N H b (blockInput B) e ≤ 2 * A := by
  apply active_mass_from_unstarred_interval_source_included
    (Q := Q) (Q' := Q) (le_refl Q) B N hB hN hH b e
  intro _hleft _hne
  exact hsource

/-- Fully composed central source bridge with the remaining active-character
input written at the literal von-Mangoldt source-family level. -/
theorem conditional_eventual_positive_central_source_of_literal_family_bound :
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
        ∀ b A : ℝ, 0 ≤ b → b ≤ 1 → 0 ≤ A →
        ∀ e : StructurallyAdmissibleActiveSlot
          ⌊(((8 * m : ℕ) : ℝ) ^ rho) ^ 2⌋₊,
        (∀ q : PositiveLevel ⌊(((8 * m : ℕ) : ℝ) ^ rho) ^ 2⌋₊,
          q.val ∣ K) →
        1 ≤ (((8 * m : ℕ) : ℝ) /
          (((8 * m : ℕ) : ℝ) ^ rho) ^ 4) →
        (∀ i ∈ Finset.range (2 * m + 1), ∀ ξ η' : ℝ,
          arithmeticCorrelation (((8 * m : ℕ) : ℝ) ^ rho) ξ η'
              (Finset.Ioc ((8 * m) / 2) (8 * m))
              (centralTargetNat m i) ≤
            CH * (((8 * m : ℕ) : ℝ) / 2) *
              finiteSieveProduct (centralTargetNat m i) ((8 * m) / 2) *
              goodBadProduct (((8 * m : ℕ) : ℝ) ^ rho) ξ η'
                (centralTargetNat m i) ((8 * m) / 2)) →
        (∀ n ∈ blockCarrier (8 * m),
          exactUnstarredActiveSourceMass
            ⌊(((8 * m : ℕ) : ℝ) ^ rho) ^ 2⌋₊
            (8 * m) n
            (((8 * m : ℕ) : ℝ) /
              (((8 * m : ℕ) : ℝ) ^ rho) ^ 4)
            b e.val ≤ A) →
        (∀ i ∈ Finset.range (2 * m + 1),
          (2 * A) * arithmeticFactor (centralTargetNat m i) *
              centeredCorrectionDimensionlessCoefficient
                CE CB D c CH rho < (1 : ℝ) / 2048) →
        0 < centralBlockSourceTargetSum m ∧
          ∃ i ∈ Finset.range (2 * m + 1),
            0 < (GoldbachCircleMethodActualResidualExactDecompositionV18225.canonicalBlockSourceAt
              (8 * m) ((centralTargetNat m i : ℕ) : ℤ)).re := by
  obtain ⟨CE, hCE, CB, hCB, hbridge⟩ :=
    conditional_eventual_positive_central_von_mangoldt_source
  refine ⟨CE, hCE, CB, hCB, ?_⟩
  intro D c CH hD hCH hweighted hharmonic rho hrho hrhoUpper C hC hV
  obtain ⟨m₁, hcore⟩ :=
    hbridge D c CH hD hCH hweighted hharmonic rho hrho hrhoUpper C hC hV
  let m₀ := max m₁ 1
  refine ⟨m₀, ?_⟩
  intro m hm K hKinst b A hb hb1 hA e hK hH hcorrelation hsource hsmall
  have hm₁ : m₁ ≤ m := (le_max_left m₁ 1).trans hm
  have hm1 : 1 ≤ m := (le_max_right m₁ 1).trans hm
  apply hcore m hm₁ b (2 * A) hb hb1 (mul_nonneg (by norm_num) hA)
    e hK hcorrelation
  · intro n hn
    exact active_mass_le_twice_exact_unstarred_source
      ⌊(((8 * m : ℕ) : ℝ) ^ rho) ^ 2⌋₊ (8 * m) n
      (by omega) hn hH b e.val (hsource n hn)
  · exact hsmall

end GoldbachCircleMethodCentralLiteralSourceInterfaceV18414
