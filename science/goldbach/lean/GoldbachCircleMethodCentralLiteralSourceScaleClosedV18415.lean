import GoldbachCircleMethodCentralLiteralSourceInterfaceV18414
import GoldbachCircleMethodActualMultiplierScaleV18135

/-!
# Goldbach V1.8.415: central literal source scale closure

The elementary window normalization premise `1 <= B/R^4` is discharged from
the already admitted canonical scale.  The final central conditional bridge
therefore exposes only genuine analytic source assumptions, not a removable
scale side condition.

The literal character-family bound, Vaughan estimate, Mertens inputs and
correlation estimate remain premises.  The conclusion remains at the literal
von-Mangoldt source layer and `proof_status = NO_PROOF`.
-/

set_option autoImplicit false

open scoped BigOperators Classical ArithmeticFunction

namespace GoldbachCircleMethodCentralLiteralSourceScaleClosedV18415

open GoldbachCircleMethodActualMultiplierScaleV18135
open GoldbachCircleMethodActiveCharacterRadicalErrorV18158
open GoldbachCircleMethodActiveExceptionalCenteringV18129
open GoldbachCircleMethodBadPrimeProductComparisonV18165
open GoldbachCircleMethodBlockPairCarrierV18227
open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodCanonicalCentralAdjustedPositiveV18403
open GoldbachCircleMethodCanonicalCentralSourceTransferV18404
open GoldbachCircleMethodCentralLiteralSourceInterfaceV18414
open GoldbachCircleMethodCenteredDimensionlessBudgetV18411
open GoldbachCircleMethodDirectLambdaRadicalDominationV18178
open GoldbachCircleMethodDisjointPrimeFactorCompositionV18171
open GoldbachCircleMethodFiniteCompanionBindingV18118
open GoldbachCircleMethodGlobalSieveFiniteFactorV18173
open GoldbachCircleMethodLogCutoffPresieveBindingV18120
open GoldbachCircleMethodMertensUniformConstantsV18168
open GoldbachCircleMethodRadicalCorrelationTransferV18161
open GoldbachCircleMethodRealApproximationMinorAdapterV1873
open GoldbachCircleMethodResidualScaleAdmissionV18196
open GoldbachCircleMethodStructurallyAdmissibleActiveSlotV18258

/-- The canonical scale already makes the literal source normalization window
at least one.  This is elementary scale algebra, not an analytic hypothesis. -/
theorem admitted_canonical_window_scale_one
    (rho : ℝ) (hrho : 0 < rho)
    (hrhoUpper : rho ≤ (1 : ℝ) / 10000)
    (B : ℕ) (hB : blockThreshold rho ≤ B) :
    1 ≤ (B : ℝ) / ((B : ℝ) ^ rho) ^ 4 := by
  obtain ⟨hB6, hR2, _hlower, hupper⟩ :=
    actual_scale_admission rho hrho hrhoUpper B hB
  have hB1 : (1 : ℝ) ≤ B := by exact_mod_cast (show 1 ≤ B by omega)
  have hR1 : (1 : ℝ) ≤ (B : ℝ) ^ rho := by linarith
  have hscale6 : ((B : ℝ) ^ rho) ^ 6 ≤ (B : ℝ) :=
    (upper_scale_window_and_gap (B : ℝ) ((B : ℝ) ^ rho)
      hB1 hR2 hupper).1
  have hscale4 : ((B : ℝ) ^ rho) ^ 4 ≤ (B : ℝ) :=
    (pow_le_pow_right₀ hR1 (by norm_num : 4 ≤ 6)).trans hscale6
  exact (one_le_div (pow_pos (Real.rpow_pos_of_pos (by positivity) rho) 4)).2 hscale4

/-- V1.8.414 with the window-scale premise removed by V1.8.196 and V1.8.135. -/
theorem conditional_eventual_positive_central_source_of_literal_family_bound_scale_closed :
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
        (∀ i ∈ Finset.range (2 * m + 1), ∀ ξ eta' : ℝ,
          arithmeticCorrelation (((8 * m : ℕ) : ℝ) ^ rho) ξ eta'
              (Finset.Ioc ((8 * m) / 2) (8 * m))
              (centralTargetNat m i) ≤
            CH * (((8 * m : ℕ) : ℝ) / 2) *
              finiteSieveProduct (centralTargetNat m i) ((8 * m) / 2) *
              goodBadProduct (((8 * m : ℕ) : ℝ) ^ rho) ξ eta'
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
    conditional_eventual_positive_central_source_of_literal_family_bound
  refine ⟨CE, hCE, CB, hCB, ?_⟩
  intro D c CH hD hCH hweighted hharmonic rho hrho hrhoUpper C hC hV
  obtain ⟨m₁, hcore⟩ :=
    hbridge D c CH hD hCH hweighted hharmonic rho hrho hrhoUpper C hC hV
  let m₀ := max m₁ (blockThreshold rho)
  refine ⟨m₀, ?_⟩
  intro m hm K hKinst b A hb hb1 hA e hK hcorrelation hsource hsmall
  have hm₁ : m₁ ≤ m := (le_max_left m₁ (blockThreshold rho)).trans hm
  have hthreshold_m : blockThreshold rho ≤ m :=
    (le_max_right m₁ (blockThreshold rho)).trans hm
  have hthreshold_B : blockThreshold rho ≤ 8 * m := by omega
  exact hcore m hm₁ b A hb hb1 hA e hK
    (admitted_canonical_window_scale_one rho hrho hrhoUpper (8 * m) hthreshold_B)
    hcorrelation hsource hsmall

end GoldbachCircleMethodCentralLiteralSourceScaleClosedV18415
