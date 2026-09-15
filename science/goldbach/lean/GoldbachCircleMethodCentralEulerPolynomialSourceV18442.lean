import GoldbachCircleMethodCentralEulerMeanAbsorptionV18441
import GoldbachCircleMethodCanonicalCentralSingleObstructionV18410
import GoldbachCircleMethodCentralCorrectionMeanMajorantV18425
import GoldbachCircleMethodCentralLiteralSourceInterfaceV18414
import GoldbachCircleMethodCentralLiteralSourceScaleClosedV18415
import GoldbachCircleMethodCentralSourceExponentAbsorptionV18420

/-!
# Goldbach V1.8.442: Euler-mean central bridge from polynomial source decay

The unconditional arithmetic mean from V1.8.440 is combined with the exact
correction majorant and central single-obstruction theorem.  Any fixed positive
polynomial decay of the literal active source mass now absorbs the arithmetic
correction without a targetwise divisor-envelope loss.

The polynomial source estimate, arithmetic-correlation bound, Mertens inputs,
and named Vaughan estimate remain explicit analytic premises.  The conclusion
is a positive von-Mangoldt source witness, not pointwise Goldbach.  Therefore
`proof_status = NO_PROOF` remains mandatory.
-/

set_option autoImplicit false

open scoped BigOperators Classical ArithmeticFunction Topology
open Filter

namespace GoldbachCircleMethodCentralEulerPolynomialSourceV18442

open GoldbachCircleMethodActiveExceptionalCenteringV18129
open GoldbachCircleMethodActiveCharacterRadicalErrorV18158
open GoldbachCircleMethodArithmeticEulerKernelBoundV18439
open GoldbachCircleMethodArithmeticPrefixMeanClosedV18440
open GoldbachCircleMethodBadPrimeProductComparisonV18165
open GoldbachCircleMethodBlockPairCarrierV18227
open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodCanonicalCentralAdjustedPositiveV18403
open GoldbachCircleMethodCanonicalCentralSingleObstructionV18410
open GoldbachCircleMethodCanonicalCentralSourceTransferV18404
open GoldbachCircleMethodCentralCorrectionMeanMajorantV18425
open GoldbachCircleMethodCentralArithmeticMeanBudgetV18424
open GoldbachCircleMethodCentralDivisorEnvelopeV18417
open GoldbachCircleMethodCentralEulerMeanAbsorptionV18441
open GoldbachCircleMethodCentralLiteralSourceInterfaceV18414
open GoldbachCircleMethodCentralLiteralSourceScaleClosedV18415
open GoldbachCircleMethodCentralSourceExponentAbsorptionV18420
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

/-- A fixed polynomial source decay absorbs the now-unconditional arithmetic
Euler mean.  No numerical upper bound for `eulerKernelConstant` is needed. -/
theorem source_power_decay_absorbs_euler_mean
    (CA Gamma sigma : ℝ)
    (hCA : 0 ≤ CA) (hGamma : 0 ≤ Gamma) (hsigma : 0 < sigma) :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m →
      (2 * (CA * ((14 * m : ℕ) : ℝ) ^ (-sigma))) * Gamma *
          (4 * (eulerKernelConstant + 1)) <
        (1 : ℝ) / 768 := by
  let K : ℝ := 2 * CA * Gamma * (4 * (eulerKernelConstant + 1))
  have hEuler : 0 ≤ eulerKernelConstant + 1 := eulerMean_nonneg
  have hK : 0 ≤ K := by
    dsimp [K]
    positivity
  have hdecay : Tendsto
      (fun m : ℕ => ((14 * m : ℕ) : ℝ) ^ (-sigma))
      atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop hsigma).comp tendsto_fourteen_mul_natCast_atTop
  have hlim : Tendsto
      (fun m : ℕ => K * ((14 * m : ℕ) : ℝ) ^ (-sigma))
      atTop (nhds 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul hdecay
  have hsmall : ∀ᶠ m : ℕ in atTop,
      K * ((14 * m : ℕ) : ℝ) ^ (-sigma) < (1 : ℝ) / 768 :=
    (tendsto_order.1 hlim).2 ((1 : ℝ) / 768) (by norm_num)
  apply eventually_atTop.mp
  filter_upwards [hsmall] with m hm
  have hrewrite :
      (2 * (CA * ((14 * m : ℕ) : ℝ) ^ (-sigma))) * Gamma *
          (4 * (eulerKernelConstant + 1)) =
        K * ((14 * m : ℕ) : ℝ) ^ (-sigma) := by
    dsimp [K]
    ring
  rw [hrewrite]
  exact hm

/-- Fully composed central source bridge with the arithmetic mean discharged.
Only genuine analytic source-side premises remain exposed. -/
theorem conditional_eventual_positive_central_source_of_polynomial_decay_euler_mean :
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
        (sigma CA : ℝ) (_hsigma : 0 < sigma) (_hCA : 0 ≤ CA),
      ∃ m₀ : ℕ, ∀ (m : ℕ), m₀ ≤ m →
        ∀ {K : ℕ} [NeZero K],
        ∀ b : ℝ, 0 ≤ b → b ≤ 1 →
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
            b e.val ≤
              CA * ((14 * m : ℕ) : ℝ) ^ (-sigma)) →
        0 < centralBlockSourceTargetSum m ∧
          ∃ i ∈ Finset.range (2 * m + 1),
            0 < (GoldbachCircleMethodActualResidualExactDecompositionV18225.canonicalBlockSourceAt
              (8 * m) ((centralTargetNat m i : ℕ) : ℤ)).re := by
  obtain ⟨CE, hCE, CB, hCB, hcorrectionCore⟩ :=
    eventual_central_adjusted_centered_error_le_mean_budget
  refine ⟨CE, hCE, CB, hCB, ?_⟩
  intro D c CH hD hCH hweighted hharmonic rho hrho hrhoUpper CV hCV hV
    sigma CA hsigma hCA
  obtain ⟨B₀, hcorrectionBound⟩ :=
    hcorrectionCore D c CH hD hCH hweighted hharmonic rho hrho
      (hrhoUpper.trans (by norm_num : (1 : ℝ) / 10000 ≤ 1))
  obtain ⟨m₁, hpositive⟩ :=
    eventual_central_source_positive_of_centered_error_bound
      CV rho hCV hV hrho hrhoUpper
  have hGamma : 0 ≤ centeredCorrectionDimensionlessCoefficient
      CE CB D c CH rho :=
    centeredCorrectionDimensionlessCoefficient_nonneg CE CB D c CH rho
      hCE hCB hCH hrho
  obtain ⟨m₂, hscalar⟩ := source_power_decay_absorbs_euler_mean
    CA (centeredCorrectionDimensionlessCoefficient CE CB D c CH rho)
      sigma hCA hGamma hsigma
  let m₀ := max (max (max m₁ m₂) B₀) (max (blockThreshold rho) 1)
  refine ⟨m₀, ?_⟩
  intro m hm K hKinst b hb hb1 e hK hcorrelation hsource
  have hm₁ : m₁ ≤ m :=
    (le_max_left m₁ m₂).trans
      ((le_max_left (max m₁ m₂) B₀).trans
        ((le_max_left (max (max m₁ m₂) B₀) (max (blockThreshold rho) 1)).trans hm))
  have hm₂ : m₂ ≤ m :=
    (le_max_right m₁ m₂).trans
      ((le_max_left (max m₁ m₂) B₀).trans
        ((le_max_left (max (max m₁ m₂) B₀) (max (blockThreshold rho) 1)).trans hm))
  have hB₀m : B₀ ≤ m :=
    (le_max_right (max m₁ m₂) B₀).trans
      ((le_max_left (max (max m₁ m₂) B₀) (max (blockThreshold rho) 1)).trans hm)
  have hthreshold : blockThreshold rho ≤ m :=
    (le_max_left (blockThreshold rho) 1).trans
      ((le_max_right (max (max m₁ m₂) B₀) (max (blockThreshold rho) 1)).trans hm)
  have hmOne : 1 ≤ m :=
    (le_max_right (blockThreshold rho) 1).trans
      ((le_max_right (max (max m₁ m₂) B₀) (max (blockThreshold rho) 1)).trans hm)
  let A : ℝ := CA * ((14 * m : ℕ) : ℝ) ^ (-sigma)
  let eta : ℝ := 2 * A
  have hA : 0 ≤ A := by
    dsimp [A]
    positivity
  have heta : 0 ≤ eta := by
    dsimp [eta]
    positivity
  have hwindow :
      1 ≤ (((8 * m : ℕ) : ℝ) /
        (((8 * m : ℕ) : ℝ) ^ rho) ^ 4) :=
    admitted_canonical_window_scale_one rho hrho hrhoUpper (8 * m) (by omega)
  have hmass : ∀ n ∈ blockCarrier (8 * m),
      activeFluctuationMass ⌊(((8 * m : ℕ) : ℝ) ^ rho) ^ 2⌋₊
        (8 * m) n
        (((8 * m : ℕ) : ℝ) /
          (((8 * m : ℕ) : ℝ) ^ rho) ^ 4)
        b (blockInput (8 * m)) e.val ≤ eta := by
    intro n hn
    have hs := active_mass_le_twice_exact_unstarred_source
      ⌊(((8 * m : ℕ) : ℝ) ^ rho) ^ 2⌋₊ (8 * m) n
      (by omega) hn hwindow b e.val (hsource n hn)
    simpa only [eta, A] using hs
  have hcorrection :
      |centralAdjustedCenteredErrorTargetSum m rho b e| ≤
        centralAdjustedCenteredBudgetSum CE CB D c CH rho eta m :=
    hcorrectionBound m hmOne b eta e (by omega) hb heta hcorrelation hmass
  have hscalar' :
      eta * centeredCorrectionDimensionlessCoefficient CE CB D c CH rho *
          (4 * (eulerKernelConstant + 1)) < (1 : ℝ) / 768 := by
    simpa only [eta, A] using hscalar m hm₂
  have hCentered :
      |centralAdjustedCenteredErrorTargetSum m rho b e| <
        ((8 * m : ℕ) : ℝ) ^ 2 / 2048 :=
    central_adjusted_centered_error_lt_of_euler_mean
      CE CB D c CH rho b eta m hmOne e heta hGamma hcorrection hscalar'
  exact hpositive m hm₁ b hb hb1 e hK hCentered

end GoldbachCircleMethodCentralEulerPolynomialSourceV18442
