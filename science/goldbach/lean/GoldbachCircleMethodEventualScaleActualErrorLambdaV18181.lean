import GoldbachCircleMethodFixedRhoPolynomialLossV18180
import GoldbachCircleMethodActiveCharacterRadicalErrorV18158

set_option autoImplicit false
open scoped BigOperators Classical ArithmeticFunction ContDiff Topology
open Filter
open GoldbachCircleMethodLogCutoffPresieveBindingV18120
open GoldbachCircleMethodActiveExceptionalCenteringV18129
open GoldbachCircleMethodBumpDecayRadicalEnvelopeV18155
open GoldbachCircleMethodActiveCharacterRadicalErrorV18158
open GoldbachCircleMethodRadicalCorrelationTransferV18161
open GoldbachCircleMethodBadPrimeProductComparisonV18165
open GoldbachCircleMethodMertensUniformConstantsV18168
open GoldbachCircleMethodBadPrimeUniformFrequencyV18169
open GoldbachCircleMethodGlobalSieveFiniteFactorV18173
open GoldbachCircleMethodMertensProductFromHarmonicV18174
open GoldbachCircleMethodDisjointPrimeFactorCompositionV18171
open GoldbachCircleMethodDirectLambdaRadicalDominationV18178
open GoldbachCircleMethodFixedRhoPolynomialLossV18180
namespace GoldbachCircleMethodEventualScaleActualErrorLambdaV18181

/-- For every fixed positive `rho`, the actual power scale is eventually at
least two, while the same threshold also supplies the finite lower bound on
`M` used by V180.  No effective numerical threshold is extracted. -/
theorem fixedRho_eventual_scale_two {rho : ℝ} (hrho : 0 < rho) :
    ∃ M₀ : ℕ, ∀ M ≥ M₀, 16 ≤ M ∧ 2 ≤ (M : ℝ)^rho := by
  have hpow : Tendsto (fun M : ℕ => (M : ℝ)^rho) atTop atTop :=
    (tendsto_rpow_atTop hrho).comp tendsto_natCast_atTop_atTop
  apply eventually_atTop.mp
  filter_upwards [eventually_ge_atTop (16 : ℕ),
      hpow.eventually (eventually_ge_atTop (2 : ℝ))] with M hM hR
  exact ⟨hM,hR⟩

/-- The literal V158 adjusted error and active exceptional mass, composed with
the exact V180 half-scale von-Mangoldt companion bound.  The mass estimate and
all analytic source predicates remain explicit hypotheses. -/
theorem eventual_actual_adjusted_error_lambda_power_bound {G : ℝ → ℝ}
    (hc : HasCompactSupport G) (hd : ContDiff ℝ ∞ G)
    (hG : ∀ t : ℝ, 2 < t → G t = 0) :
    ∃ CG : ℝ, 0 ≤ CG ∧
      ∀ (D c CH : ℝ) (_hD : 0 ≤ D) (_hCH : 0 ≤ CH)
        (_hweighted : ∀ (X : ℕ), 2 ≤ X → ∀ t : ℝ, 2 ≤ t → t ≤ (X : ℝ) →
          |prefixLogMoment X t - Real.log t| ≤ D)
        (_hharmonic : ∀ (X : ℕ), 2 ≤ X → ∀ t : ℝ, 2 ≤ t → t ≤ (X : ℝ) →
          |prefixHarmonicMoment X t - Real.log (Real.log t) - c| ≤ D / Real.log t)
        (rho : ℝ) (_hrho : 0 < rho) (_hrho1 : rho ≤ 1),
      ∃ M₀ : ℕ,
      ∀ {M m B : ℕ} (H b eta : ℝ) (f : ℕ → ℂ)
        (e : CharacterSlot ⌊((M : ℝ)^rho)^2⌋₊),
        M₀ ≤ M → 5 * M ≤ 4 * m → 4 * m ≤ 7 * M → 0 ≤ eta →
        (∀ ξ η : ℝ,
          arithmeticCorrelation ((M : ℝ)^rho) ξ η (Finset.Ioc (M / 2) M) m ≤
            CH * ((M : ℝ) / 2) * finiteSieveProduct m (M / 2) *
              goodBadProduct ((M : ℝ)^rho) ξ η m (M / 2)) →
        (∀ n ∈ Finset.Ioc (M / 2) M,
          activeFluctuationMass ⌊((M : ℝ)^rho)^2⌋₊ B n H b f e ≤ eta) →
        (∑ n ∈ Finset.Ioc (M / 2) M,
          ‖adjustedCenteredError ⌊((M : ℝ)^rho)^2⌋₊ B n H b f
              (logWeight ((M : ℝ)^rho) G) e‖ * Λ (m - n)) ≤
          CG * eta *
            ((128 * CH * (mertensProductConstant D c)^2 *
                (oneFrequencyConstant D c)^2 *
                (∫ ξ : ℝ, secondMomentDecay ξ)^2 / tenthDecayMass) *
              (M : ℝ) * arithmeticFactor m / rho^3) := by
  obtain ⟨CG,hCG,herror⟩ := actual_adjusted_error_radical_bound hc hd hG
  refine ⟨CG,hCG,?_⟩
  intro D c CH hD hCH hweighted hharmonic rho hrho hrho1
  obtain ⟨M₀,hscale⟩ := fixedRho_eventual_scale_two hrho
  refine ⟨M₀,?_⟩
  intro M m B H b eta f e hM₀ hmlower hmupper heta hsource hmass
  have hs := hscale M hM₀
  have hRone : 1 < (M : ℝ)^rho :=
    (fixedRho_scale_admission hs.1 hrho hrho1).1
  have hcomp := actual_half_scale_lambda_power_bound D c CH hD hCH
    hweighted hharmonic hs.1 hmlower hmupper hrho hrho1 hsource
  have hpoint (n : ℕ) (hn : n ∈ Finset.Ioc (M / 2) M) :
      ‖adjustedCenteredError ⌊((M : ℝ)^rho)^2⌋₊ B n H b f
          (logWeight ((M : ℝ)^rho) G) e‖ * Λ (m - n) ≤
        (CG * eta) * (radicalMajorant ((M : ℝ)^rho) n * Λ (m - n)) := by
    have hnpos : 0 < n := by
      simp only [Finset.mem_Ioc] at hn
      omega
    have herr := herror ((M : ℝ)^rho) hs.2 B n hnpos H b f e
    have hrad : 0 ≤ radicalMajorant ((M : ℝ)^rho) n :=
      radicalMajorant_nonneg hRone n
    calc
      _ ≤ (CG * radicalMajorant ((M : ℝ)^rho) n *
          activeFluctuationMass ⌊((M : ℝ)^rho)^2⌋₊ B n H b f e) * Λ (m - n) :=
        mul_le_mul_of_nonneg_right herr ArithmeticFunction.vonMangoldt_nonneg
      _ ≤ (CG * radicalMajorant ((M : ℝ)^rho) n * eta) * Λ (m - n) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hmass n hn) (mul_nonneg hCG hrad))
          ArithmeticFunction.vonMangoldt_nonneg
      _ = (CG * eta) * (radicalMajorant ((M : ℝ)^rho) n * Λ (m - n)) := by
        ring
  calc
    _ ≤ ∑ n ∈ Finset.Ioc (M / 2) M,
        (CG * eta) * (radicalMajorant ((M : ℝ)^rho) n * Λ (m - n)) :=
      Finset.sum_le_sum (fun n hn => hpoint n hn)
    _ = (CG * eta) * (∑ n ∈ Finset.Ioc (M / 2) M,
        radicalMajorant ((M : ℝ)^rho) n * Λ (m - n)) := by
      rw [Finset.mul_sum]
    _ ≤ CG * eta *
        ((128 * CH * (mertensProductConstant D c)^2 *
            (oneFrequencyConstant D c)^2 *
            (∫ ξ : ℝ, secondMomentDecay ξ)^2 / tenthDecayMass) *
          (M : ℝ) * arithmeticFactor m / rho^3) :=
      mul_le_mul_of_nonneg_left hcomp (mul_nonneg hCG heta)

end GoldbachCircleMethodEventualScaleActualErrorLambdaV18181
