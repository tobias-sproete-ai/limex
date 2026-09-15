import GoldbachCircleMethodDirectHalfScaleLambdaCompositionV18179
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

set_option autoImplicit false
open scoped BigOperators Classical ArithmeticFunction Topology
open Filter
open GoldbachCircleMethodBumpDecayRadicalEnvelopeV18155
open GoldbachCircleMethodRadicalCorrelationTransferV18161
open GoldbachCircleMethodBadPrimeProductComparisonV18165
open GoldbachCircleMethodMertensUniformConstantsV18168
open GoldbachCircleMethodBadPrimeUniformFrequencyV18169
open GoldbachCircleMethodGlobalSieveFiniteFactorV18173
open GoldbachCircleMethodMertensProductFromHarmonicV18174
open GoldbachCircleMethodDisjointPrimeFactorCompositionV18171
open GoldbachCircleMethodDirectLambdaRadicalDominationV18178
open GoldbachCircleMethodDirectHalfScaleLambdaCompositionV18179
namespace GoldbachCircleMethodFixedRhoPolynomialLossV18180

/-- The actual power scale is admitted by the unchanged V179 range. -/
theorem fixedRho_scale_admission {M : ℕ} (hM : 16 ≤ M) {rho : ℝ}
    (hrho : 0 < rho) (hrho1 : rho ≤ 1) :
    1 < (M : ℝ)^rho ∧ (M : ℝ)^rho ≤ ((2 * M : ℕ) : ℝ) :=
  power_cutoff_bounds (by omega) hrho hrho1

/-- The logarithmic quotient is derived from `Real.log_rpow`, not supplied as
a normalization hypothesis. -/
theorem fixedRho_log_ratio {M : ℕ} (hM : 16 ≤ M) {rho : ℝ}
    (hrho : 0 < rho) :
    Real.log (M : ℝ) / Real.log ((M : ℝ)^rho) = 1 / rho := by
  have hMpos : (0 : ℝ) < M := by positivity
  have hlogM : Real.log (M : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast (show 1 < M by omega))).ne'
  rw [Real.log_rpow hMpos]
  field_simp [hrho.ne',hlogM]

/-- V179 at the genuine scale `R=M^rho`.  The exact same source predicates and
half-window remain in the theorem statement. -/
theorem actual_half_scale_lambda_power_bound
    (D c CH : ℝ) (hD : 0 ≤ D) (hCH : 0 ≤ CH)
    (hweighted : ∀ (X : ℕ), 2 ≤ X → ∀ t : ℝ, 2 ≤ t → t ≤ (X : ℝ) →
      |prefixLogMoment X t - Real.log t| ≤ D)
    (hharmonic : ∀ (X : ℕ), 2 ≤ X → ∀ t : ℝ, 2 ≤ t → t ≤ (X : ℝ) →
      |prefixHarmonicMoment X t - Real.log (Real.log t) - c| ≤ D / Real.log t)
    {M m : ℕ} (hM : 16 ≤ M) (hmlower : 5 * M ≤ 4 * m)
    (hmupper : 4 * m ≤ 7 * M)
    {rho : ℝ} (hrho : 0 < rho) (hrho1 : rho ≤ 1)
    (hsource : ∀ ξ η : ℝ,
      arithmeticCorrelation ((M : ℝ)^rho) ξ η (Finset.Ioc (M / 2) M) m ≤
        CH * ((M : ℝ) / 2) * finiteSieveProduct m (M / 2) *
          goodBadProduct ((M : ℝ)^rho) ξ η m (M / 2)) :
    (∑ n ∈ Finset.Ioc (M / 2) M,
      radicalMajorant ((M : ℝ)^rho) n * Λ (m - n)) ≤
      (128 * CH * (mertensProductConstant D c)^2 *
          (oneFrequencyConstant D c)^2 *
          (∫ ξ : ℝ, secondMomentDecay ξ)^2 / tenthDecayMass) *
        (M : ℝ) * arithmeticFactor m / rho^3 := by
  have hscale := fixedRho_scale_admission hM hrho hrho1
  have hbase := actual_half_scale_lambda_companion_bound D c CH hD hCH
    hweighted hharmonic hM hmlower hmupper hscale.1 hscale.2 hsource
  rw [fixedRho_log_ratio hM hrho] at hbase
  calc
    (∑ n ∈ Finset.Ioc (M / 2) M,
      radicalMajorant ((M : ℝ)^rho) n * Λ (m - n)) ≤
        (128 * CH * (mertensProductConstant D c)^2 *
          (oneFrequencyConstant D c)^2 *
          (∫ ξ : ℝ, secondMomentDecay ξ)^2 / tenthDecayMass) *
        (M : ℝ) * arithmeticFactor m * (1 / rho)^3 := hbase
    _ = (128 * CH * (mertensProductConstant D c)^2 *
          (oneFrequencyConstant D c)^2 *
          (∫ ξ : ℝ, secondMomentDecay ξ)^2 / tenthDecayMass) *
        (M : ℝ) * arithmeticFactor m / rho^3 := by
      field_simp [hrho.ne']

/-- A fixed quartic polynomial loss is absorbed by exponential decay as the
positive scale parameter tends to zero.  This scalar lemma supplies no analytic
source estimate and no value of `rho`. -/
theorem quartic_exponential_loss_absorption (C c eps : ℝ)
    (hC : 0 ≤ C) (hc : 0 < c) (heps : 0 < eps) :
    ∃ rho : ℝ, 0 < rho ∧ rho ≤ 1 / 10000 ∧
      C * Real.exp (-c / rho) / rho^4 < eps := by
  rcases hC.eq_or_lt with rfl | hCpos
  · refine ⟨1 / 10000, by norm_num, le_rfl, ?_⟩
    simpa using heps
  · have hbase := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
        (4 : ℝ) c hc
    have hbaseNat : Tendsto (fun t : ℝ => t^4 * Real.exp (-c * t)) atTop (𝓝 0) := by
      simpa only [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num,
        Real.rpow_natCast] using hbase
    have hlim : Tendsto (fun t : ℝ => C * (t^4 * Real.exp (-c * t))) atTop (𝓝 0) := by
      simpa only [mul_zero] using tendsto_const_nhds.mul hbaseNat
    have hsmall : ∀ᶠ t : ℝ in atTop, C * (t^4 * Real.exp (-c * t)) < eps :=
      (tendsto_order.1 hlim).2 eps heps
    obtain ⟨t,ht,hlt⟩ := ((eventually_ge_atTop (10000 : ℝ)).and hsmall).exists
    have htpos : 0 < t := lt_of_lt_of_le (by norm_num) ht
    refine ⟨1 / t, one_div_pos.mpr htpos,
      one_div_le_one_div_of_le (by norm_num) ht, ?_⟩
    calc
      C * Real.exp (-c / (1 / t)) / (1 / t)^4 =
          C * (t^4 * Real.exp (-c * t)) := by
        field_simp [htpos.ne']
      _ < eps := hlt

end GoldbachCircleMethodFixedRhoPolynomialLossV18180
