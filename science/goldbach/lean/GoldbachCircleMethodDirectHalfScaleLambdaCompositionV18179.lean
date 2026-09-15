import GoldbachCircleMethodDirectLambdaRadicalDominationV18178

set_option autoImplicit false
open scoped BigOperators Classical ArithmeticFunction
open GoldbachCircleMethodBumpDecayRadicalEnvelopeV18155
open GoldbachCircleMethodRadicalCorrelationTransferV18161
open GoldbachCircleMethodBadPrimeProductComparisonV18165
open GoldbachCircleMethodMertensUniformConstantsV18168
open GoldbachCircleMethodBadPrimeUniformFrequencyV18169
open GoldbachCircleMethodGlobalSieveFiniteFactorV18173
open GoldbachCircleMethodMertensProductFromHarmonicV18174
open GoldbachCircleMethodDisjointPrimeFactorCompositionV18171
open GoldbachCircleMethodActualHalfScaleCorrelationV18177
open GoldbachCircleMethodDirectLambdaRadicalDominationV18178
namespace GoldbachCircleMethodDirectHalfScaleLambdaCompositionV18179

/-- The direct V178 von-Mangoldt companion domination composed with the exact V177
half-window correlation bound.  Both source remainder families and the uniform
frequency inequality remain explicit hypotheses. -/
theorem actual_half_scale_lambda_companion_bound
    (D c CH : ℝ) (hD : 0 ≤ D) (hCH : 0 ≤ CH)
    (hweighted : ∀ (X : ℕ), 2 ≤ X → ∀ t : ℝ, 2 ≤ t → t ≤ (X : ℝ) →
      |prefixLogMoment X t - Real.log t| ≤ D)
    (hharmonic : ∀ (X : ℕ), 2 ≤ X → ∀ t : ℝ, 2 ≤ t → t ≤ (X : ℝ) →
      |prefixHarmonicMoment X t - Real.log (Real.log t) - c| ≤ D / Real.log t)
    {M m : ℕ} (hM : 16 ≤ M) (hmlower : 5 * M ≤ 4 * m)
    (hmupper : 4 * m ≤ 7 * M)
    {R : ℝ} (hR : 1 < R) (hRX : R ≤ ((2 * M : ℕ) : ℝ))
    (hsource : ∀ ξ η : ℝ,
      arithmeticCorrelation R ξ η (Finset.Ioc (M / 2) M) m ≤
        CH * ((M : ℝ) / 2) * finiteSieveProduct m (M / 2) *
          goodBadProduct R ξ η m (M / 2)) :
    (∑ n ∈ Finset.Ioc (M / 2) M, radicalMajorant R n * Λ (m - n)) ≤
      (128 * CH * (mertensProductConstant D c)^2 *
          (oneFrequencyConstant D c)^2 *
          (∫ ξ : ℝ, secondMomentDecay ξ)^2 / tenthDecayMass) *
        (M : ℝ) * arithmeticFactor m *
          (Real.log (M : ℝ) / Real.log R)^3 := by
  have hX : 2 ≤ 2 * M := by omega
  have hmX : m ≤ 2 * M := by omega
  have hlogR : 0 < Real.log R := Real.log_pos hR
  have hJ : 0 < tenthDecayMass := tenthDecayMass_pos
  have hlogM : 0 < Real.log (M : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < M by omega))
  have hdouble := double_window_log_upper_bound hM
  have hden : 0 < 2 * Real.log R * tenthDecayMass :=
    mul_pos (mul_pos (by norm_num) hlogR) hJ
  have hcoef : Real.log ((2 * M : ℕ) : ℝ) /
        (2 * Real.log R * tenthDecayMass) ≤
      Real.log (M : ℝ) / (Real.log R * tenthDecayMass) := by
    calc
      Real.log ((2 * M : ℕ) : ℝ) /
          (2 * Real.log R * tenthDecayMass) ≤
        (2 * Real.log (M : ℝ)) /
          (2 * Real.log R * tenthDecayMass) :=
        (div_le_div_iff_of_pos_right hden).2 hdouble
      _ = Real.log (M : ℝ) / (Real.log R * tenthDecayMass) := by
        field_simp [ne_of_gt hlogR, ne_of_gt hJ]
  have hHH0 : 0 ≤ ∑ n ∈ Finset.Ioc (M / 2) M,
      radicalMajorant R n * radicalMajorant R (m - n) := by
    exact Finset.sum_nonneg (fun n _ =>
      mul_nonneg (radicalMajorant_nonneg hR n) (radicalMajorant_nonneg hR (m - n)))
  have hdirect := finite_lambda_companion_le_radical hX hmX hR hRX
    (Finset.Ioc (M / 2) M)
  have hhalf := actual_half_scale_correlation_bound D c CH hD hCH hweighted hharmonic
    hM hmlower hmupper hR hRX hsource
  have hsmallCoef : 0 ≤ Real.log (M : ℝ) /
      (Real.log R * tenthDecayMass) := by positivity
  calc
    (∑ n ∈ Finset.Ioc (M / 2) M, radicalMajorant R n * Λ (m - n)) ≤
        (Real.log ((2 * M : ℕ) : ℝ) /
          (2 * Real.log R * tenthDecayMass)) *
          (∑ n ∈ Finset.Ioc (M / 2) M,
            radicalMajorant R n * radicalMajorant R (m - n)) := hdirect
    _ ≤ (Real.log (M : ℝ) / (Real.log R * tenthDecayMass)) *
          (∑ n ∈ Finset.Ioc (M / 2) M,
            radicalMajorant R n * radicalMajorant R (m - n)) :=
      mul_le_mul_of_nonneg_right hcoef hHH0
    _ ≤ (Real.log (M : ℝ) / (Real.log R * tenthDecayMass)) *
        (128 * CH * (mertensProductConstant D c)^2 *
          (oneFrequencyConstant D c)^2 *
          (∫ ξ : ℝ, secondMomentDecay ξ)^2 * (M : ℝ) *
          arithmeticFactor m * (Real.log (M : ℝ) / Real.log R)^2) :=
      mul_le_mul_of_nonneg_left hhalf hsmallCoef
    _ = (128 * CH * (mertensProductConstant D c)^2 *
          (oneFrequencyConstant D c)^2 *
          (∫ ξ : ℝ, secondMomentDecay ξ)^2 / tenthDecayMass) *
        (M : ℝ) * arithmeticFactor m *
          (Real.log (M : ℝ) / Real.log R)^3 := by
      field_simp [ne_of_gt hlogR, ne_of_gt hJ]

end GoldbachCircleMethodDirectHalfScaleLambdaCompositionV18179
