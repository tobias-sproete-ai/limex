import GoldbachCircleMethodExactHenriotCarrierBridgesV18176

set_option autoImplicit false
open scoped BigOperators Classical
open GoldbachCircleMethodBadPrimeProductComparisonV18165
open GoldbachCircleMethodMertensUniformConstantsV18168
open GoldbachCircleMethodBadPrimeUniformFrequencyV18169
open GoldbachCircleMethodGlobalSieveFiniteFactorV18173
open GoldbachCircleMethodMertensProductFromHarmonicV18174
open GoldbachCircleMethodConditionalSieveCorrelationCompositionV18175
open GoldbachCircleMethodDisjointPrimeFactorCompositionV18171
open GoldbachCircleMethodBumpDecayRadicalEnvelopeV18155
open GoldbachCircleMethodRadicalCorrelationTransferV18161
namespace GoldbachCircleMethodActualHalfScaleCorrelationV18177

/-- Natural halving costs at most a factor two in the logarithm once `M >= 16`.
The proof explicitly covers odd `M`. -/
theorem half_cutoff_log_lower_bound {M : ℕ} (hM : 16 ≤ M) :
    Real.log (M : ℝ) / 2 ≤ Real.log ((M / 2 : ℕ) : ℝ) := by
  have hK4 : 4 ≤ M / 2 := by omega
  have hlinear : M ≤ 4 * (M / 2) := by omega
  have hsqNat : M ≤ (M / 2)^2 := by nlinarith
  have hMpos : (0 : ℝ) < M := by positivity
  have hsqReal : (M : ℝ) ≤ (((M / 2 : ℕ) : ℝ))^2 := by exact_mod_cast hsqNat
  have hlog := Real.log_le_log hMpos hsqReal
  rw [Real.log_pow] at hlog
  nlinarith

/-- Doubling the source scale costs at most a factor two in the logarithm. -/
theorem double_window_log_upper_bound {M : ℕ} (hM : 16 ≤ M) :
    Real.log ((2 * M : ℕ) : ℝ) ≤ 2 * Real.log (M : ℝ) := by
  have hMpos : (0 : ℝ) < M := by positivity
  have hsqNat : 2 * M ≤ M^2 := by nlinarith
  have hsqReal : ((2 * M : ℕ) : ℝ) ≤ (M : ℝ)^2 := by exact_mod_cast hsqNat
  have hlog := Real.log_le_log (by positivity : (0 : ℝ) < ((2 * M : ℕ) : ℝ)) hsqReal
  simpa [Real.log_pow] using hlog

/-- The exact logarithmic quotient appearing after the V175 specialization
costs at most `64` relative to the target half-scale quotient. -/
theorem half_scale_log_fraction_bound {M : ℕ} (hM : 16 ≤ M)
    {R : ℝ} (hR : 1 < R) :
    (Real.log R)^2 / (Real.log ((M / 2 : ℕ) : ℝ))^2 *
        (Real.log ((2 * M : ℕ) : ℝ) / Real.log R)^4 ≤
      64 * (Real.log (M : ℝ) / Real.log R)^2 := by
  have hLMpos : 0 < Real.log (M : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < M by omega))
  have hLKpos : 0 < Real.log ((M / 2 : ℕ) : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < M / 2 by omega))
  have hLRpos : 0 < Real.log R := Real.log_pos hR
  have hLX0 : 0 ≤ Real.log ((2 * M : ℕ) : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ 2 * M by omega))
  have hK := half_cutoff_log_lower_bound hM
  have hX := double_window_log_upper_bound hM
  have hKpow := pow_le_pow_left₀ (by positivity : 0 ≤ Real.log (M : ℝ) / 2) hK 2
  have hLsq : (Real.log (M : ℝ))^2 ≤
      4 * (Real.log ((M / 2 : ℕ) : ℝ))^2 := by
    nlinarith
  have hXpow := pow_le_pow_left₀ hLX0 hX 4
  have hLmul := mul_le_mul_of_nonneg_right hLsq (sq_nonneg (Real.log (M : ℝ)))
  have hnum : (Real.log ((2 * M : ℕ) : ℝ))^4 ≤
      64 * (Real.log ((M / 2 : ℕ) : ℝ))^2 *
        (Real.log (M : ℝ))^2 := by
    calc
      (Real.log ((2 * M : ℕ) : ℝ))^4 ≤
          (2 * Real.log (M : ℝ))^4 := hXpow
      _ = 16 * (Real.log (M : ℝ))^4 := by ring
      _ ≤ 64 * (Real.log ((M / 2 : ℕ) : ℝ))^2 *
          (Real.log (M : ℝ))^2 := by nlinarith
  have hden : 0 < (Real.log ((M / 2 : ℕ) : ℝ))^2 * (Real.log R)^2 := by
    positivity
  calc
    (Real.log R)^2 / (Real.log ((M / 2 : ℕ) : ℝ))^2 *
        (Real.log ((2 * M : ℕ) : ℝ) / Real.log R)^4 =
      (Real.log ((2 * M : ℕ) : ℝ))^4 /
        ((Real.log ((M / 2 : ℕ) : ℝ))^2 * (Real.log R)^2) := by
          field_simp [ne_of_gt hLKpos, ne_of_gt hLRpos]
    _ ≤ (64 * (Real.log ((M / 2 : ℕ) : ℝ))^2 *
        (Real.log (M : ℝ))^2) /
        ((Real.log ((M / 2 : ℕ) : ℝ))^2 * (Real.log R)^2) :=
      (div_le_div_iff_of_pos_right hden).2 hnum
    _ = 64 * (Real.log (M : ℝ) / Real.log R)^2 := by
      field_simp [ne_of_gt hLKpos, ne_of_gt hLRpos]

/-- V175 specialized to the actual half-window and half-scale source input.
The Henriot-style source inequality and both V168 remainder families remain
explicit hypotheses. -/
theorem actual_half_scale_correlation_bound
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
    (∑ n ∈ Finset.Ioc (M / 2) M,
      radicalMajorant R n * radicalMajorant R (m - n)) ≤
      128 * CH * (mertensProductConstant D c)^2 *
        (oneFrequencyConstant D c)^2 *
        (∫ ξ : ℝ, secondMomentDecay ξ)^2 * (M : ℝ) *
        arithmeticFactor m * (Real.log (M : ℝ) / Real.log R)^2 := by
  have hm : 0 < m := by omega
  have hmX : m ≤ 2 * M := by omega
  have hK : 2 ≤ M / 2 := by omega
  have hKX : M / 2 ≤ 2 * M := by omega
  have hX : 2 ≤ 2 * M := by omega
  have hbase := conditional_sieve_correlation_transfers
    D c CH ((M : ℝ) / 2) hD hCH (by positivity)
    hweighted hharmonic hm hK hKX hmX hX hR hRX
    (Finset.Ioc (M / 2) M) hsource
  have hratio := half_scale_log_fraction_bound hM hR
  have hA : 0 ≤ arithmeticFactor m := arithmeticFactor_nonneg m
  have hcommon : 0 ≤
      2 * CH * (M : ℝ) * (mertensProductConstant D c)^2 *
        (oneFrequencyConstant D c)^2 * arithmeticFactor m *
        (∫ ξ : ℝ, secondMomentDecay ξ)^2 := by
    positivity
  have hscaled := mul_le_mul_of_nonneg_left hratio hcommon
  calc
    (∑ n ∈ Finset.Ioc (M / 2) M,
        radicalMajorant R n * radicalMajorant R (m - n)) ≤
      (Real.log R)^2 *
        conditionalCorrelationCoefficient D c CH ((M : ℝ) / 2)
          m (M / 2) (2 * M) R *
        (∫ ξ : ℝ, secondMomentDecay ξ)^2 := hbase
    _ = (2 * CH * (M : ℝ) * (mertensProductConstant D c)^2 *
          (oneFrequencyConstant D c)^2 * arithmeticFactor m *
          (∫ ξ : ℝ, secondMomentDecay ξ)^2) *
        ((Real.log R)^2 / (Real.log ((M / 2 : ℕ) : ℝ))^2 *
          (Real.log ((2 * M : ℕ) : ℝ) / Real.log R)^4) := by
      unfold conditionalCorrelationCoefficient
      ring
    _ ≤ (2 * CH * (M : ℝ) * (mertensProductConstant D c)^2 *
          (oneFrequencyConstant D c)^2 * arithmeticFactor m *
          (∫ ξ : ℝ, secondMomentDecay ξ)^2) *
        (64 * (Real.log (M : ℝ) / Real.log R)^2) := hscaled
    _ = 128 * CH * (mertensProductConstant D c)^2 *
        (oneFrequencyConstant D c)^2 *
        (∫ ξ : ℝ, secondMomentDecay ξ)^2 * (M : ℝ) *
        arithmeticFactor m * (Real.log (M : ℝ) / Real.log R)^2 := by ring

end GoldbachCircleMethodActualHalfScaleCorrelationV18177
