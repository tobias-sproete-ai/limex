import GoldbachCircleMethodMertensProductFromHarmonicV18174
import GoldbachCircleMethodDisjointPrimeFactorCompositionV18171
import GoldbachCircleMethodRadicalCorrelationTransferV18161

set_option autoImplicit false
open scoped BigOperators Classical
open GoldbachCircleMethodBadPrimeProductComparisonV18165
open GoldbachCircleMethodMertensUniformConstantsV18168
open GoldbachCircleMethodBadPrimeUniformFrequencyV18169
open GoldbachCircleMethodDisjointPrimeFactorCompositionV18171
open GoldbachCircleMethodGlobalSieveFiniteFactorV18173
open GoldbachCircleMethodMertensProductFromHarmonicV18174
open GoldbachCircleMethodBumpDecayRadicalEnvelopeV18155
open GoldbachCircleMethodRadicalCorrelationTransferV18161
namespace GoldbachCircleMethodConditionalSieveCorrelationCompositionV18175

/-- The explicit coefficient obtained by keeping the finite sieve factor and
the good/bad frequency product as two separate inputs. -/
noncomputable def conditionalCorrelationCoefficient
    (D c CH y : ℝ) (m K X : ℕ) (R : ℝ) : ℝ :=
  4 * CH * y * (mertensProductConstant D c)^2 *
      (oneFrequencyConstant D c)^2 * arithmeticFactor m /
      (Real.log (K : ℝ))^2 *
      (Real.log (X : ℝ) / Real.log R)^4

/-- Pointwise consequence of one explicit, still hypothetical source
correlation inequality.  No Henriot estimate is instantiated here. -/
theorem arithmeticCorrelation_le_conditionalCoefficient
    (D c CH y : ℝ) (hD : 0 ≤ D) (hCH : 0 ≤ CH) (hy : 0 ≤ y)
    (hweighted : ∀ (X : ℕ), 2 ≤ X → ∀ t : ℝ, 2 ≤ t → t ≤ (X : ℝ) →
      |prefixLogMoment X t - Real.log t| ≤ D)
    (hharmonic : ∀ (X : ℕ), 2 ≤ X → ∀ t : ℝ, 2 ≤ t → t ≤ (X : ℝ) →
      |prefixHarmonicMoment X t - Real.log (Real.log t) - c| ≤ D / Real.log t)
    {m K X : ℕ} (hm : 0 < m) (hK : 2 ≤ K) (hKX : K ≤ X)
    (hmX : m ≤ X) (hX : 2 ≤ X)
    {R : ℝ} (hR : 1 < R) (hRX : R ≤ (X : ℝ))
    (I : Finset ℕ)
    (hsource : ∀ ξ η : ℝ, arithmeticCorrelation R ξ η I m ≤
      CH * y * finiteSieveProduct m K * goodBadProduct R ξ η m K)
    (ξ η : ℝ) :
    arithmeticCorrelation R ξ η I m ≤
      conditionalCorrelationCoefficient D c CH y m K X R *
        (1 + |ξ|)^2 * (1 + |η|)^2 := by
  have hsieve := finiteSieveProduct_le_mertens_harmonic_bound
    D c hD hharmonic hm hK
  have hgood := good_bad_uniform_bound D c hD hweighted hharmonic
    hm hmX hKX hX hR hRX ξ η
  have hsieve0 : 0 ≤ finiteSieveProduct m K := by
    rw [finiteSieveProduct_eq_baseline_mul_correction]
    apply mul_nonneg
    · unfold baselineProduct
      apply Finset.prod_nonneg
      intro p hp
      exact baseline_local_nonneg (Finset.mem_filter.mp hp).2
    · exact finiteCorrection_nonneg m K
  have hgood0 : 0 ≤ goodBadProduct R ξ η m K := by
    have hbad : 0 ≤ badPrimeProduct R ξ η m := by
      unfold badPrimeProduct
      apply Finset.prod_nonneg
      intro p _
      exact zero_le_one.trans (badPrimeFactor_one_le hR ξ η p m)
    have hgp : ∀ p ∈ goodPrimes m K, p.Prime := by
      intro p hp
      exact (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2
    unfold goodBadProduct
    exact mul_nonneg (mul_nonneg hbad (comparisonProduct_nonneg hR ξ hgp))
      (comparisonProduct_nonneg hR η hgp)
  have hsieveBound0 :
      0 ≤ 4 * (mertensProductConstant D c)^2 * arithmeticFactor m /
        (Real.log (K : ℝ))^2 := by
    exact div_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _))
        (arithmeticFactor_nonneg m)) (sq_nonneg _)
  have hprod := mul_le_mul hsieve hgood hgood0 hsieveBound0
  have hscale := mul_le_mul_of_nonneg_left hprod (mul_nonneg hCH hy)
  calc
    arithmeticCorrelation R ξ η I m ≤
        CH * y * finiteSieveProduct m K * goodBadProduct R ξ η m K := hsource ξ η
    _ ≤ CH * y *
        ((4 * (mertensProductConstant D c)^2 * arithmeticFactor m /
          (Real.log (K : ℝ))^2) *
        ((oneFrequencyConstant D c)^2 * (1 + |ξ|)^2 * (1 + |η|)^2 *
          (Real.log (X : ℝ) / Real.log R)^4)) := by
      simpa only [mul_assoc] using hscale
    _ = conditionalCorrelationCoefficient D c CH y m K X R *
        (1 + |ξ|)^2 * (1 + |η|)^2 := by
      unfold conditionalCorrelationCoefficient
      ring

/-- Exact V161 finite-convolution transfer from the same explicit source
inequality.  The source premise remains visible in the signature. -/
theorem conditional_sieve_correlation_transfers
    (D c CH y : ℝ) (hD : 0 ≤ D) (hCH : 0 ≤ CH) (hy : 0 ≤ y)
    (hweighted : ∀ (X : ℕ), 2 ≤ X → ∀ t : ℝ, 2 ≤ t → t ≤ (X : ℝ) →
      |prefixLogMoment X t - Real.log t| ≤ D)
    (hharmonic : ∀ (X : ℕ), 2 ≤ X → ∀ t : ℝ, 2 ≤ t → t ≤ (X : ℝ) →
      |prefixHarmonicMoment X t - Real.log (Real.log t) - c| ≤ D / Real.log t)
    {m K X : ℕ} (hm : 0 < m) (hK : 2 ≤ K) (hKX : K ≤ X)
    (hmX : m ≤ X) (hX : 2 ≤ X)
    {R : ℝ} (hR : 1 < R) (hRX : R ≤ (X : ℝ))
    (I : Finset ℕ)
    (hsource : ∀ ξ η : ℝ, arithmeticCorrelation R ξ η I m ≤
      CH * y * finiteSieveProduct m K * goodBadProduct R ξ η m K) :
    (∑ n ∈ I, radicalMajorant R n * radicalMajorant R (m - n)) ≤
      (Real.log R)^2 * conditionalCorrelationCoefficient D c CH y m K X R *
        (∫ ξ : ℝ, secondMomentDecay ξ)^2 := by
  apply correlation_bound_transfers hR I m
  intro ξ η
  exact arithmeticCorrelation_le_conditionalCoefficient
    D c CH y hD hCH hy hweighted hharmonic hm hK hKX hmX hX
      hR hRX I hsource ξ η

end GoldbachCircleMethodConditionalSieveCorrelationCompositionV18175
