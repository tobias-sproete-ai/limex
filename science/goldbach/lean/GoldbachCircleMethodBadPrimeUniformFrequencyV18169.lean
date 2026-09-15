import GoldbachCircleMethodMertensUniformConstantsV18168
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option autoImplicit false
open scoped BigOperators Classical
open GoldbachCircleMethodBadPrimeProductComparisonV18165
open GoldbachCircleMethodMertensUniformConstantsV18168
namespace GoldbachCircleMethodBadPrimeUniformFrequencyV18169

noncomputable def oneFrequencyConstant (D c : ℝ) : ℝ :=
  100*Real.exp (2*uniformC0 D+2*uniformC1 D c)

theorem oneFrequencyConstant_pos (D c : ℝ) : 0 < oneFrequencyConstant D c := by
  unfold oneFrequencyConstant
  positivity

/-- The source constants and remainders precede every application parameter. -/
theorem bad_prime_uniform_bound (D c : ℝ) (hD : 0 ≤ D)
    (hweighted : ∀ (X : ℕ), 2 ≤ X → ∀ t : ℝ, 2 ≤ t → t ≤ (X : ℝ) →
      |prefixLogMoment X t-Real.log t| ≤ D)
    (hharmonic : ∀ (X : ℕ), 2 ≤ X → ∀ t : ℝ, 2 ≤ t → t ≤ (X : ℝ) →
      |prefixHarmonicMoment X t-Real.log (Real.log t)-c| ≤ D/Real.log t)
    {m X : ℕ} (hm : 0 < m) (hmX : m ≤ X) (hX : 2 ≤ X)
    {R : ℝ} (hR : 1 < R) (hRX : R ≤ (X : ℝ)) (ξ η : ℝ) :
    badPrimeProduct R ξ η m ≤
      (oneFrequencyConstant D c)^2*(1+|ξ|)^2*(1+|η|)^2*
        (Real.log (X : ℝ)/Real.log R)^4 := by
  have hx := uniform_frequency_bound D c hD hweighted hharmonic hX hR hRX ξ
  have hy := uniform_frequency_bound D c hD hweighted hharmonic hX hR hRX η
  change comparisonProduct R ξ (primePrefix X) ≤
    oneFrequencyConstant D c*(1+|ξ|)^2*(Real.log (X : ℝ)/Real.log R)^2 at hx
  change comparisonProduct R η (primePrefix X) ≤
    oneFrequencyConstant D c*(1+|η|)^2*(Real.log (X : ℝ)/Real.log R)^2 at hy
  have hn := comparisonProduct_nonneg hR η
    (fun _ hp => (Finset.mem_filter.mp hp).2 : ∀ p ∈ primePrefix X, p.Prime)
  have hc := (oneFrequencyConstant_pos D c).le
  have hmul := mul_le_mul hx hy hn (by positivity)
  calc
    badPrimeProduct R ξ η m ≤
        comparisonProduct R ξ (primePrefix X)*comparisonProduct R η (primePrefix X) :=
      badPrimeProduct_le_prefix hR ξ η hm hmX
    _ ≤ _ := hmul
    _ = _ := by ring

theorem power_cutoff_bounds {M : ℕ} (hM : 2 ≤ M) {θ : ℝ}
    (hθ : 0 < θ) (hθ1 : θ ≤ 1) :
    1 < (M : ℝ)^θ ∧ (M : ℝ)^θ ≤ ((2*M : ℕ) : ℝ) := by
  have hMr : (2 : ℝ) ≤ M := by exact_mod_cast hM
  constructor
  · exact Real.one_lt_rpow (by linarith) hθ
  · have hr := Real.rpow_le_self_of_one_le (by linarith : (1 : ℝ) ≤ M) hθ1
    push_cast
    linarith

theorem double_window_log_ratio {M : ℕ} (hM : 2 ≤ M) {θ : ℝ} (hθ : 0 < θ) :
    Real.log ((2*M : ℕ) : ℝ)/Real.log ((M : ℝ)^θ) ≤ 2/θ := by
  have hMr : (2 : ℝ) ≤ M := by exact_mod_cast hM
  have hMp : (0 : ℝ) < M := by linarith
  have hl := Real.log_le_log (by norm_num : (0 : ℝ)<2) hMr
  have hlog := Real.log_pos (by linarith : (1 : ℝ)<M)
  push_cast
  rw [Real.log_mul (by norm_num : (2 : ℝ)≠0) hMp.ne', Real.log_rpow hMp]
  apply (div_le_iff₀ (mul_pos hθ hlog)).mpr
  calc
    Real.log 2+Real.log (M : ℝ) ≤ 2*Real.log (M : ℝ) := by linarith
    _ = (2/θ)*(θ*Real.log (M : ℝ)) := by field_simp

theorem bad_prime_power_scale_bound (D c : ℝ) (hD : 0 ≤ D)
    (hweighted : ∀ (X : ℕ), 2 ≤ X → ∀ t : ℝ, 2 ≤ t → t ≤ (X : ℝ) →
      |prefixLogMoment X t-Real.log t| ≤ D)
    (hharmonic : ∀ (X : ℕ), 2 ≤ X → ∀ t : ℝ, 2 ≤ t → t ≤ (X : ℝ) →
      |prefixHarmonicMoment X t-Real.log (Real.log t)-c| ≤ D/Real.log t)
    {m M : ℕ} (hm : 0 < m) (hmM : m ≤ 2*M) (hM : 2 ≤ M)
    {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1) (ξ η : ℝ) :
    badPrimeProduct ((M : ℝ)^θ) ξ η m ≤
      (oneFrequencyConstant D c)^2*(2/θ)^4*(1+|ξ|)^2*(1+|η|)^2 := by
  have hcut := power_cutoff_bounds hM hθ hθ1
  have hb := bad_prime_uniform_bound D c hD hweighted hharmonic hm hmM
    (by omega : 2 ≤ 2*M) hcut.1 hcut.2 ξ η
  have hratio := double_window_log_ratio hM hθ
  have hnon : 0 ≤ Real.log ((2*M : ℕ) : ℝ)/Real.log ((M : ℝ)^θ) := by
    have htwo : (1 : ℝ) ≤ ((2*M : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ 2*M)
    exact div_nonneg (Real.log_nonneg htwo) (Real.log_pos hcut.1).le
  have hp := pow_le_pow_left₀ hnon hratio 4
  calc
    badPrimeProduct ((M : ℝ)^θ) ξ η m ≤ _ := hb
    _ ≤ (oneFrequencyConstant D c)^2*(1+|ξ|)^2*(1+|η|)^2*(2/θ)^4 :=
      mul_le_mul_of_nonneg_left hp (by positivity)
    _ = _ := by ring

end GoldbachCircleMethodBadPrimeUniformFrequencyV18169

