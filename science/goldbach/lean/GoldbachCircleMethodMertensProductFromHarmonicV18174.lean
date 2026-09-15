import GoldbachCircleMethodGlobalSieveFiniteFactorV18173
import GoldbachCircleMethodMertensUniformConstantsV18168

set_option autoImplicit false
open scoped BigOperators Classical
open GoldbachCircleMethodBadPrimeProductComparisonV18165
open GoldbachCircleMethodMertensUniformConstantsV18168
open GoldbachCircleMethodGlobalSieveFiniteFactorV18173
namespace GoldbachCircleMethodMertensProductFromHarmonicV18174

/-- The explicit constant obtained from one harmonic-prime remainder bound. -/
noncomputable def mertensProductConstant (D c : ℝ) : ℝ :=
  Real.exp (-c + D / Real.log 2)

theorem mertensProductConstant_pos (D c : ℝ) :
    0 < mertensProductConstant D c := by
  unfold mertensProductConstant
  exact Real.exp_pos _

theorem finiteMertensProduct_pos (K : ℕ) :
    0 < finiteMertensProduct K := by
  unfold finiteMertensProduct
  apply Finset.prod_pos
  intro p hp
  have hprime : p.Prime := (Finset.mem_filter.mp hp).2
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hprime.pos
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hprime.one_lt
  exact sub_pos.mpr ((div_lt_one hp0).mpr hp1)

theorem localMertensFactor_le_exp (p : ℕ) :
    1 - 1 / (p : ℝ) ≤ Real.exp (-(1 / (p : ℝ))) := by
  simpa only [sub_eq_add_neg, add_comm] using
    Real.add_one_le_exp (-(1 / (p : ℝ)))

/-- A finite Euler-product comparison requiring no asymptotic Mertens input. -/
theorem finiteMertensProduct_le_exp_neg_harmonic (K : ℕ) :
    finiteMertensProduct K ≤
      Real.exp (-(∑ p ∈ primePrefix K, 1 / (p : ℝ))) := by
  rw [← Finset.sum_neg_distrib, Real.exp_sum]
  unfold finiteMertensProduct
  apply Finset.prod_le_prod
  · intro p hp
    have hprime : p.Prime := (Finset.mem_filter.mp hp).2
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hprime.pos
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hprime.one_le
    exact sub_nonneg.mpr ((div_le_one hp0).mpr hp1)
  · intro p _
    exact localMertensFactor_le_exp p

/-- Pointwise conversion of the existing explicit harmonic remainder at `K`
into a finite Mertens-product upper bound. -/
theorem finiteMertensProduct_le_constant_div_log
    {K : ℕ} (hK : 2 ≤ K) {D c : ℝ} (hD : 0 ≤ D)
    (hrem :
      |prefixHarmonicMoment K (K : ℝ) - Real.log (Real.log (K : ℝ)) - c| ≤
        D / Real.log (K : ℝ)) :
    finiteMertensProduct K ≤
      mertensProductConstant D c / Real.log (K : ℝ) := by
  have hKr : (2 : ℝ) ≤ K := by exact_mod_cast hK
  have hK1 : (1 : ℝ) < K := by linarith
  have hlogK : 0 < Real.log (K : ℝ) := Real.log_pos hK1
  have hbudget := error_budget_mono hD hKr
  have hlower := (abs_le.mp hrem).1
  have hmoment :
      Real.log (Real.log (K : ℝ)) + c - D / Real.log 2 ≤
        prefixHarmonicMoment K (K : ℝ) := by
    linarith
  calc
    finiteMertensProduct K ≤
        Real.exp (-(prefixHarmonicMoment K (K : ℝ))) := by
      simpa only [prefix_full] using finiteMertensProduct_le_exp_neg_harmonic K
    _ ≤ Real.exp (-(Real.log (Real.log (K : ℝ)) + c - D / Real.log 2)) :=
      Real.exp_le_exp.mpr (neg_le_neg hmoment)
    _ = mertensProductConstant D c / Real.log (K : ℝ) := by
      rw [show -(Real.log (Real.log (K : ℝ)) + c - D / Real.log 2) =
          (-c + D / Real.log 2) - Real.log (Real.log (K : ℝ)) by ring]
      rw [Real.exp_sub, Real.exp_log hlogK]
      rfl

/-- Uniform form with `D,c` quantified before every finite cutoff. Their
existence remains an explicit source hypothesis. -/
theorem finiteMertensProduct_uniform_bound
    (D c : ℝ) (hD : 0 ≤ D)
    (hharmonic : ∀ (X : ℕ), 2 ≤ X → ∀ t : ℝ, 2 ≤ t → t ≤ (X : ℝ) →
      |prefixHarmonicMoment X t - Real.log (Real.log t) - c| ≤ D / Real.log t)
    {K : ℕ} (hK : 2 ≤ K) :
    finiteMertensProduct K ≤
      mertensProductConstant D c / Real.log (K : ℝ) := by
  apply finiteMertensProduct_le_constant_div_log hK hD
  exact hharmonic K hK K (by exact_mod_cast hK) le_rfl

theorem arithmeticFactor_nonneg (m : ℕ) : 0 ≤ arithmeticFactor m := by
  unfold arithmeticFactor
  apply Finset.prod_nonneg
  intro p hp
  exact zero_le_one.trans
    (correctionFactor_one_le (Finset.mem_filter.mp hp).2)

/-- Conditional finite sieve-product consequence. The arithmetic factor stays
explicit and no Mertens-source existence statement is added. -/
theorem finiteSieveProduct_le_mertens_harmonic_bound
    (D c : ℝ) (hD : 0 ≤ D)
    (hharmonic : ∀ (X : ℕ), 2 ≤ X → ∀ t : ℝ, 2 ≤ t → t ≤ (X : ℝ) →
      |prefixHarmonicMoment X t - Real.log (Real.log t) - c| ≤ D / Real.log t)
    {m K : ℕ} (hm : 0 < m) (hK : 2 ≤ K) :
    finiteSieveProduct m K ≤
      4 * (mertensProductConstant D c)^2 * arithmeticFactor m /
        (Real.log (K : ℝ))^2 := by
  have hP := finiteMertensProduct_uniform_bound D c hD hharmonic hK
  have hP0 := (finiteMertensProduct_pos K).le
  have hKr : (2 : ℝ) ≤ K := by exact_mod_cast hK
  have hlogK : 0 < Real.log (K : ℝ) := Real.log_pos (by linarith)
  have hC0 : 0 ≤ mertensProductConstant D c / Real.log (K : ℝ) := by
    exact div_nonneg (mertensProductConstant_pos D c).le hlogK.le
  have hsq : (finiteMertensProduct K)^2 ≤
      (mertensProductConstant D c / Real.log (K : ℝ))^2 :=
    (sq_le_sq₀ hP0 hC0).mpr hP
  calc
    finiteSieveProduct m K ≤
        4 * arithmeticFactor m * (finiteMertensProduct K)^2 :=
      finiteSieveProduct_le_four_mul hm hK
    _ ≤ 4 * arithmeticFactor m *
        (mertensProductConstant D c / Real.log (K : ℝ))^2 := by
      exact mul_le_mul_of_nonneg_left hsq
        (mul_nonneg (by norm_num) (arithmeticFactor_nonneg m))
    _ = 4 * (mertensProductConstant D c)^2 * arithmeticFactor m /
        (Real.log (K : ℝ))^2 := by ring

end GoldbachCircleMethodMertensProductFromHarmonicV18174
