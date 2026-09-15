import GoldbachCircleMethodRadicalMertensPrefixBindingV18167

set_option autoImplicit false
open scoped BigOperators Classical
open GoldbachCircleMethodBadPrimeProductComparisonV18165
open GoldbachCircleMethodRadicalMertensPrefixBindingV18167
namespace GoldbachCircleMethodMertensUniformConstantsV18168

noncomputable def prefixLogMoment (X : ℕ) (t : ℝ) : ℝ :=
  ∑ p ∈ (primePrefix X).filter (fun (p : ℕ) => (p : ℝ) ≤ t),
    Real.log (p : ℝ)/(p : ℝ)

noncomputable def prefixHarmonicMoment (X : ℕ) (t : ℝ) : ℝ :=
  ∑ p ∈ (primePrefix X).filter (fun (p : ℕ) => (p : ℝ) ≤ t), 1/(p : ℝ)

noncomputable def uniformC0 (D : ℝ) : ℝ := 1+D/Real.log 2
noncomputable def uniformC1 (D c : ℝ) : ℝ :=
  |c|+|Real.log (Real.log 2)|+2*D/Real.log 2

theorem log_two_pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)

theorem prefix_full (X : ℕ) :
    prefixHarmonicMoment X (X : ℝ) = ∑ p ∈ primePrefix X, 1/(p : ℝ) := by
  unfold prefixHarmonicMoment
  have he : (primePrefix X).filter (fun (p : ℕ) => (p : ℝ) ≤ (X : ℝ)) = primePrefix X := by
    apply Finset.filter_eq_self.mpr
    intro p hp
    have h := Finset.mem_range.mp (Finset.mem_filter.mp hp).1
    exact_mod_cast (by omega : p ≤ X)
  rw [he]

theorem tail_identity (X : ℕ) (t : ℝ) :
    (∑ p ∈ (primePrefix X).filter (fun (p : ℕ) => t < (p : ℝ)), 1/(p : ℝ)) =
      prefixHarmonicMoment X (X : ℝ)-prefixHarmonicMoment X t := by
  have he := Finset.sum_filter_add_sum_filter_not (primePrefix X)
    (fun (p : ℕ) => (p : ℝ) ≤ t) (fun p => 1/(p : ℝ))
  simp only [not_le] at he
  rw [prefix_full]
  unfold prefixHarmonicMoment
  linarith

theorem error_budget_mono {D t : ℝ} (hD : 0 ≤ D) (ht : 2 ≤ t) :
    D/Real.log t ≤ D/Real.log 2 := by
  apply div_le_div_of_nonneg_left hD log_two_pos
  exact Real.log_le_log (by norm_num) ht

theorem uniformC0_nonneg {D : ℝ} (hD : 0 ≤ D) : 0 ≤ uniformC0 D := by
  unfold uniformC0
  positivity

theorem log_moment_bound {X : ℕ} {t D : ℝ} (hD : 0 ≤ D) (ht : 2 ≤ t)
    (he : |prefixLogMoment X t-Real.log t| ≤ D) :
    prefixLogMoment X t ≤ uniformC0 D*Real.log t := by
  have hlog := Real.log_le_log (by norm_num : (0 : ℝ)<2) ht
  have hd : D ≤ (D/Real.log 2)*Real.log t := by
    calc
      D = (D/Real.log 2)*Real.log 2 := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hlog (div_nonneg hD log_two_pos.le)
  have hh := (abs_le.mp he).2
  unfold uniformC0
  nlinarith

theorem tail_moment_bound {X : ℕ} (hX : 2 ≤ X) {t D c : ℝ}
    (hD : 0 ≤ D) (ht : 2 ≤ t)
    (heX : |prefixHarmonicMoment X (X : ℝ)-Real.log (Real.log (X : ℝ))-c| ≤ D/Real.log (X : ℝ))
    (het : |prefixHarmonicMoment X t-Real.log (Real.log t)-c| ≤ D/Real.log t) :
    (∑ p ∈ (primePrefix X).filter (fun (p : ℕ) => t < (p : ℝ)), 1/(p : ℝ)) ≤
      uniformC1 D c + Real.log (Real.log (X : ℝ)/Real.log t) := by
  have hXr : (2 : ℝ) ≤ X := by exact_mod_cast hX
  have hX1 : (1 : ℝ)<X := by linarith
  have ht1 : 1<t := by linarith
  have hxerr := error_budget_mono hD hXr
  have hterr := error_budget_mono hD ht
  have hx := (abs_le.mp heX).2
  have hl := (abs_le.mp het).1
  rw [tail_identity, Real.log_div (Real.log_pos hX1).ne' (Real.log_pos ht1).ne']
  unfold uniformC1
  have ha := abs_nonneg c
  have hb := abs_nonneg (Real.log (Real.log 2))
  rw [mul_div_assoc]
  linarith

theorem full_moment_bound {X : ℕ} (hX : 2 ≤ X) {D c : ℝ} (hD : 0 ≤ D)
    (heX : |prefixHarmonicMoment X (X : ℝ)-Real.log (Real.log (X : ℝ))-c| ≤ D/Real.log (X : ℝ)) :
    (∑ p ∈ primePrefix X, 1/(p : ℝ)) ≤
      uniformC1 D c + Real.log (Real.log (X : ℝ)/Real.log 2) := by
  have hXr : (2 : ℝ) ≤ X := by exact_mod_cast hX
  have hX1 : (1 : ℝ)<X := by linarith
  have hxerr := error_budget_mono hD hXr
  have hx := (abs_le.mp heX).2
  rw [← prefix_full, Real.log_div (Real.log_pos hX1).ne' log_two_pos.ne']
  unfold uniformC1
  have ha := le_abs_self c
  have hb := le_abs_self (Real.log (Real.log 2))
  have hd := div_nonneg hD log_two_pos.le
  rw [mul_div_assoc]
  linarith

/-- Constants and source remainder estimates are quantified before all
application parameters; their existence remains an external-source input. -/
theorem uniform_frequency_bound (D c : ℝ) (hD : 0 ≤ D)
    (hweighted : ∀ (X : ℕ), 2 ≤ X → ∀ t : ℝ, 2 ≤ t → t ≤ (X : ℝ) →
      |prefixLogMoment X t-Real.log t| ≤ D)
    (hharmonic : ∀ (X : ℕ), 2 ≤ X → ∀ t : ℝ, 2 ≤ t → t ≤ (X : ℝ) →
      |prefixHarmonicMoment X t-Real.log (Real.log t)-c| ≤ D/Real.log t)
    {X : ℕ} (hX : 2 ≤ X) {R : ℝ} (hR : 1 < R) (hRX : R ≤ (X : ℝ)) (ξ : ℝ) :
    comparisonProduct R ξ (primePrefix X) ≤
      100*Real.exp (2*uniformC0 D+2*uniformC1 D c)*(1+|ξ|)^2*
        (Real.log (X : ℝ)/Real.log R)^2 := by
  have hXr : (2 : ℝ) ≤ X := by exact_mod_cast hX
  have hx := hharmonic X hX X hXr le_rfl
  apply prefix_bound_from_mertens hX (uniformC0_nonneg hD)
  · intro t ht htX
    exact log_moment_bound hD ht (hweighted X hX t ht htX)
  · intro t ht htX
    exact tail_moment_bound hX hD ht hx (hharmonic X hX t ht htX)
  · exact full_moment_bound hX hD hx
  · exact hR
  · exact hRX

end GoldbachCircleMethodMertensUniformConstantsV18168
