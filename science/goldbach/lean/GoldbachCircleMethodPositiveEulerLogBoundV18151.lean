import GoldbachCircleMethodPositiveEulerBudgetV18150

set_option autoImplicit false
open scoped BigOperators Classical
open Filter
open GoldbachCircleMethodCompanionAbsoluteConvergenceV18141
open GoldbachCircleMethodComplementaryEulerProductV18145
open GoldbachCircleMethodLocalEulerRadicalBoundsV18149
open GoldbachCircleMethodPositiveEulerBudgetV18150
namespace GoldbachCircleMethodPositiveEulerLogBoundV18151

theorem norm_zeta_real_bound {σ : ℝ} (hσ : 0 < σ) :
    ‖riemannZeta ((1+σ : ℝ) : ℂ)‖ ≤ 1+1/σ := by
  have hs : 1 < (((1+σ : ℝ) : ℂ)).re := by simpa using hσ
  rw [← tsum_riemannZetaSummand hs]
  calc
    _ ≤ ∑' n : ℕ, ‖riemannZetaSummandHom (Complex.ne_zero_of_one_lt_re hs) n‖ :=
      norm_tsum_le_tsum_norm (summable_riemannZetaSummand hs)
    _ = ∑' n : ℕ, (n : ℝ)^(-(1+σ)) := by
      congr 1
      funext n
      change ‖(n : ℂ)^(-((1+σ : ℝ) : ℂ))‖ = _
      rw [Complex.norm_natCast_cpow_of_re_ne_zero n (by simpa using (show -(1+σ) ≠ 0 by linarith))]
      simp only [Complex.neg_re,Complex.ofReal_re]
    _ ≤ _ := pseries_explicit_bound hσ

theorem norm_complementary_prime_real {p : ℕ} (hp : p.Prime) (σ : ℝ) :
    ‖complementaryLocalFactor 1 (σ : ℂ) p‖ = positiveLocal (p : ℝ) σ := by
  have he : complementaryLocalFactor 1 (σ : ℂ) p =
      ((positiveLocal (p : ℝ) σ : ℝ) : ℂ) := by
    unfold complementaryLocalFactor positiveLocal
    rw [if_neg hp.not_dvd_one,Nat.totient_prime hp]
    push_cast
    rw [Complex.ofReal_cpow (Nat.cast_nonneg p)]
    rw [Nat.cast_sub hp.one_le,Nat.cast_one]
    rfl
  rw [he,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (positiveLocal_nonneg (by exact_mod_cast hp.one_lt) σ)]

/-- Real positive product obtained from the already convergent actual series. -/
theorem positive_euler_hasProd {σ : ℝ} (hσ : 0 < σ) :
    HasProd (fun p : Nat.Primes => positiveLocal (p.val : ℝ) σ)
      ‖∑' q, complementaryDirichletTerm 1 (σ : ℂ) q‖ := by
  have hh := (complementary_euler_hasProd 1 (by simpa using hσ : 0 < (σ : ℂ).re)).map
    (normHom.toMonoidHom : ℂ →* ℝ) continuous_norm
  have he : (fun p : Nat.Primes => ‖complementaryLocalFactor 1 (σ : ℂ) p.val‖) =
      (fun p : Nat.Primes => positiveLocal (p.val : ℝ) σ) :=
    funext (fun p => norm_complementary_prime_real p.property σ)
  change HasProd (fun p : Nat.Primes => ‖complementaryLocalFactor 1 (σ : ℂ) p.val‖) _ at hh
  rw [he] at hh
  exact hh

theorem norm_zeta_prime_factor {p : ℕ} (hp : p.Prime) {σ : ℝ} (hσ : 0 ≤ σ) :
    ‖(1-(p : ℂ)^(-((1+σ : ℝ) : ℂ)))⁻¹‖ =
      (1-1/(p : ℝ)^(1+σ))⁻¹ := by
  have he : (1-(p : ℂ)^(-((1+σ : ℝ) : ℂ)))⁻¹ =
      (((1-1/(p : ℝ)^(1+σ))⁻¹ : ℝ) : ℂ) := by
    rw [Complex.ofReal_inv,Complex.ofReal_sub,Complex.ofReal_one,
      Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_cpow (Nat.cast_nonneg p),
      Complex.cpow_neg,one_div]
    simp only [Complex.ofReal_natCast]
  rw [he,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg]
  exact inv_nonneg.mpr (zeta_correction_factor_pos (by exact_mod_cast hp.one_lt) hσ).le

theorem positive_zeta_hasProd {σ : ℝ} (hσ : 0 < σ) :
    HasProd (fun p : Nat.Primes => (1-1/(p.val : ℝ)^(1+σ))⁻¹)
      ‖riemannZeta ((1+σ : ℝ) : ℂ)‖ := by
  have hh := (riemannZeta_eulerProduct_hasProd (by simpa using hσ :
      1 < (((1+σ : ℝ) : ℂ)).re)).map
    (normHom.toMonoidHom : ℂ →* ℝ) continuous_norm
  have he : (fun p : Nat.Primes => ‖(1-(p.val : ℂ)^(-((1+σ : ℝ) : ℂ)))⁻¹‖) =
      (fun p : Nat.Primes => (1-1/(p.val : ℝ)^(1+σ))⁻¹) :=
    funext (fun p => norm_zeta_prime_factor p.property hσ.le)
  change HasProd (fun p : Nat.Primes => ‖(1-(p.val : ℂ)^(-((1+σ : ℝ) : ℂ)))⁻¹‖) _ at hh
  rw [he] at hh
  exact hh

theorem finite_nonnegative_product_le_limit {ι : Type*} (f : ι → ℝ)
    {a : ℝ} (hf : HasProd f a) (hone : ∀ i, 1 ≤ f i) (S : Finset ι) :
    (∏ i ∈ S, f i) ≤ a := by
  apply ge_of_tendsto hf
  filter_upwards [eventually_ge_atTop S] with T hT
  exact Finset.prod_le_prod_of_subset_of_one_le hT
    (fun i _ => zero_le_one.trans (hone i)) (fun i _ _ => hone i)

theorem finite_positive_euler_bound {σ : ℝ} (hσ : 0 < σ) (S : Finset Nat.Primes) :
    (∏ p ∈ S, positiveLocal (p.val : ℝ) σ) ≤
      Real.exp 1 * ‖riemannZeta ((1+σ : ℝ) : ℂ)‖ := by
  have hb0 := finite_positive_euler_correction_budget (S.image Subtype.val)
    (fun p hp => by
      obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
      exact q.property) hσ.le
  have he : (∏ p ∈ S.image (Subtype.val : Nat.Primes → ℕ),
      positiveLocal (p : ℝ) σ*(1-1/(p : ℝ)^(1+σ))) =
      ∏ p ∈ S, positiveLocal (p.val : ℝ) σ*(1-1/(p.val : ℝ)^(1+σ)) :=
    Finset.prod_image (fun p hp q hq heq => Subtype.val_injective heq)
  have hb : (∏ p ∈ S, positiveLocal (p.val : ℝ) σ*(1-1/(p.val : ℝ)^(1+σ))) ≤ Real.exp 1 :=
    he.symm.trans_le hb0
  have hzpos : 0 < ∏ p ∈ S, (1-1/(p.val : ℝ)^(1+σ)) :=
    Finset.prod_pos (fun p _ => zeta_correction_factor_pos (by exact_mod_cast p.property.one_lt) hσ.le)
  rw [Finset.prod_mul_distrib] at hb
  have hb' := (le_div_iff₀ hzpos).mpr hb
  have hz := finite_nonnegative_product_le_limit _ (positive_zeta_hasProd hσ)
    (fun p => by
      have hp0 := zeta_correction_factor_pos (p := (p.val : ℝ))
        (by exact_mod_cast p.property.one_lt) hσ.le
      apply (one_le_inv₀ hp0).mpr
      exact sub_le_self _ (by positivity)) S
  calc
    _ ≤ Real.exp 1/(∏ p ∈ S, (1-1/(p.val : ℝ)^(1+σ))) := hb'
    _ = Real.exp 1*(∏ p ∈ S, (1-1/(p.val : ℝ)^(1+σ))⁻¹) := by
      rw [div_eq_mul_inv,Finset.prod_inv_distrib]
    _ ≤ _ := mul_le_mul_of_nonneg_left hz (Real.exp_pos _).le

/-- Sharp logarithmic-order budget, with an explicit absolute constant. -/
theorem actual_positive_euler_log_bound {σ : ℝ} (hσ : 0 < σ) :
    ‖∑' q, complementaryDirichletTerm 1 (σ : ℂ) q‖ ≤ Real.exp 1*(1+1/σ) := by
  have hh := hasProd_le_of_prod_le (positive_euler_hasProd hσ)
    (finite_positive_euler_bound hσ)
  exact hh.trans (mul_le_mul_of_nonneg_left (norm_zeta_real_bound hσ) (Real.exp_pos _).le)

theorem complementary_series_sharp_norm_bound (k : ℕ) {s : ℂ} (hs : 0 < s.re) :
    ‖∑' q, complementaryDirichletTerm k s q‖ ≤ Real.exp 1*(1+1/s.re) := by
  have hk := (complementary_euler_hasProd k hs).map
    (normHom.toMonoidHom : ℂ →* ℝ) continuous_norm
  change HasProd (fun p : Nat.Primes => ‖complementaryLocalFactor k s p.val‖)
    ‖∑' q, complementaryDirichletTerm k s q‖ at hk
  have hp := positive_euler_hasProd hs
  have hpoint (p : Nat.Primes) :
      ‖complementaryLocalFactor k s p.val‖ ≤ positiveLocal (p.val : ℝ) s.re := by
    unfold complementaryLocalFactor
    by_cases hd : p.val ∣ k
    · rw [if_pos hd,norm_one]
      unfold positiveLocal
      have hnonneg : 0 ≤ 1/(((p.val : ℝ)-1)*(p.val : ℝ)^s.re) := by
        apply div_nonneg zero_le_one
        apply mul_nonneg
        · have hh : (1 : ℝ) < (p.val : ℝ) := by exact_mod_cast p.property.one_lt
          linarith
        · exact (Real.rpow_pos_of_pos (Nat.cast_pos.mpr p.property.pos) _).le
      linarith
    · rw [if_neg hd]
      exact norm_good_prime_factor_le_positiveLocal p.property s
  have hb := le_of_tendsto_of_tendsto' hk hp (fun S =>
    Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun p _ => hpoint p))
  exact hb.trans (actual_positive_euler_log_bound hs)

theorem radical_line_sharp_complementary_bound {R : ℝ} (hR : 1 < R)
    (k : ℕ) (ξ : ℝ) :
    ‖∑' q, complementaryDirichletTerm k (radicalExponent R ξ) q‖ ≤
      Real.exp 1*(1+Real.log R) := by
  have hb := complementary_series_sharp_norm_bound k (radicalExponent_re_pos hR ξ)
  simpa only [radicalExponent_re,one_div_one_div] using hb

end GoldbachCircleMethodPositiveEulerLogBoundV18151
