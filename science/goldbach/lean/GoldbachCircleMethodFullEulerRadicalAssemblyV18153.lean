import GoldbachCircleMethodConductorProductCompensationV18152

set_option autoImplicit false
open scoped BigOperators Classical
open Filter
open GoldbachCircleMethodCompanionAbsoluteConvergenceV18141
open GoldbachCircleMethodFullRamanujanDirichletV18147
open GoldbachCircleMethodLocalEulerRadicalBoundsV18149
open GoldbachCircleMethodPositiveEulerBudgetV18150
open GoldbachCircleMethodPositiveEulerLogBoundV18151
open GoldbachCircleMethodConductorProductCompensationV18152
namespace GoldbachCircleMethodFullEulerRadicalAssemblyV18153

noncomputable def primeDivisors (n : ℕ) : Finset Nat.Primes :=
  n.primeFactors.subtype Nat.Prime

theorem mem_primeDivisors {n : ℕ} (p : Nat.Primes) :
    p ∈ primeDivisors n ↔ p.val ∈ n.primeFactors :=
  Finset.mem_subtype

theorem primeDivisors_product (n : ℕ) (f : ℕ → ℝ) :
    (∏ p ∈ primeDivisors n, f p.val) = ∏ p ∈ n.primeFactors, f p :=
  Finset.prod_subtype_of_mem f (fun _ hp => Nat.prime_of_mem_primeFactors hp)

theorem supported_prime_product {n : ℕ} (hn : 0 < n)
    (S : Finset Nat.Primes) (hS : primeDivisors n ⊆ S) (f : ℕ → ℝ) :
    (∏ p ∈ S, if p.val ∣ n then f p.val else 1) =
      ∏ p ∈ n.primeFactors, f p := by
  calc
    _ = ∏ p ∈ primeDivisors n, if p.val ∣ n then f p.val else 1 := by
      symm
      apply Finset.prod_subset hS
      intro p hp hnot
      rw [if_neg]
      intro hd
      exact hnot ((mem_primeDivisors p).mpr (Nat.mem_primeFactors.mpr ⟨p.property,hd,hn.ne'⟩))
    _ = ∏ p ∈ primeDivisors n, f p.val := by
      apply Finset.prod_congr rfl
      intro p hp
      exact if_pos (Nat.mem_primeFactors.mp ((mem_primeDivisors p).mp hp)).2.1
    _ = _ := primeDivisors_product n f

theorem positiveLocal_one_le {p : ℝ} (hp : 1 < p) (σ : ℝ) :
    1 ≤ positiveLocal p σ := by
  unfold positiveLocal
  have hh : 0 ≤ 1/((p-1)*p^σ) :=
    div_nonneg zero_le_one (mul_nonneg (by linarith)
      (Real.rpow_pos_of_pos (by linarith) _).le)
  linarith

theorem compensated_full_local_bound {r N : ℕ} (hcop : r.Coprime N)
    {s : ℂ} (hs : 0 ≤ s.re) (p : Nat.Primes) :
    (if p.val ∣ r then conductorLocal (p.val : ℝ) s.re else 1) *
      ‖fullRamanujanLocalFactor r N s p.val‖ ≤
    positiveLocal (p.val : ℝ) s.re *
      (if p.val ∣ N then ‖1-1/(p.val : ℂ)^s‖ else 1) := by
  have hp : (1 : ℝ) < (p.val : ℝ) := by exact_mod_cast p.property.one_lt
  unfold fullRamanujanLocalFactor
  by_cases hr : p.val ∣ r
  · have hn : ¬ p.val ∣ N := by
      intro hn
      have hd := Nat.dvd_gcd hr hn
      rw [hcop.gcd_eq_one] at hd
      exact p.property.not_dvd_one hd
    simp only [hr,hn,ite_true,ite_false,norm_one,mul_one]
    exact conductorLocal_le_positiveLocal hp hs
  · simp only [hr,ite_false,one_mul]
    by_cases hn : p.val ∣ N
    · simp only [hn,ite_true]
      exact le_mul_of_one_le_left (norm_nonneg _) (positiveLocal_one_le hp _)
    · simp only [hn,ite_false,mul_one]
      exact norm_good_prime_factor_le_positiveLocal p.property s

theorem finite_compensated_full_product {r N : ℕ}
    (hr : 0 < r) (hN : 0 < N) (hcop : r.Coprime N)
    {s : ℂ} (hs : 0 ≤ s.re) (S : Finset Nat.Primes)
    (hrS : primeDivisors r ⊆ S) (hNS : primeDivisors N ⊆ S) :
    conductorWeight r s.re * (∏ p ∈ S, ‖fullRamanujanLocalFactor r N s p.val‖) ≤
      (∏ p ∈ S, positiveLocal (p.val : ℝ) s.re) *
        ‖∏ p ∈ N.primeFactors, (1-1/(p : ℂ)^s)‖ := by
  have hc := conductorWeight_le_local_product hr hs
  have heC := supported_prime_product hr S hrS (fun p => conductorLocal (p : ℝ) s.re)
  rw [← heC] at hc
  have hbS := Finset.prod_le_prod (s := S)
    (fun p _ => mul_nonneg (by
      split_ifs
      · exact conductorLocal_nonneg (by exact_mod_cast p.property.one_lt) _
      · exact zero_le_one) (norm_nonneg _))
    (fun p _ => compensated_full_local_bound hcop hs p)
  rw [Finset.prod_mul_distrib,Finset.prod_mul_distrib] at hbS
  have heN := supported_prime_product hN S hNS (fun p => ‖1-1/(p : ℂ)^s‖)
  have heR := congrArg (fun b : ℝ => (∏ p ∈ S, positiveLocal (p.val : ℝ) s.re)*b) heN
  have hbN := hbS.trans_eq heR
  rw [norm_prod]
  exact (mul_le_mul_of_nonneg_right hc (Finset.prod_nonneg (fun _ _ => norm_nonneg _))).trans hbN

/-- No division by N-prime factors, which may vanish, is used. -/
theorem conductor_compensated_full_series_bound {r N : ℕ}
    (hr : 0 < r) (hN : 0 < N) (hcop : r.Coprime N)
    {s : ℂ} (hs : 0 < s.re) :
    conductorWeight r s.re * ‖∑' q, fullRamanujanDirichletTerm r N s q‖ ≤
      (Real.exp 1*(1+1/s.re)) * ‖∏ p ∈ N.primeFactors, (1-1/(p : ℂ)^s)‖ := by
  have hf := (full_ramanujan_euler_hasProd r hN hs).map
    (normHom.toMonoidHom : ℂ →* ℝ) continuous_norm
  change HasProd (fun p : Nat.Primes => ‖fullRamanujanLocalFactor r N s p.val‖)
    ‖∑' q, fullRamanujanDirichletTerm r N s q‖ at hf
  have hp := positive_euler_hasProd hs
  have hh := le_of_tendsto_of_tendsto
    (hf.const_mul (conductorWeight r s.re))
    (hp.mul_const ‖∏ p ∈ N.primeFactors, (1-1/(p : ℂ)^s)‖)
    (by
      filter_upwards [eventually_ge_atTop (primeDivisors r ∪ primeDivisors N)] with S hS
      exact finite_compensated_full_product hr hN hcop hs.le S
        (Finset.Subset.trans Finset.subset_union_left hS)
        (Finset.Subset.trans Finset.subset_union_right hS))
  exact hh.trans (mul_le_mul_of_nonneg_right (actual_positive_euler_log_bound hs) (norm_nonneg _))

theorem conductor_compensated_radical_line_bound {R : ℝ} (hR : 1 < R)
    (ξ : ℝ) {r N : ℕ} (hr : 0 < r) (hN : 0 < N) (hcop : r.Coprime N) :
    conductorWeight r (1/Real.log R) *
      ‖∑' q, fullRamanujanDirichletTerm r N (radicalExponent R ξ) q‖ ≤
      (Real.exp 1*(1+Real.log R))*((N.divisors.card : ℝ)*radicalEnvelope R ξ N) := by
  have hb := conductor_compensated_full_series_bound hr hN hcop (radicalExponent_re_pos hR ξ)
  simp only [radicalExponent_re,one_div_one_div] at hb
  exact hb.trans (mul_le_mul_of_nonneg_left (actual_N_prime_product_radical_bound hR ξ hN)
    (mul_nonneg (Real.exp_pos _).le (by have := Real.log_pos hR; linarith)))

end GoldbachCircleMethodFullEulerRadicalAssemblyV18153
