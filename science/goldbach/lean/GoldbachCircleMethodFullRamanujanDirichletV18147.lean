import GoldbachCircleMethodOuterDivisorIntegralV18146

set_option autoImplicit false
open scoped BigOperators Classical
open GoldbachCircleMethodCompanionAbsoluteConvergenceV18141
open GoldbachCircleMethodCompanionSquarefreeGcdBindingV18139
open GoldbachCircleMethodRamanujanCoprimeBindingV1840
open GoldbachCircleMethodRamanujanCharacterProductV1843
open GoldbachCircleMethodFullSquarefreeCoefficientV1847
open GoldbachCircleMethodGeneralCoprimeCharacterV1868
open GoldbachCircleMethodFiniteResiduePrefixV1866

namespace GoldbachCircleMethodFullRamanujanDirichletV18147

/-- The genuine V118 Fourier-character coefficient with a Dirichlet
power attached. Zero modulus is explicitly excluded. -/
noncomputable def fullRamanujanDirichletTerm (r N : ℕ) (s : ℂ) (q : ℕ) : ℂ :=
  if hq : q = 0 then 0 else
    if Nat.Coprime r q then
      (((ArithmeticFunction.moebius q : ℤ) : ℂ)*finiteFourierRamanujan q N hq/
        (q.totient : ℂ))/((q : ℂ)^s)
    else 0

theorem full_term_zero (r N : ℕ) (s : ℂ) :
    fullRamanujanDirichletTerm r N s 0 = 0 := by
  simp [fullRamanujanDirichletTerm]

theorem full_term_one (r N : ℕ) (s : ℂ) :
    fullRamanujanDirichletTerm r N s 1 = 1 := by
  simp [fullRamanujanDirichletTerm,finiteFourierRamanujan_one]

theorem full_term_multiplicative (r N : ℕ) (s : ℂ) {m n : ℕ}
    (hmn : Nat.Coprime m n) :
    fullRamanujanDirichletTerm r N s (m*n) =
      fullRamanujanDirichletTerm r N s m * fullRamanujanDirichletTerm r N s n := by
  by_cases hm : m = 0
  · subst m
    simp [full_term_zero]
  by_cases hn : n = 0
  · subst n
    simp [full_term_zero]
  have hprod : m*n ≠ 0 := mul_ne_zero hm hn
  simp only [fullRamanujanDirichletTerm,dif_neg hm,dif_neg hn,dif_neg hprod]
  by_cases hrm : Nat.Coprime r m
  · by_cases hrn : Nat.Coprime r n
    · rw [if_pos (Nat.coprime_mul_iff_right.mpr ⟨hrm,hrn⟩),if_pos hrm,if_pos hrn,
        ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hmn,
        finiteFourierRamanujan_mul_of_coprime hm hn hmn N,Nat.totient_mul hmn]
      push_cast
      rw [Complex.natCast_mul_natCast_cpow]
      ring
    · have hb : ¬Nat.Coprime r (m*n) := fun h => hrn (Nat.coprime_mul_iff_right.mp h).2
      simp only [if_neg hb,if_neg hrn,mul_zero]
  · have hb : ¬Nat.Coprime r (m*n) := fun h => hrm (Nat.coprime_mul_iff_right.mp h).1
    simp only [if_neg hb,if_neg hrm,zero_mul]

noncomputable def divisorMass (N : ℕ) : ℝ := ∑ d ∈ N.divisors, (d : ℝ)

theorem divisorMass_nonneg (N : ℕ) : 0 ≤ divisorMass N :=
  Finset.sum_nonneg (fun d _ => Nat.cast_nonneg d)

theorem moebius_divisor_sum_norm_le_mass (q : ℕ) {N : ℕ} (hN : 0 < N) :
    ‖∑ d ∈ (Nat.gcd q N).divisors, ((ArithmeticFunction.moebius d : ℤ) : ℂ)*(d : ℂ)‖ ≤
      divisorMass N := by
  calc
    _ ≤ ∑ d ∈ (Nat.gcd q N).divisors,
        ‖((ArithmeticFunction.moebius d : ℤ) : ℂ)*(d : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ d ∈ (Nat.gcd q N).divisors, (d : ℝ) := by
      apply Finset.sum_le_sum
      intro d _
      have hmu : ‖((ArithmeticFunction.moebius d : ℤ) : ℂ)‖ ≤ 1 := by
        rw [Complex.norm_intCast]
        exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := d))
      rw [norm_mul,Complex.norm_natCast]
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hmu (Nat.cast_nonneg d)
    _ ≤ divisorMass N := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro d hd
        exact Nat.mem_divisors.mpr
          ⟨(Nat.dvd_of_mem_divisors hd).trans (Nat.gcd_dvd_right q N),hN.ne'⟩
      · intro d _ _
        exact Nat.cast_nonneg d

/-- Native finite divisor identity bounds the genuine Fourier
coefficient. The bound is used only for convergence, not sharp savings. -/
theorem full_term_norm_le (r : ℕ) {N : ℕ} (hN : 0 < N) (s : ℂ) (q : ℕ) :
    ‖fullRamanujanDirichletTerm r N s q‖ ≤ divisorMass N*divisorMajorant s.re q := by
  by_cases hq0 : q = 0
  · subst q
    simp [full_term_zero,divisorMajorant]
  by_cases hr : Nat.Coprime r q
  · by_cases hq : Squarefree q
    · have : NeZero q := ⟨hq0⟩
      have he : fullRamanujanDirichletTerm r N s q =
          (∑ d ∈ (Nat.gcd q N).divisors,
            ((ArithmeticFunction.moebius d : ℤ) : ℂ)*(d : ℂ)) *
            complementaryDirichletTerm 1 s q := by
        simp only [fullRamanujanDirichletTerm,dif_neg hq0,if_pos hr,
          finiteFourierRamanujan_eq_unitCharacterSum]
        rw [moebius_character_finite_divisor_sum q N hq]
        rw [complementaryDirichletTerm,if_pos ⟨hq,Nat.coprime_one_left q⟩]
        ring
      rw [he,norm_mul]
      exact mul_le_mul (moebius_divisor_sum_norm_le_mass q hN)
        (complementaryDirichletTerm_norm_le 1 s q) (norm_nonneg _) (divisorMass_nonneg N)
    · simp only [fullRamanujanDirichletTerm,dif_neg hq0,if_pos hr,
        ArithmeticFunction.moebius_eq_zero_of_not_squarefree hq,Int.cast_zero,
        zero_mul,zero_div,norm_zero]
      exact mul_nonneg (divisorMass_nonneg N) (divisorMajorant_nonneg s.re q)
  · simp only [fullRamanujanDirichletTerm,dif_neg hq0,if_neg hr,norm_zero]
    exact mul_nonneg (divisorMass_nonneg N) (divisorMajorant_nonneg s.re q)

theorem full_term_norm_summable (r : ℕ) {N : ℕ} (hN : 0 < N)
    {s : ℂ} (hs : 0 < s.re) :
    Summable (fun q => ‖fullRamanujanDirichletTerm r N s q‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (full_term_norm_le r hN s)
    ((summable_divisorMajorant hs).mul_left (divisorMass N))


theorem full_term_prime_power_zero (r N : ℕ) (s : ℂ) {p e : ℕ}
    (hp : p.Prime) (he : 2 ≤ e) :
    fullRamanujanDirichletTerm r N s (p^e) = 0 := by
  have he0 : e ≠ 0 := by omega
  have he1 : e ≠ 1 := by omega
  simp [fullRamanujanDirichletTerm,
    ArithmeticFunction.moebius_apply_prime_pow hp he0,he1]

/-- Combined Euler factor: conductor-excluded primes, primes dividing N,
and the remaining primes are distinct branches. -/
noncomputable def fullRamanujanLocalFactor (r N : ℕ) (s : ℂ) (p : ℕ) : ℂ :=
  if p ∣ r then 1 else
    if p ∣ N then 1-1/((p : ℂ)^s)
    else 1+1/((p.totient : ℂ)*(p : ℂ)^s)

theorem full_term_prime_local (r N : ℕ) (s : ℂ) {p : ℕ} (hp : p.Prime) :
    1+fullRamanujanDirichletTerm r N s p = fullRamanujanLocalFactor r N s p := by
  have hpr : Nat.Coprime r p ↔ ¬p ∣ r := Nat.coprime_comm.trans hp.coprime_iff_not_dvd
  have hpφ : (p.totient : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr hp.pos).ne'
  simp only [fullRamanujanDirichletTerm,dif_neg hp.ne_zero,
    ArithmeticFunction.moebius_apply_prime hp,Int.cast_neg,Int.cast_one,
    fullRamanujanLocalFactor]
  by_cases hr : p ∣ r
  · simp only [if_pos hr,if_neg (hpr.not.mpr (not_not.mpr hr)),add_zero]
  · rw [if_neg hr,if_pos (hpr.mpr hr)]
    by_cases hN : p ∣ N
    · rw [if_pos hN,finiteFourierRamanujan_eq_totient_of_dvd hp.ne_zero hN]
      field_simp
      ring
    · rw [if_neg hN,finiteFourierRamanujan_eq_neg_one_of_prime hp
        (Nat.coprime_comm.mpr (hp.coprime_iff_not_dvd.mpr hN))]
      ring

theorem full_term_prime_power_sum (r N : ℕ) (s : ℂ) {p : ℕ} (hp : p.Prime) :
    (∑' e : ℕ, fullRamanujanDirichletTerm r N s (p^e)) =
      fullRamanujanLocalFactor r N s p := by
  have hfin : HasSum (fun e : ℕ => fullRamanujanDirichletTerm r N s (p^e))
      (∑ e ∈ ({0,1} : Finset ℕ), fullRamanujanDirichletTerm r N s (p^e)) := by
    apply hasSum_sum_of_ne_finset_zero
    intro e he
    have he2 : 2 ≤ e := by
      simp only [Finset.mem_insert,Finset.mem_singleton] at he
      omega
    exact full_term_prime_power_zero r N s hp he2
  rw [hfin.tsum_eq]
  simp only [Finset.sum_insert,Finset.mem_singleton,zero_ne_one,not_false_eq_true,
    Finset.sum_singleton,pow_zero,pow_one,full_term_one]
  exact full_term_prime_local r N s hp

/-- HasProd for the original Fourier-defined coefficient, not a
heuristically factored replacement of the bracket. -/
theorem full_ramanujan_euler_hasProd (r : ℕ) {N : ℕ} (hN : 0 < N)
    {s : ℂ} (hs : 0 < s.re) :
    HasProd (fun p : Nat.Primes => fullRamanujanLocalFactor r N s p.val)
      (∑' q, fullRamanujanDirichletTerm r N s q) := by
  have hp := EulerProduct.eulerProduct_hasProd
    (full_term_one r N s) (full_term_multiplicative r N s)
    (full_term_norm_summable r hN hs) (full_term_zero r N s)
  have he : (fun p : Nat.Primes => ∑' e : ℕ, fullRamanujanDirichletTerm r N s (p.val^e)) =
      (fun p : Nat.Primes => fullRamanujanLocalFactor r N s p.val) :=
    funext (fun p => full_term_prime_power_sum r N s p.property)
  rw [he] at hp
  exact hp

theorem full_term_original_coefficient (r N : ℕ) (s : ℂ) (q : ℕ) [NeZero q] :
    fullRamanujanDirichletTerm r N s q =
      if Nat.Coprime r q then
        (((ArithmeticFunction.moebius q : ℤ) : ℂ)*
          unitCharacterSum q (N : ZMod q)/(q.totient : ℂ))/((q : ℂ)^s)
      else 0 := by
  simp only [fullRamanujanDirichletTerm,dif_neg (NeZero.ne q),
    finiteFourierRamanujan_eq_unitCharacterSum]

end GoldbachCircleMethodFullRamanujanDirichletV18147
