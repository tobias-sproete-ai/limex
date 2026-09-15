import GoldbachCircleMethodDirectEulerMellinOperatorV18148
import Mathlib.NumberTheory.ArithmeticFunction.Misc

set_option autoImplicit false
open scoped BigOperators Classical
open GoldbachCircleMethodCompanionAbsoluteConvergenceV18141
open GoldbachCircleMethodFullRamanujanDirichletV18147
namespace GoldbachCircleMethodLocalEulerRadicalBoundsV18149

noncomputable def positiveLocal (p σ : ℝ) : ℝ := 1 + 1/((p-1)*p^σ)

theorem local_correction_identity {p : ℝ} (hp : 1 < p) (t : ℝ) :
    (1+t/(p-1))*(1-t/p) = 1+(t-t^2)/(p*(p-1)) := by
  have hp0 : p ≠ 0 := (lt_trans zero_lt_one hp).ne'
  have hd0 : p-1 ≠ 0 := sub_ne_zero.mpr hp.ne'
  field_simp [hp0,hd0]
  ring

theorem local_correction_le_exp {p t : ℝ} (hp : 1 < p) :
    (1+t/(p-1))*(1-t/p) ≤ Real.exp (1/(p*(p-1))) := by
  rw [local_correction_identity hp]
  have hd : 0 < p*(p-1) := mul_pos (by linarith) (by linarith)
  have hnum : t-t^2 ≤ 1 := by nlinarith [sq_nonneg (t-1/2)]
  calc
    _ ≤ 1+1/(p*(p-1)) := add_le_add_right ((div_le_div_iff_of_pos_right hd).mpr hnum) _
    _ ≤ _ := by simpa only [add_comm] using Real.add_one_le_exp (1/(p*(p-1)))

theorem local_conductor_compensation {p t : ℝ} (hp : 1 < p) (ht : t ≤ 1) :
    p/(p-1)*t ≤ 1+t/(p-1) := by
  have hd : 0 < p-1 := by linarith
  apply (mul_le_mul_iff_left₀ hd).mp
  have he : (1+t/(p-1))*(p-1) = p-1+t := by field_simp [hd.ne']
  have he' : (p/(p-1)*t)*(p-1) = p*t := by field_simp [hd.ne']
  rw [he',he]
  nlinarith

theorem reciprocal_nat_cpow_norm_le_one {p : ℕ} (hp : 0 < p)
    {s : ℂ} (hs : 0 ≤ s.re) : ‖1/((p : ℂ)^s)‖ ≤ 1 := by
  rw [norm_div,norm_one,Complex.norm_natCast_cpow_of_pos hp]
  apply (div_le_one (Real.rpow_pos_of_pos (Nat.cast_pos.mpr hp) _)).mpr
  exact Real.one_le_rpow (by exact_mod_cast hp) hs

theorem norm_one_sub_reciprocal_cpow_le_two {p : ℕ} (hp : 0 < p)
    {s : ℂ} (hs : 0 ≤ s.re) : ‖1-1/((p : ℂ)^s)‖ ≤ 2 := by
  have hb := norm_sub_le (1 : ℂ) (1/((p : ℂ)^s))
  rw [norm_one] at hb
  linarith [reciprocal_nat_cpow_norm_le_one hp hs]

theorem norm_one_sub_reciprocal_cpow_le_log {p : ℕ} (hp : 0 < p)
    {s : ℂ} (hs : 0 ≤ s.re) :
    ‖1-1/((p : ℂ)^s)‖ ≤ 2*‖s‖*Real.log (p : ℝ) := by
  let z : ℂ := -(Complex.log (p : ℂ)*s)
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  have hz : ‖z‖ = ‖s‖*Real.log (p : ℝ) := by
    dsimp [z]
    rw [norm_neg,norm_mul,← Complex.natCast_log,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (Real.log_nonneg (by exact_mod_cast hp))]
    ring
  by_cases hsmall : ‖z‖ ≤ 1
  · have he : 1/((p : ℂ)^s) = Complex.exp z := by
      rw [Complex.cpow_def_of_ne_zero hpC,one_div,← Complex.exp_neg]
    rw [he,norm_sub_rev]
    have hb := Complex.norm_exp_sub_one_le hsmall
    rw [hz] at hb
    nlinarith
  · have hb := norm_one_sub_reciprocal_cpow_le_two hp hs
    have hzbig : 1 < ‖s‖*Real.log (p : ℝ) := by simpa only [hz] using lt_of_not_ge hsmall
    linarith

theorem radicalExponent_norm_le {R : ℝ} (hR : 1 < R) (ξ : ℝ) :
    ‖radicalExponent R ξ‖ ≤ (1+|ξ|)/Real.log R := by
  unfold radicalExponent
  rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.log_pos hR)]
  apply div_le_div_of_nonneg_right _ (Real.log_pos hR).le
  have hb := norm_add_le (1 : ℂ) (Complex.I*(ξ : ℂ))
  simpa only [norm_one,norm_mul,Complex.norm_I,Complex.norm_real,Real.norm_eq_abs,one_mul] using hb

noncomputable def radicalLocal (R ξ : ℝ) (p : ℕ) : ℝ :=
  min 1 (10*(1+|ξ|)*Real.log (p : ℝ)/Real.log R)

theorem actual_N_prime_factor_radical_bound {R : ℝ} (hR : 1 < R) (ξ : ℝ)
    {p : ℕ} (hp : p.Prime) :
    ‖1-1/((p : ℂ)^radicalExponent R ξ)‖ ≤ 2*radicalLocal R ξ p := by
  have hlog : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast hp.one_le)
  have hn := radicalExponent_norm_le hR ξ
  have hb2 := norm_one_sub_reciprocal_cpow_le_two hp.pos (radicalExponent_re_pos hR ξ).le
  have hbl := norm_one_sub_reciprocal_cpow_le_log hp.pos (radicalExponent_re_pos hR ξ).le
  have hb : ‖1-1/((p : ℂ)^radicalExponent R ξ)‖ ≤
      2*((1+|ξ|)/Real.log R)*Real.log (p : ℝ) := by
    exact hbl.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hn (by norm_num)) hlog)
  unfold radicalLocal
  rw [mul_min_of_nonneg (R := ℝ) 1 _ (by norm_num : (0 : ℝ) ≤ 2)]
  simp only [mul_one]
  apply le_min hb2
  have ht : 0 ≤ ((1+|ξ|)/Real.log R)*Real.log (p : ℝ) :=
    mul_nonneg (div_nonneg (by positivity) (Real.log_pos hR).le) hlog
  have he : 2*(10*(1+|ξ|)*Real.log (p : ℝ)/Real.log R) =
      20*(((1+|ξ|)/Real.log R)*Real.log (p : ℝ)) := by ring
  rw [he]
  nlinarith

theorem positiveLocal_correction_le_exp {p : ℝ} (hp : 1 < p) (σ : ℝ) :
    positiveLocal p σ * (1-1/p^(1+σ)) ≤ Real.exp (1/(p*(p-1))) := by
  have he : positiveLocal p σ * (1-1/p^(1+σ)) =
      (1+(1/p^σ)/(p-1))*(1-(1/p^σ)/p) := by
    unfold positiveLocal
    rw [Real.rpow_add (lt_trans zero_lt_one hp),Real.rpow_one]
    simp only [div_div,mul_comm (p^σ) (p-1),mul_comm (p^σ) p]
  rw [he]
  exact local_correction_le_exp hp

theorem positiveLocal_conductor_compensation {p : ℝ} (hp : 1 < p)
    {σ : ℝ} (hσ : 0 ≤ σ) :
    p/(p-1)*(1/p^σ) ≤ positiveLocal p σ := by
  have ht : 1/p^σ ≤ 1 := (div_le_one (Real.rpow_pos_of_pos (lt_trans zero_lt_one hp) _)).mpr
    (Real.one_le_rpow hp.le hσ)
  have hb := local_conductor_compensation hp ht
  unfold positiveLocal
  simpa only [div_div,mul_comm (p^σ) (p-1)] using hb

theorem norm_good_prime_factor_le_positiveLocal {p : ℕ} (hp : p.Prime) (s : ℂ) :
    ‖1+1/((p.totient : ℂ)*(p : ℂ)^s)‖ ≤ positiveLocal (p : ℝ) s.re := by
  have hb := norm_add_le (1 : ℂ) (1/((p.totient : ℂ)*(p : ℂ)^s))
  rw [norm_one,norm_div,norm_one,norm_mul,Complex.norm_natCast,
    Complex.norm_natCast_cpow_of_pos hp.pos] at hb
  have he : (p.totient : ℝ) = (p : ℝ)-1 := by
    rw [Nat.totient_prime hp,Nat.cast_sub hp.one_le,Nat.cast_one]
  rw [he] at hb
  exact hb

theorem radicalLocal_nonneg {R : ℝ} (hR : 1 < R) (ξ : ℝ)
    {p : ℕ} (hp : p.Prime) : 0 ≤ radicalLocal R ξ p := by
  unfold radicalLocal
  exact le_min zero_le_one (div_nonneg
    (mul_nonneg (by positivity) (Real.log_nonneg (by exact_mod_cast hp.one_le)))
    (Real.log_pos hR).le)

theorem two_pow_primeFactors_card_le_divisors {N : ℕ} (hN : 0 < N) :
    2^N.primeFactors.card ≤ N.divisors.card := by
  rw [Nat.card_divisors hN.ne',← Finset.prod_const]
  apply Finset.prod_le_prod
  · intro p hp
    exact Nat.zero_le _
  · intro p hp
    have hh := Nat.mem_primeFactors.mp hp
    have he := hh.1.factorization_pos_of_dvd hN.ne' hh.2.1
    omega

noncomputable def radicalEnvelope (R ξ : ℝ) (N : ℕ) : ℝ :=
  ∏ p ∈ N.primeFactors, radicalLocal R ξ p

/-- Distinct prime support, including nonsquarefree N; powers are not discarded. -/
theorem actual_N_prime_product_radical_bound {R : ℝ} (hR : 1 < R)
    (ξ : ℝ) {N : ℕ} (hN : 0 < N) :
    ‖∏ p ∈ N.primeFactors, (1-1/((p : ℂ)^radicalExponent R ξ))‖ ≤
      (N.divisors.card : ℝ)*radicalEnvelope R ξ N := by
  have hnrad : 0 ≤ radicalEnvelope R ξ N :=
    Finset.prod_nonneg (fun p hp => radicalLocal_nonneg hR ξ (Nat.prime_of_mem_primeFactors hp))
  calc
    _ ≤ ∏ p ∈ N.primeFactors, ‖1-1/((p : ℂ)^radicalExponent R ξ)‖ := le_of_eq (norm_prod _ _)
    _ ≤ ∏ p ∈ N.primeFactors, 2*radicalLocal R ξ p :=
      Finset.prod_le_prod (fun _ _ => norm_nonneg _)
        (fun p hp => actual_N_prime_factor_radical_bound hR ξ (Nat.prime_of_mem_primeFactors hp))
    _ = (2 : ℝ)^N.primeFactors.card*radicalEnvelope R ξ N := by
      rw [Finset.prod_mul_distrib,Finset.prod_const]
      rfl
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (by exact_mod_cast two_pow_primeFactors_card_le_divisors hN) hnrad

end GoldbachCircleMethodLocalEulerRadicalBoundsV18149
