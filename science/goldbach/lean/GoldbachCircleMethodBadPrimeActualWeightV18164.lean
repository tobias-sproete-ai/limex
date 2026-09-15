import GoldbachCircleMethodBadPrimeResidueCountV18163

set_option autoImplicit false
open scoped BigOperators Classical
open GoldbachCircleMethodBadPrimeResidueCountV18163
open GoldbachCircleMethodLocalEulerRadicalBoundsV18149
open GoldbachCircleMethodRadicalArithmeticClassV18159
namespace GoldbachCircleMethodBadPrimeActualWeightV18164

noncomputable def actualBadPrimeResidues (p m : ℕ) : Finset ℕ :=
  (Finset.range (p*p)).filter (fun n =>
    exactFirstPower p (n : ℤ) ∧ exactFirstPower p ((m : ℤ)-n))

theorem actual_carrier_eq {p m : ℕ} (hm : p ∣ m) :
    actualBadPrimeResidues p m = twoFormResidues p (m/p) := by
  have he : (p : ℤ)*((m/p : ℕ) : ℤ) = m := by exact_mod_cast Nat.mul_div_cancel' hm
  simp only [actualBadPrimeResidues, twoFormResidues, he]

theorem square_divides_iff_quotient {p m : ℕ} (hp : 0 < p) (hm : p ∣ m) :
    p^2 ∣ m ↔ p ∣ m/p := by
  have he : m = p*(m/p) := (Nat.mul_div_cancel' hm).symm
  conv_lhs => rw [he, pow_two]
  exact Nat.mul_dvd_mul_iff_left hp

theorem actual_count {p m : ℕ} (hp : 0 < p) (hm : p ∣ m) :
    (actualBadPrimeResidues p m).card = if p^2 ∣ m then p-1 else p-2 := by
  rw [actual_carrier_eq hm, residue_count hp]
  simp only [← square_divides_iff_quotient hp hm]

theorem actual_density {p m : ℕ} (hp : p.Prime) (hm : p ∣ m) :
    ((actualBadPrimeResidues p m).card : ℝ)/(p : ℝ)^2 =
      if p^2 ∣ m then ((p : ℝ)-1)/(p : ℝ)^2
      else ((p : ℝ)-2)/(p : ℝ)^2 := by
  rw [actual_count hp.pos hm]
  split_ifs
  · rw [Nat.cast_sub hp.one_le]; norm_num
  · rw [Nat.cast_sub hp.two_le]; norm_num

theorem actual_density_le {p m : ℕ} (hp : 0 < p) (hm : p ∣ m) :
    ((actualBadPrimeResidues p m).card : ℝ)/(p : ℝ)^2 ≤ 1/(p : ℝ) := by
  rw [actual_carrier_eq hm]
  exact residue_density_le hp _

noncomputable def badPrimeFactor (R ξ η : ℝ) (p m : ℕ) : ℝ :=
  1 + divisorRadicalWeight R ξ p * divisorRadicalWeight R η p *
    (((actualBadPrimeResidues p m).card : ℝ)/(p : ℝ)^2)

theorem divisorRadicalWeight_prime (R ξ : ℝ) {p : ℕ} (hp : p.Prime) :
    divisorRadicalWeight R ξ p = 2*radicalLocal R ξ p := by
  simpa using divisorRadicalWeight_prime_power R ξ (k := 1) hp (by norm_num)

theorem actual_bad_factor_bound {R : ℝ} (hR : 1 < R) (ξ η : ℝ)
    {p m : ℕ} (hp : p.Prime) (hm : p ∣ m) :
    badPrimeFactor R ξ η p m ≤
      (1+2*radicalLocal R ξ p/(p : ℝ))*
      (1+2*radicalLocal R η p/(p : ℝ)) := by
  have hpr : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hu0 := radicalLocal_nonneg hR ξ hp
  have hv0 := radicalLocal_nonneg hR η hp
  have hu1 : radicalLocal R ξ p ≤ 1 := min_le_left _ _
  have hv1 : radicalLocal R η p ≤ 1 := min_le_left _ _
  have hc := mul_le_mul_of_nonneg_left (actual_density_le hp.pos hm)
    (mul_nonneg (divisorRadicalWeight_nonneg hR ξ p)
      (divisorRadicalWeight_nonneg hR η p))
  rw [divisorRadicalWeight_prime R ξ hp, divisorRadicalWeight_prime R η hp] at hc
  have hstep : badPrimeFactor R ξ η p m ≤
      1+4*radicalLocal R ξ p*radicalLocal R η p/(p : ℝ) := by
    unfold badPrimeFactor
    rw [divisorRadicalWeight_prime R ξ hp, divisorRadicalWeight_prime R η hp]
    convert add_le_add_left hc 1 using 1 <;> first | rfl | ring
  exact hstep.trans (local_factor_comparison hpr hu0 hu1 hv0 hv1)

theorem prime_two_boundary (m : ℕ) (hm : 2 ∣ m) (hm4 : ¬4 ∣ m) :
    actualBadPrimeResidues 2 m = ∅ := by
  apply Finset.card_eq_zero.mp
  simpa [hm4] using actual_count (by norm_num : 0<2) hm

end GoldbachCircleMethodBadPrimeActualWeightV18164
