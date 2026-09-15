import GoldbachCircleMethodRadicalCorrelationTransferV18161

set_option autoImplicit false
open scoped BigOperators Classical
namespace GoldbachCircleMethodBadPrimeResidueCountV18163

/-- Exact first-power divisibility; used below at prime moduli. -/
def exactFirstPower (p : ℕ) (z : ℤ) : Prop :=
  (p : ℤ) ∣ z ∧ ¬ (p : ℤ)^2 ∣ z

def rootParameters (p k : ℕ) : Finset ℕ :=
  ((Finset.range p).erase 0).erase (k % p)

/-- Actual representatives modulo p squared, for the forms n and p*k-n. -/
noncomputable def twoFormResidues (p k : ℕ) : Finset ℕ :=
  (Finset.range (p*p)).filter (fun n =>
    exactFirstPower p (n : ℤ) ∧ exactFirstPower p ((p : ℤ)*k-n))

theorem cross_divisibility (p : ℕ) (m n : ℤ) (hm : (p : ℤ) ∣ m) :
    (p : ℤ) ∣ n ↔ (p : ℤ) ∣ m-n := by
  constructor
  · exact fun hn => dvd_sub hm hn
  · intro hn
    simpa using dvd_sub hm hn

theorem first_power_product_iff {p : ℕ} (hp : 0 < p) (z : ℤ) :
    exactFirstPower p ((p : ℤ)*z) ↔ ¬ (p : ℤ) ∣ z := by
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast (ne_of_gt hp)
  simp only [exactFirstPower, dvd_mul_right, true_and, pow_two,
    mul_dvd_mul_iff_left hp0]

theorem difference_divisibility_iff {p t : ℕ} (k : ℕ) (ht : t < p) :
    ((p : ℤ) ∣ (k : ℤ)-t) ↔ k % p = t := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  simp only [Int.cast_sub, Int.cast_natCast, sub_eq_zero,
    ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt ht]

theorem parameter_mem_iff (p k t : ℕ) :
    t ∈ rootParameters p k ↔ t < p ∧ t ≠ 0 ∧ t ≠ k % p := by
  simp only [rootParameters, Finset.mem_erase, Finset.mem_range]
  tauto

theorem parameter_exact_iff {p t : ℕ} (hp : 0 < p) (k : ℕ) (ht : t < p) :
    t ∈ rootParameters p k ↔
      exactFirstPower p ((p : ℤ)*t) ∧
      exactFirstPower p ((p : ℤ)*k-(p : ℤ)*t) := by
  rw [parameter_mem_iff, ← mul_sub, first_power_product_iff hp,
    first_power_product_iff hp]
  rw [Int.natCast_dvd_natCast, Nat.dvd_iff_mod_eq_zero, Nat.mod_eq_of_lt ht,
    difference_divisibility_iff k ht]
  tauto

theorem residue_carrier_eq_image {p : ℕ} (hp : 0 < p) (k : ℕ) :
    twoFormResidues p k = (rootParameters p k).image (fun t => p*t) := by
  ext n
  constructor
  · intro hn
    rcases Finset.mem_filter.mp hn with ⟨hnrange, hnfirst, hnsecond⟩
    have hnlt := Finset.mem_range.mp hnrange
    have hdiv : p ∣ n := Int.natCast_dvd_natCast.mp hnfirst.1
    rcases hdiv with ⟨t, rfl⟩
    have ht : t < p := (Nat.mul_lt_mul_left hp).mp hnlt
    apply Finset.mem_image.mpr
    refine ⟨t, (parameter_exact_iff hp k ht).mpr ?_, rfl⟩
    simpa only [Nat.cast_mul] using And.intro hnfirst hnsecond
  · intro hn
    rcases Finset.mem_image.mp hn with ⟨t, htmem, rfl⟩
    have ht := (parameter_mem_iff p k t).mp htmem
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr (Nat.mul_lt_mul_of_pos_left ht.1 hp), ?_⟩
    simpa only [Nat.cast_mul] using (parameter_exact_iff hp k ht.1).mp htmem

theorem parameter_count {p : ℕ} (hp : 0 < p) (k : ℕ) :
    (rootParameters p k).card = if p ∣ k then p-1 else p-2 := by
  have hz : 0 ∈ Finset.range p := Finset.mem_range.mpr hp
  have hk : k % p ∈ Finset.range p := Finset.mem_range.mpr (Nat.mod_lt k hp)
  by_cases h : p ∣ k
  · have he : k % p = 0 := Nat.mod_eq_zero_of_dvd h
    simp [rootParameters, h, he, Finset.card_erase_of_mem hz]
  · have he : k % p ≠ 0 := by simpa [Nat.dvd_iff_mod_eq_zero] using h
    have hm : k % p ∈ (Finset.range p).erase 0 :=
      Finset.mem_erase.mpr ⟨he, hk⟩
    rw [rootParameters, Finset.card_erase_of_mem hm,
      Finset.card_erase_of_mem hz, Finset.card_range, if_neg h]
    omega

theorem residue_count {p : ℕ} (hp : 0 < p) (k : ℕ) :
    (twoFormResidues p k).card = if p ∣ k then p-1 else p-2 := by
  rw [residue_carrier_eq_image hp, Finset.card_image_of_injective]
  · exact parameter_count hp k
  · exact fun a b hab => (Nat.mul_left_cancel_iff hp).mp hab

theorem residue_density_le {p : ℕ} (hp : 0 < p) (k : ℕ) :
    ((twoFormResidues p k).card : ℝ) / (p : ℝ)^2 ≤ 1 / (p : ℝ) := by
  have hc : (twoFormResidues p k).card ≤ p := by
    rw [residue_count hp]
    split_ifs <;> omega
  have hpr : (0 : ℝ) < p := by exact_mod_cast hp
  have hcr : ((twoFormResidues p k).card : ℝ) ≤ p := by exact_mod_cast hc
  apply (div_le_iff₀ (sq_pos_of_pos hpr)).mpr
  field_simp
  nlinarith

theorem local_factor_comparison {p u v : ℝ} (hp : 0 < p)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    1+4*u*v/p ≤ (1+2*u/p)*(1+2*v/p) := by
  have huv : 2*u*v ≤ u+v := by
    have h1 := mul_nonneg hu0 (sub_nonneg.mpr hv1)
    have h2 := mul_nonneg hv0 (sub_nonneg.mpr hu1)
    nlinarith
  have hp2 : 0 < p^2 := sq_pos_of_pos hp
  apply (mul_le_mul_iff_left₀ hp2).mp
  field_simp
  nlinarith [mul_nonneg (sub_nonneg.mpr huv) (le_of_lt hp), mul_nonneg hu0 hv0]

end GoldbachCircleMethodBadPrimeResidueCountV18163
