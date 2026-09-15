import GoldbachCircleMethodBadPrimeActualWeightV18164

set_option autoImplicit false
open scoped BigOperators Classical
open GoldbachCircleMethodLocalEulerRadicalBoundsV18149
open GoldbachCircleMethodRadicalArithmeticClassV18159
open GoldbachCircleMethodBadPrimeActualWeightV18164
namespace GoldbachCircleMethodBadPrimeProductComparisonV18165

noncomputable def comparisonLocal (R ξ : ℝ) (p : ℕ) : ℝ :=
  1+2*radicalLocal R ξ p/(p : ℝ)

noncomputable def comparisonProduct (R ξ : ℝ) (S : Finset ℕ) : ℝ :=
  ∏ p ∈ S, comparisonLocal R ξ p

noncomputable def badPrimeProduct (R ξ η : ℝ) (m : ℕ) : ℝ :=
  ∏ p ∈ m.primeFactors, badPrimeFactor R ξ η p m

def primePrefix (X : ℕ) : Finset ℕ :=
  (Finset.range (X+1)).filter Nat.Prime

theorem comparisonLocal_one_le {R : ℝ} (hR : 1 < R) (ξ : ℝ)
    {p : ℕ} (hp : p.Prime) : 1 ≤ comparisonLocal R ξ p := by
  unfold comparisonLocal
  have h := radicalLocal_nonneg hR ξ hp
  have hpr : (0 : ℝ) ≤ p := Nat.cast_nonneg _
  exact le_add_of_nonneg_right (by positivity)

theorem badPrimeFactor_one_le {R : ℝ} (hR : 1 < R) (ξ η : ℝ)
    (p m : ℕ) : 1 ≤ badPrimeFactor R ξ η p m := by
  unfold badPrimeFactor
  have h1 := divisorRadicalWeight_nonneg hR ξ p
  have h2 := divisorRadicalWeight_nonneg hR η p
  exact le_add_of_nonneg_right (by positivity)

theorem badPrimeProduct_le_comparison {R : ℝ} (hR : 1 < R) (ξ η : ℝ)
    (m : ℕ) :
    badPrimeProduct R ξ η m ≤
      comparisonProduct R ξ m.primeFactors * comparisonProduct R η m.primeFactors := by
  unfold badPrimeProduct comparisonProduct
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_le_prod
  · intro p _
    exact (badPrimeFactor_one_le hR ξ η p m).trans' zero_le_one
  · intro p hp
    exact actual_bad_factor_bound hR ξ η (Nat.prime_of_mem_primeFactors hp)
      (Nat.dvd_of_mem_primeFactors hp)

theorem primeFactors_subset_prefix {m X : ℕ} (hm : 0 < m) (hmX : m ≤ X) :
    m.primeFactors ⊆ primePrefix X := by
  intro p hp
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_range.mpr ?_, Nat.prime_of_mem_primeFactors hp⟩
  have hp_le : p ≤ m := Nat.le_of_dvd hm (Nat.dvd_of_mem_primeFactors hp)
  omega

theorem comparisonProduct_mono {R : ℝ} (hR : 1 < R) (ξ : ℝ)
    {S T : Finset ℕ} (hst : S ⊆ T) (ht : ∀ p ∈ T, p.Prime) :
    comparisonProduct R ξ S ≤ comparisonProduct R ξ T := by
  unfold comparisonProduct
  apply Finset.prod_le_prod_of_subset_of_one_le hst
  · intro p hp
    exact zero_le_one.trans (comparisonLocal_one_le hR ξ (ht p (hst hp)))
  · intro p hp _
    exact comparisonLocal_one_le hR ξ (ht p hp)

theorem comparisonProduct_nonneg {R : ℝ} (hR : 1 < R) (ξ : ℝ)
    {S : Finset ℕ} (hs : ∀ p ∈ S, p.Prime) : 0 ≤ comparisonProduct R ξ S := by
  exact Finset.prod_nonneg (fun p hp => zero_le_one.trans (comparisonLocal_one_le hR ξ (hs p hp)))

theorem badPrimeProduct_le_prefix {R : ℝ} (hR : 1 < R) (ξ η : ℝ)
    {m X : ℕ} (hm : 0 < m) (hmX : m ≤ X) :
    badPrimeProduct R ξ η m ≤
      comparisonProduct R ξ (primePrefix X) * comparisonProduct R η (primePrefix X) := by
  have ht : ∀ p ∈ primePrefix X, p.Prime := fun _ hp => (Finset.mem_filter.mp hp).2
  have hs : ∀ p ∈ m.primeFactors, p.Prime := fun _ hp => Nat.prime_of_mem_primeFactors hp
  have hsub := primeFactors_subset_prefix hm hmX
  exact (badPrimeProduct_le_comparison hR ξ η m).trans
    (mul_le_mul (comparisonProduct_mono hR ξ hsub ht) (comparisonProduct_mono hR η hsub ht)
      (comparisonProduct_nonneg hR η hs) (comparisonProduct_nonneg hR ξ ht))

theorem comparisonProduct_le_exp_sum {R : ℝ} (hR : 1 < R) (ξ : ℝ)
    {S : Finset ℕ} (hs : ∀ p ∈ S, p.Prime) :
    comparisonProduct R ξ S ≤ Real.exp (∑ p ∈ S, 2*radicalLocal R ξ p/(p : ℝ)) := by
  rw [Real.exp_sum]
  apply Finset.prod_le_prod
  · intro p hp
    exact zero_le_one.trans (comparisonLocal_one_le hR ξ (hs p hp))
  · intro p _
    simpa only [comparisonLocal, add_comm] using
      Real.add_one_le_exp (2*radicalLocal R ξ p/(p : ℝ))

end GoldbachCircleMethodBadPrimeProductComparisonV18165
