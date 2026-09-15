import GoldbachCircleMethodHenriotArithmeticGrowthClassV18170

set_option autoImplicit false
open scoped BigOperators Classical
open GoldbachCircleMethodBadPrimeProductComparisonV18165
open GoldbachCircleMethodMertensUniformConstantsV18168
open GoldbachCircleMethodBadPrimeUniformFrequencyV18169
namespace GoldbachCircleMethodDisjointPrimeFactorCompositionV18171

def goodPrimes (m K : ℕ) : Finset ℕ :=
  (primePrefix K).filter (fun p => ¬p ∣ m)

noncomputable def goodBadProduct (R ξ η : ℝ) (m K : ℕ) : ℝ :=
  badPrimeProduct R ξ η m*
    comparisonProduct R ξ (goodPrimes m K)*comparisonProduct R η (goodPrimes m K)

theorem good_bad_disjoint (m K : ℕ) : Disjoint m.primeFactors (goodPrimes m K) := by
  apply Finset.disjoint_left.mpr
  intro p hp hg
  exact (Finset.mem_filter.mp hg).2 (Nat.dvd_of_mem_primeFactors hp)

theorem union_subset_prefix {m K X : ℕ} (hm : 0 < m) (hmX : m ≤ X) (hKX : K ≤ X) :
    m.primeFactors ∪ goodPrimes m K ⊆ primePrefix X := by
  intro p hp
  rcases Finset.mem_union.mp hp with hb | hg
  · exact primeFactors_subset_prefix hm hmX hb
  · have hk := (Finset.mem_filter.mp hg).1
    have he := Finset.mem_filter.mp hk
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr ?_, he.2⟩
    have hlt := Finset.mem_range.mp he.1
    omega

theorem comparisonProduct_union (R ξ : ℝ) {S T : Finset ℕ} (hd : Disjoint S T) :
    comparisonProduct R ξ (S ∪ T) =
      comparisonProduct R ξ S*comparisonProduct R ξ T := by
  exact Finset.prod_union hd

theorem good_bad_product_le_prefix {R : ℝ} (hR : 1 < R) (ξ η : ℝ)
    {m K X : ℕ} (hm : 0 < m) (hmX : m ≤ X) (hKX : K ≤ X) :
    goodBadProduct R ξ η m K ≤
      comparisonProduct R ξ (primePrefix X)*comparisonProduct R η (primePrefix X) := by
  let U := m.primeFactors ∪ goodPrimes m K
  have hU := union_subset_prefix hm hmX hKX
  have ht : ∀ p ∈ primePrefix X, p.Prime := fun _ hp => (Finset.mem_filter.mp hp).2
  have hu : ∀ p ∈ U, p.Prime := fun p hp => ht p (hU hp)
  have hg : ∀ p ∈ goodPrimes m K, p.Prime :=
    fun _ hp => (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2
  have hstep := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (badPrimeProduct_le_comparison hR ξ η m)
      (comparisonProduct_nonneg hR ξ hg)) (comparisonProduct_nonneg hR η hg)
  calc
    goodBadProduct R ξ η m K ≤
        (comparisonProduct R ξ m.primeFactors*comparisonProduct R η m.primeFactors)*
          comparisonProduct R ξ (goodPrimes m K)*comparisonProduct R η (goodPrimes m K) := hstep
    _ = comparisonProduct R ξ U*comparisonProduct R η U := by
      dsimp [U]
      rw [comparisonProduct_union R ξ (good_bad_disjoint m K),
        comparisonProduct_union R η (good_bad_disjoint m K)]
      ring
    _ ≤ _ := mul_le_mul (comparisonProduct_mono hR ξ hU ht)
      (comparisonProduct_mono hR η hU ht) (comparisonProduct_nonneg hR η hu)
      (comparisonProduct_nonneg hR ξ ht)

theorem good_bad_uniform_bound (D c : ℝ) (hD : 0 ≤ D)
    (hweighted : ∀ (X : ℕ), 2 ≤ X → ∀ t : ℝ, 2 ≤ t → t ≤ (X : ℝ) →
      |prefixLogMoment X t-Real.log t| ≤ D)
    (hharmonic : ∀ (X : ℕ), 2 ≤ X → ∀ t : ℝ, 2 ≤ t → t ≤ (X : ℝ) →
      |prefixHarmonicMoment X t-Real.log (Real.log t)-c| ≤ D/Real.log t)
    {m K X : ℕ} (hm : 0 < m) (hmX : m ≤ X) (hKX : K ≤ X) (hX : 2 ≤ X)
    {R : ℝ} (hR : 1 < R) (hRX : R ≤ (X : ℝ)) (ξ η : ℝ) :
    goodBadProduct R ξ η m K ≤
      (oneFrequencyConstant D c)^2*(1+|ξ|)^2*(1+|η|)^2*
        (Real.log (X : ℝ)/Real.log R)^4 := by
  have hx := uniform_frequency_bound D c hD hweighted hharmonic hX hR hRX ξ
  have hy := uniform_frequency_bound D c hD hweighted hharmonic hX hR hRX η
  have hn := comparisonProduct_nonneg hR η
    (fun _ hp => (Finset.mem_filter.mp hp).2 : ∀ p ∈ primePrefix X, p.Prime)
  have he := Real.exp_pos (2*uniformC0 D+2*uniformC1 D c)
  have hp := mul_le_mul hx hy hn (by positivity)
  calc
    goodBadProduct R ξ η m K ≤ _ := good_bad_product_le_prefix hR ξ η hm hmX hKX
    _ ≤ _ := hp
    _ = _ := by unfold oneFrequencyConstant; ring

end GoldbachCircleMethodDisjointPrimeFactorCompositionV18171

