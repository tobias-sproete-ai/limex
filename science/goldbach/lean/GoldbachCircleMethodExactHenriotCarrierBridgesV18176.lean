import GoldbachCircleMethodConditionalSieveCorrelationCompositionV18175

set_option autoImplicit false
open scoped BigOperators Classical
open GoldbachCircleMethodBadPrimeProductComparisonV18165
open GoldbachCircleMethodGlobalSieveFiniteFactorV18173
namespace GoldbachCircleMethodExactHenriotCarrierBridgesV18176

/-- The natural half-window is exactly the real interval `M/2 < n ≤ M`,
also when `M` is odd. -/
theorem mem_half_window_real_iff {M n : ℕ} :
    n ∈ Finset.Ioc (M / 2) M ↔
      (M : ℝ) / 2 < (n : ℝ) ∧ (n : ℝ) ≤ (M : ℝ) := by
  rw [Finset.mem_Ioc]
  constructor
  · rintro ⟨hlow, hhigh⟩
    have htwice : M < 2 * n := by omega
    constructor
    · apply (div_lt_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
      exact_mod_cast (show M < n * 2 by simpa [mul_comm] using htwice)
    · exact_mod_cast hhigh
  · rintro ⟨hlow, hhigh⟩
    have htwiceR : (M : ℝ) < 2 * (n : ℝ) := by linarith
    have htwice : M < 2 * n := by exact_mod_cast htwiceR
    constructor
    · omega
    · exact_mod_cast hhigh

/-- The canonical prime prefix at the natural half cutoff has the precise
real cutoff used by the source interval. -/
theorem mem_primePrefix_half_iff {M p : ℕ} :
    p ∈ primePrefix (M / 2) ↔
      p.Prime ∧ (p : ℝ) ≤ (M : ℝ) / 2 := by
  simp only [primePrefix, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨hp, hprime⟩
    refine ⟨hprime, ?_⟩
    have hle : p ≤ M / 2 := by omega
    have htwice : 2 * p ≤ M := by omega
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
    exact_mod_cast (show p * 2 ≤ M by simpa [mul_comm] using htwice)
  · rintro ⟨hprime, hle⟩
    have htwiceR : (p : ℝ) * 2 ≤ (M : ℝ) := by linarith
    have htwice : p * 2 ≤ M := by exact_mod_cast htwiceR
    exact ⟨by omega, hprime⟩

/-- On the declared source window, both polynomial values are positive and
integer absolute value agrees with natural subtraction. -/
theorem half_window_positive_subtraction {M m n : ℕ}
    (hM : 0 < M) (hmm : 5 * M ≤ 4 * m)
    (hn : n ∈ Finset.Ioc (M / 2) M) :
    0 < n ∧ n < m ∧
      Int.natAbs ((m : ℤ) - (n : ℤ)) = m - n := by
  have hn' := Finset.mem_Ioc.mp hn
  have hMm : M < m := by omega
  have hnm : n ≤ m := hn'.2.trans hMm.le
  refine ⟨by omega, hn'.2.trans_lt hMm, ?_⟩
  have heq : (m : ℤ) - (n : ℤ) = ((m - n : ℕ) : ℤ) := by omega
  rw [heq]
  simp

/-- For a prime modulus, the disjunctive root carrier already used by V173 is
exactly the zero set of the product of the two linear forms. -/
theorem localRootResidues_eq_product_filter {p : ℕ} (hp : p.Prime) (m : ℕ) :
    localRootResidues p m =
      (Finset.range p).filter (fun n : ℕ =>
        (n : ZMod p) * ((m : ZMod p) - (n : ZMod p)) = 0) := by
  let _ : Fact p.Prime := ⟨hp⟩
  unfold localRootResidues
  ext n
  simp only [Finset.mem_filter, Finset.mem_range, and_congr_right_iff]
  intro _
  exact mul_eq_zero.symm

/-- A finite sufficient size condition for the source coefficient-norm
constraint.  The constant remains an explicit parameter. -/
theorem source_coefficient_norm_bound {C₀ : ℝ} {M m : ℕ}
    (hC₀ : 0 ≤ C₀) (hM : 4 ≤ M) (hupper : 4 * m ≤ 7 * M)
    (hsize : 8 * C₀^2 ≤ (M : ℝ)) :
    C₀ * Real.sqrt ((m : ℝ) + 1) ≤ (M : ℝ) / 2 := by
  have hmNat : m + 1 ≤ 2 * M := by omega
  have hmReal : (m : ℝ) + 1 ≤ 2 * (M : ℝ) := by exact_mod_cast hmNat
  have hCsize : C₀^2 ≤ (M : ℝ) / 8 := by linarith
  have hprod := mul_le_mul hCsize hmReal (by positivity : (0 : ℝ) ≤ m + 1)
    (by positivity : (0 : ℝ) ≤ (M : ℝ) / 8)
  have hsqrt : 0 ≤ Real.sqrt ((m : ℝ) + 1) := Real.sqrt_nonneg _
  apply (sq_le_sq₀ (mul_nonneg hC₀ hsqrt) (by positivity)).mp
  rw [mul_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ m + 1)]
  nlinarith

theorem sqrt_half_lt_half {M : ℕ} (hM : 2 < M) :
    Real.sqrt ((M : ℝ) / 2) < (M : ℝ) / 2 := by
  apply Real.sqrt_lt_self_iff.mpr
  exact (lt_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr (by exact_mod_cast hM)

theorem epsilon_lt_source_threshold : (1 : ℝ) / 1600 < 1 / 800 := by
  norm_num

end GoldbachCircleMethodExactHenriotCarrierBridgesV18176
