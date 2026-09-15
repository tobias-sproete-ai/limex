import GoldbachCircleMethodCorrectedLocalFactorBindingV18172

set_option autoImplicit false
open scoped BigOperators Classical
open GoldbachCircleMethodBadPrimeProductComparisonV18165
namespace GoldbachCircleMethodGlobalSieveFiniteFactorV18173

/-- Residues modulo `p` on which `n * (m-n)` vanishes. The subtraction is in
`ZMod p`, matching the integer forms rather than truncated natural subtraction. -/
noncomputable def localRootResidues (p m : ℕ) : Finset ℕ :=
  (Finset.range p).filter (fun n =>
    (n : ZMod p) = 0 ∨ (m : ZMod p) - (n : ZMod p) = 0)

theorem localRootResidues_eq_pair {p : ℕ} (hp : p.Prime) (m : ℕ) :
    localRootResidues p m = {0, m % p} := by
  have hp0 := hp.pos
  ext n
  simp only [localRootResidues, Finset.mem_filter, Finset.mem_range,
    sub_eq_zero, Finset.mem_insert, Finset.mem_singleton]
  rw [ZMod.natCast_eq_zero_iff, ZMod.natCast_eq_natCast_iff']
  constructor
  · rintro ⟨hn, hzero | heq⟩
    · exact Or.inl (Nat.eq_zero_of_dvd_of_lt hzero hn)
    · right
      rw [Nat.mod_eq_of_lt hn] at heq
      exact heq.symm
  · rintro (rfl | rfl)
    · exact ⟨hp0, Or.inl (dvd_zero p)⟩
    · have hmod := Nat.mod_lt m hp0
      refine ⟨hmod, Or.inr ?_⟩
      rw [Nat.mod_eq_of_lt hmod]

/-- The two linear forms have one root modulo `p` when `p ∣ m`, and two
distinct roots otherwise. -/
theorem localRootResidues_card {p : ℕ} (hp : p.Prime) (m : ℕ) :
    (localRootResidues p m).card = if p ∣ m then 1 else 2 := by
  rw [localRootResidues_eq_pair hp]
  by_cases hm : p ∣ m
  · have hz : m % p = 0 := Nat.mod_eq_zero_of_dvd hm
    simp [hm, hz]
  · have hz : m % p ≠ 0 := by simpa [Nat.dvd_iff_mod_eq_zero] using hm
    have hnot : 0 ∉ ({m % p} : Finset ℕ) := by simpa [eq_comm] using hz
    rw [if_neg hm, Finset.card_insert_of_notMem hnot]
    simp

/-- The canonical prime prefix restricted to odd primes. -/
def oddPrimePrefix (K : ℕ) : Finset ℕ :=
  (primePrefix K).filter (fun p => 2 < p)

noncomputable def localSieveFactor (p m : ℕ) : ℝ :=
  1 - ((localRootResidues p m).card : ℝ) / (p : ℝ)

noncomputable def correctionFactor (p : ℕ) : ℝ :=
  ((p : ℝ) - 1) / ((p : ℝ) - 2)

noncomputable def finiteSieveProduct (m K : ℕ) : ℝ :=
  ∏ p ∈ oddPrimePrefix K, localSieveFactor p m

noncomputable def baselineProduct (K : ℕ) : ℝ :=
  ∏ p ∈ oddPrimePrefix K, (1 - 2 / (p : ℝ))

noncomputable def finiteCorrection (m K : ℕ) : ℝ :=
  ∏ p ∈ oddPrimePrefix K, if p ∣ m then correctionFactor p else 1

noncomputable def arithmeticFactor (m : ℕ) : ℝ :=
  ∏ p ∈ m.primeFactors.filter (fun p => 2 < p), correctionFactor p

noncomputable def oddMertensProduct (K : ℕ) : ℝ :=
  ∏ p ∈ oddPrimePrefix K, (1 - 1 / (p : ℝ))

noncomputable def finiteMertensProduct (K : ℕ) : ℝ :=
  ∏ p ∈ primePrefix K, (1 - 1 / (p : ℝ))

theorem localSieveFactor_eq {p m : ℕ} (hp : p.Prime) (hp2 : 2 < p) :
    localSieveFactor p m =
      (1 - 2 / (p : ℝ)) * (if p ∣ m then correctionFactor p else 1) := by
  rw [localSieveFactor, localRootResidues_card hp]
  by_cases hm : p ∣ m
  · simp only [hm, if_true, Nat.cast_one, correctionFactor]
    have hp0 : (p : ℝ) ≠ 0 := by positivity
    have hp2r : (2 : ℝ) < p := by exact_mod_cast hp2
    have hp20 : (p : ℝ) - 2 ≠ 0 := by linarith
    field_simp
  · simp [hm]

/-- Exact finite local correction identity on the single canonical odd-prime
prefix. -/
theorem finiteSieveProduct_eq_baseline_mul_correction (m K : ℕ) :
    finiteSieveProduct m K = baselineProduct K * finiteCorrection m K := by
  unfold finiteSieveProduct baselineProduct finiteCorrection
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  have hop := (Finset.mem_filter.mp hp).2
  have hprime := (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2
  exact localSieveFactor_eq hprime hop

theorem finiteCorrection_eq_divisor_product (m K : ℕ) :
    finiteCorrection m K =
      ∏ p ∈ (oddPrimePrefix K).filter (fun p => p ∣ m), correctionFactor p := by
  unfold finiteCorrection
  exact (Finset.prod_filter (s := oddPrimePrefix K)
    (fun p => p ∣ m) correctionFactor).symm

theorem finiteSieveProduct_exact_identity (m K : ℕ) :
    finiteSieveProduct m K = baselineProduct K *
      (∏ p ∈ (oddPrimePrefix K).filter (fun p => p ∣ m), correctionFactor p) := by
  rw [finiteSieveProduct_eq_baseline_mul_correction,
    finiteCorrection_eq_divisor_product]

theorem correctionFactor_one_le {p : ℕ} (hp2 : 2 < p) :
    1 ≤ correctionFactor p := by
  have hp2r : (2 : ℝ) < p := by exact_mod_cast hp2
  have hd : (0 : ℝ) < (p : ℝ) - 2 := by linarith
  rw [correctionFactor]
  apply (le_div_iff₀ hd).mpr
  linarith

theorem bad_odd_prefix_subset_arithmetic {m K : ℕ} (hm : 0 < m) :
    (oddPrimePrefix K).filter (fun p => p ∣ m) ⊆
      m.primeFactors.filter (fun p => 2 < p) := by
  intro p hp
  rcases Finset.mem_filter.mp hp with ⟨hop, hpm⟩
  rcases Finset.mem_filter.mp hop with ⟨hpp, hp2⟩
  have hprime := (Finset.mem_filter.mp hpp).2
  exact Finset.mem_filter.mpr
    ⟨Nat.mem_primeFactors.mpr ⟨hprime, hpm, hm.ne'⟩, hp2⟩

theorem finiteCorrection_le_arithmeticFactor {m K : ℕ} (hm : 0 < m) :
    finiteCorrection m K ≤ arithmeticFactor m := by
  rw [finiteCorrection_eq_divisor_product]
  unfold arithmeticFactor
  apply Finset.prod_le_prod_of_subset_of_one_le (bad_odd_prefix_subset_arithmetic hm)
  · intro p hp
    exact zero_le_one.trans
      (correctionFactor_one_le (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2)
  · intro p hp _
    exact correctionFactor_one_le (Finset.mem_filter.mp hp).2

theorem baseline_local_nonneg {p : ℕ} (hp2 : 2 < p) :
    0 ≤ 1 - 2 / (p : ℝ) := by
  have hp0 : (0 : ℝ) < p := by positivity
  have h2p : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.le_of_lt hp2)
  exact sub_nonneg.mpr ((div_le_one hp0).mpr h2p)

theorem baseline_local_le_square {p : ℕ} (hp2 : 2 < p) :
    1 - 2 / (p : ℝ) ≤ (1 - 1 / (p : ℝ))^2 := by
  have hp0 : (p : ℝ) ≠ 0 := by positivity
  field_simp
  linarith

theorem baselineProduct_le_oddMertens_sq (K : ℕ) :
    baselineProduct K ≤ (oddMertensProduct K)^2 := by
  unfold baselineProduct oddMertensProduct
  calc
    (∏ p ∈ oddPrimePrefix K, (1 - 2 / (p : ℝ))) ≤
        ∏ p ∈ oddPrimePrefix K, (1 - 1 / (p : ℝ))^2 := by
      apply Finset.prod_le_prod
      · intro p hp
        exact baseline_local_nonneg (Finset.mem_filter.mp hp).2
      · intro p hp
        exact baseline_local_le_square (Finset.mem_filter.mp hp).2
    _ = (∏ p ∈ oddPrimePrefix K, (1 - 1 / (p : ℝ)))^2 := by
      rw [Finset.prod_pow]

theorem primePrefix_eq_insert_two_odd {K : ℕ} (hK : 2 ≤ K) :
    primePrefix K = insert 2 (oddPrimePrefix K) := by
  ext p
  constructor
  · intro hp
    have hpr := (Finset.mem_filter.mp hp).2
    have hp2le := hpr.two_le
    by_cases he : p = 2
    · exact Finset.mem_insert.mpr (Or.inl he)
    · apply Finset.mem_insert.mpr
      exact Or.inr (Finset.mem_filter.mpr ⟨hp, by omega⟩)
  · intro hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_range.mpr (by omega), Nat.prime_two⟩
    · exact (Finset.mem_filter.mp hp).1

theorem oddMertensProduct_eq_two_mul {K : ℕ} (hK : 2 ≤ K) :
    oddMertensProduct K = 2 * finiteMertensProduct K := by
  have hnot : 2 ∉ oddPrimePrefix K := by simp [oddPrimePrefix]
  unfold finiteMertensProduct
  rw [primePrefix_eq_insert_two_odd hK, Finset.prod_insert hnot]
  unfold oddMertensProduct
  ring

theorem finiteCorrection_nonneg (m K : ℕ) : 0 ≤ finiteCorrection m K := by
  unfold finiteCorrection
  apply Finset.prod_nonneg
  intro p hp
  by_cases hpm : p ∣ m
  · simp only [hpm, if_true]
    exact zero_le_one.trans (correctionFactor_one_le (Finset.mem_filter.mp hp).2)
  · simp [hpm]

/-- Entirely finite sieve-factor comparison. No Mertens estimate is used. -/
theorem finiteSieveProduct_le_four_mul
    {m K : ℕ} (hm : 0 < m) (hK : 2 ≤ K) :
    finiteSieveProduct m K ≤
      4 * arithmeticFactor m * (finiteMertensProduct K)^2 := by
  rw [finiteSieveProduct_eq_baseline_mul_correction]
  have hmul := mul_le_mul (baselineProduct_le_oddMertens_sq K)
    (finiteCorrection_le_arithmeticFactor hm) (finiteCorrection_nonneg m K)
    (sq_nonneg (oddMertensProduct K))
  calc
    baselineProduct K * finiteCorrection m K ≤
        (oddMertensProduct K)^2 * arithmeticFactor m := hmul
    _ = 4 * arithmeticFactor m * (finiteMertensProduct K)^2 := by
      rw [oddMertensProduct_eq_two_mul hK]
      ring

end GoldbachCircleMethodGlobalSieveFiniteFactorV18173
