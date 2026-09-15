import GoldbachCircleMethodSupportedResidualParsevalV18190
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.NumberTheory.ArithmeticFunction.Misc

namespace GoldbachCircleMethodDivisorSubpowerExistenceV18191

open scoped BigOperators
open Finset Filter

/-- The elementary finite geometric estimate used for the finitely many
small prime factors. -/
theorem geometric_index_mul_pow_le_inv
    {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) (k : ℕ) :
    (k + 1 : ℝ) * x ^ k ≤ (1 - x)⁻¹ := by
  calc
    (k + 1 : ℝ) * x ^ k = ∑ _j ∈ range (k + 1), x ^ k := by simp
    _ ≤ ∑ j ∈ range (k + 1), x ^ j := by
      exact sum_le_sum fun j hj ↦
        pow_le_pow_of_le_one hx0 hx1.le (by simpa using hj)
    _ ≤ (1 - x)⁻¹ := by
      rw [← one_div]
      apply (le_div_iff₀ (sub_pos.mpr hx1)).2
      rw [geom_sum_mul_neg]
      exact sub_le_self _ (pow_nonneg hx0 _)

/-- A uniform natural threshold beyond which every real `eps`-power is at
least two. -/
theorem exists_nat_rpow_threshold {eps : ℝ} (heps : 0 < eps) :
    ∃ P : ℕ, ∀ p : ℕ, P ≤ p → (2 : ℝ) ≤ (p : ℝ) ^ eps := by
  have hlim : Tendsto (fun p : ℕ ↦ (p : ℝ) ^ eps) atTop atTop :=
    (tendsto_rpow_atTop heps).comp tendsto_natCast_atTop_atTop
  rw [tendsto_atTop_atTop] at hlim
  obtain ⟨P, hP⟩ := hlim 2
  exact ⟨P, fun p hp ↦ hP p hp⟩

private theorem nat_succ_le_two_pow (k : ℕ) : k + 1 ≤ 2 ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
      calc
        k + 1 + 1 ≤ 2 * (k + 1) := by omega
        _ ≤ 2 * 2 ^ k := Nat.mul_le_mul_left 2 ih
        _ = 2 ^ (k + 1) := by rw [pow_succ]; omega

/-- The finite correction attached to a prime below the threshold. -/
noncomputable def smallPrimeFactor (eps : ℝ) (p : ℕ) : ℝ :=
  (1 - (p : ℝ) ^ (-eps))⁻¹

/-- The product of all small-prime corrections. -/
noncomputable def divisorSubpowerConstant (eps : ℝ) (P : ℕ) : ℝ :=
  ∏ p ∈ (range P).filter Nat.Prime, smallPrimeFactor eps p

private theorem smallPrimeFactor_one_le
    {eps : ℝ} (heps : 0 < eps) {p : ℕ} (hp : p.Prime) :
    1 ≤ smallPrimeFactor eps p := by
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
  have hx0 : 0 ≤ (p : ℝ) ^ (-eps) :=
    Real.rpow_nonneg (le_trans zero_le_one hp1.le) _
  have hx1 : (p : ℝ) ^ (-eps) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg hp1 (neg_neg_of_pos heps)
  simpa [smallPrimeFactor] using
    (one_le_inv_iff₀.mpr ⟨sub_pos.mpr hx1, by linarith [hx0]⟩)

private theorem small_prime_factor_bound
    {eps : ℝ} (heps : 0 < eps) {p k : ℕ} (hp : p.Prime) :
    (k + 1 : ℝ) ≤ smallPrimeFactor eps p * (p : ℝ) ^ (eps * (k : ℝ)) := by
  have hp0 : 0 ≤ (p : ℝ) := by positivity
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
  have hp0' : 0 < (p : ℝ) := lt_trans zero_lt_one hp1
  have hx0 : 0 ≤ (p : ℝ) ^ (-eps) := Real.rpow_nonneg hp0 _
  have hx1 : (p : ℝ) ^ (-eps) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg hp1 (neg_neg_of_pos heps)
  have hgeom := geometric_index_mul_pow_le_inv hx0 hx1 k
  have hpow : 0 < (p : ℝ) ^ (eps * (k : ℝ)) := Real.rpow_pos_of_pos hp0' _
  apply (div_le_iff₀ hpow).mp
  calc
    (k + 1 : ℝ) / (p : ℝ) ^ (eps * (k : ℝ)) =
        (k + 1 : ℝ) * (p : ℝ) ^ (-(eps * (k : ℝ))) := by
          rw [div_eq_mul_inv, Real.rpow_neg hp0]
    _ = (k + 1 : ℝ) * ((p : ℝ) ^ (-eps)) ^ k := by
          rw [← Real.rpow_mul_natCast hp0]
          congr 2
          ring
    _ ≤ smallPrimeFactor eps p := by simpa [smallPrimeFactor] using hgeom

private theorem large_prime_factor_bound
    {eps : ℝ} {p k : ℕ} (hlarge : (2 : ℝ) ≤ (p : ℝ) ^ eps) :
    (k + 1 : ℝ) ≤ (p : ℝ) ^ (eps * (k : ℝ)) := by
  calc
    (k + 1 : ℝ) ≤ ((2 ^ k : ℕ) : ℝ) := by exact_mod_cast nat_succ_le_two_pow k
    _ = (2 : ℝ) ^ k := by norm_num
    _ ≤ ((p : ℝ) ^ eps) ^ k := pow_le_pow_left₀ (by positivity) hlarge k
    _ = (p : ℝ) ^ (eps * (k : ℝ)) := by
      rw [Real.rpow_mul_natCast (by positivity)]

private noncomputable def localConstant (eps : ℝ) (P p : ℕ) : ℝ :=
  if p < P then smallPrimeFactor eps p else 1

private theorem local_factor_bound
    {eps : ℝ} (heps : 0 < eps) {P p k : ℕ}
    (hP : ∀ q : ℕ, P ≤ q → (2 : ℝ) ≤ (q : ℝ) ^ eps)
    (hp : p.Prime) :
    (k + 1 : ℝ) ≤
      localConstant eps P p * (p : ℝ) ^ (eps * (k : ℝ)) := by
  by_cases hsmall : p < P
  · simpa [localConstant, hsmall] using small_prime_factor_bound heps hp (k := k)
  · simp only [localConstant, hsmall, if_false, one_mul]
    exact large_prime_factor_bound (hP p (Nat.le_of_not_gt hsmall))

private theorem localConstant_product_le
    {eps : ℝ} (heps : 0 < eps) (P n : ℕ) :
    ∏ p ∈ n.primeFactors, localConstant eps P p ≤ divisorSubpowerConstant eps P := by
  classical
  let s := n.primeFactors.filter fun p ↦ p < P
  let t := (range P).filter Nat.Prime
  have hrewrite :
      ∏ p ∈ n.primeFactors, localConstant eps P p =
        ∏ p ∈ s, smallPrimeFactor eps p := by
    simpa [s, localConstant] using
      (Finset.prod_filter (s := n.primeFactors) (fun p ↦ p < P)
        (smallPrimeFactor eps)).symm
  rw [hrewrite]
  apply prod_le_prod_of_subset_of_one_le
  · intro p hp
    dsimp [s] at hp
    simp only [mem_filter] at hp
    simp only [mem_filter, mem_range]
    exact ⟨hp.2, Nat.prime_of_mem_primeFactors hp.1⟩
  · intro p hp
    dsimp [s] at hp
    exact le_trans (by norm_num)
      (smallPrimeFactor_one_le heps (Nat.prime_of_mem_primeFactors (mem_filter.mp hp).1))
  · intro p hp _
    simp only [mem_filter] at hp
    exact smallPrimeFactor_one_le heps hp.2

private theorem divisorSubpowerConstant_one_le
    {eps : ℝ} (heps : 0 < eps) (P : ℕ) :
    1 ≤ divisorSubpowerConstant eps P := by
  classical
  apply one_le_prod
  intro p hp
  simp only [mem_filter] at hp
  exact smallPrimeFactor_one_le heps hp.2

/-- The divisor-count function is bounded by every fixed positive real power,
with a constant depending only on that power. -/
theorem exists_divisors_card_le_const_mul_rpow {eps : ℝ} (heps : 0 < eps) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ n : ℕ, 0 < n →
      (n.divisors.card : ℝ) ≤ B * (n : ℝ) ^ eps := by
  classical
  obtain ⟨P, hP⟩ := exists_nat_rpow_threshold heps
  refine ⟨divisorSubpowerConstant eps P, divisorSubpowerConstant_one_le heps P, ?_⟩
  intro n hn
  have hn0 : n ≠ 0 := Nat.ne_of_gt hn
  rw [Nat.card_divisors hn0]
  push_cast
  have hlocal :
      ∏ p ∈ n.primeFactors, ((n.factorization p : ℝ) + 1) ≤
        ∏ p ∈ n.primeFactors,
          localConstant eps P p *
            (p : ℝ) ^ (eps * (n.factorization p : ℝ)) := by
    gcongr with p hp
    simpa only [Nat.cast_add, Nat.cast_one] using
      (local_factor_bound heps hP (Nat.prime_of_mem_primeFactors hp)
        (k := n.factorization p))
  have hpow :
      ∏ p ∈ n.primeFactors, (p : ℝ) ^ (eps * (n.factorization p : ℝ)) =
        (n : ℝ) ^ eps := by
    calc
      ∏ p ∈ n.primeFactors, (p : ℝ) ^ (eps * (n.factorization p : ℝ)) =
          ∏ p ∈ n.primeFactors, ((p : ℝ) ^ n.factorization p) ^ eps := by
            apply prod_congr rfl
            intro p hp
            rw [mul_comm eps, Real.rpow_mul (by positivity), Real.rpow_natCast]
      _ = (∏ p ∈ n.primeFactors, (p : ℝ) ^ n.factorization p) ^ eps := by
            apply Real.finsetProd_rpow
            intro p hp
            positivity
      _ = (n : ℝ) ^ eps := by
            congr 1
            exact_mod_cast (Nat.prod_primeFactors_pow_factorization hn0).symm
  calc
    ∏ p ∈ n.primeFactors, ((n.factorization p : ℝ) + 1) ≤
        ∏ p ∈ n.primeFactors,
          localConstant eps P p *
            (p : ℝ) ^ (eps * (n.factorization p : ℝ)) := hlocal
    _ = (∏ p ∈ n.primeFactors, localConstant eps P p) *
          (∏ p ∈ n.primeFactors,
            (p : ℝ) ^ (eps * (n.factorization p : ℝ))) := by
          rw [prod_mul_distrib]
    _ ≤ divisorSubpowerConstant eps P *
          (∏ p ∈ n.primeFactors,
            (p : ℝ) ^ (eps * (n.factorization p : ℝ))) := by
          gcongr
          exact localConstant_product_le heps P n
    _ = divisorSubpowerConstant eps P * (n : ℝ) ^ eps := by rw [hpow]

/-- Immediate discharge of V170's divisor premise.  The selected constant is
fixed before the scale and both frequencies. -/
theorem exists_uniform_pairWeight_subpower_bound {eps : ℝ} (heps : 0 < eps) :
    ∃ B : ℝ, 1 ≤ B ∧
      ∀ {R : ℝ}, 1 < R → ∀ (xi eta : ℝ) {s t : ℕ}, 0 < s → 0 < t →
        GoldbachCircleMethodHenriotArithmeticGrowthClassV18170.pairWeight R xi eta s t ≤
          B ^ 2 * ((s * t : ℕ) : ℝ) ^ eps := by
  obtain ⟨B, hB, hdivisor⟩ := exists_divisors_card_le_const_mul_rpow heps
  refine ⟨B, hB, ?_⟩
  intro R hR xi eta s t hs ht
  exact GoldbachCircleMethodHenriotArithmeticGrowthClassV18170.pairWeight_subpower_bound
    B eps (zero_le_one.trans hB) hdivisor hR xi eta hs ht

end GoldbachCircleMethodDivisorSubpowerExistenceV18191
