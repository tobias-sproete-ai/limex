import GoldbachCircleMethodFinitePrimeProductFloorV1838
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.GCD.BigOperators

/-!
# V1.8.39: squarefree coefficient binding

This file identifies the finite subset coefficients from V1.8.38 with Möbius/totient
coefficients on an exactly matched finite divisor carrier.  It does not identify that carrier
with a Ramanujan prefix or a singular series.
-/

open scoped BigOperators

namespace GoldbachCircleMethodSquarefreeCoefficientBindingV1839

open GoldbachCircleMethodFinitePrimeProductFloorV1838

/-- Exact divisor image of the bounded bad-prime subset carrier. -/
def boundedArithmeticDivisors (N R H : ℕ) : Finset ℕ :=
  (Finset.range (H + 1)).filter fun d =>
    Squarefree d ∧ Nat.Coprime d N ∧ d.primeFactors ⊆ badPrimes N R

private theorem badPrime_prime {N R p : ℕ} (hp : p ∈ badPrimes N R) : p.Prime :=
  (Finset.mem_filter.mp hp).2.1

private theorem badPrime_not_dvd {N R p : ℕ} (hp : p ∈ badPrimes N R) : ¬p ∣ N :=
  (Finset.mem_filter.mp hp).2.2

/-- A product of a subset of the exact bad-prime carrier is squarefree. -/
theorem subsetProduct_squarefree {N R : ℕ} {s : Finset ℕ}
    (hs : s ⊆ badPrimes N R) : Squarefree (∏ p ∈ s, p) := by
  refine Finset.squarefree_prod_of_pairwise_isCoprime (fun _ hp _ hq hpq => ?_)
    (fun p hp => (badPrime_prime (hs hp)).squarefree)
  simp only [← Nat.coprime_iff_isRelPrime]
  exact (Nat.coprime_primes (badPrime_prime (hs hp)) (badPrime_prime (hs hq))).mpr hpq

/-- A product of bad primes is coprime to `N`. -/
theorem subsetProduct_coprime {N R : ℕ} {s : Finset ℕ}
    (hs : s ⊆ badPrimes N R) : Nat.Coprime (∏ p ∈ s, p) N := by
  rw [Nat.coprime_prod_left_iff]
  intro p hp
  exact (badPrime_prime (hs hp)).coprime_iff_not_dvd.mpr (badPrime_not_dvd (hs hp))

/-- Prime factorization inverts the product map on a bad-prime subset. -/
theorem subsetProduct_primeFactors {N R : ℕ} {s : Finset ℕ}
    (hs : s ⊆ badPrimes N R) : (∏ p ∈ s, p).primeFactors = s := by
  exact Nat.primeFactors_prod fun p hp => badPrime_prime (hs hp)

private theorem totient_subsetProduct {N R : ℕ} {s : Finset ℕ}
    (hs : s ⊆ badPrimes N R) :
    Nat.totient (∏ p ∈ s, p) = ∏ p ∈ s, (p - 1) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert p s hp ih =>
      have hpPrime : p.Prime := badPrime_prime (hs (Finset.mem_insert_self p s))
      have hsSubset : s ⊆ badPrimes N R := fun q hq => hs (Finset.mem_insert_of_mem hq)
      have hCoprime : Nat.Coprime p (∏ q ∈ s, q) := by
        rw [Nat.coprime_prod_right_iff]
        intro q hq
        exact (Nat.coprime_primes hpPrime (badPrime_prime (hsSubset hq))).mpr
          (fun hpq => hp (hpq ▸ hq))
      rw [Finset.prod_insert hp, Nat.totient_mul hCoprime, Nat.totient_prime hpPrime,
        ih hsSubset, Finset.prod_insert hp]

/-- Each signed subset coefficient is exactly its Möbius/totient coefficient. -/
theorem signedSubsetWeight_eq_moebius_totient {N R : ℕ} {s : Finset ℕ}
    (hs : s ⊆ badPrimes N R) :
    signedSubsetWeight s =
      (((ArithmeticFunction.moebius (∏ p ∈ s, p) : ℤ) : ℝ) /
        (((Nat.totient (∏ p ∈ s, p) : ℕ) : ℝ) ^ 2)) := by
  have hPrime : ∀ p ∈ s, p.Prime := fun p hp => badPrime_prime (hs hp)
  have hMuInt :
      ArithmeticFunction.moebius (∏ p ∈ s, p) =
        ∏ p ∈ s, ArithmeticFunction.moebius p :=
    ArithmeticFunction.isMultiplicative_moebius.map_prod_of_prime s hPrime
  have hMuReal :
      (((ArithmeticFunction.moebius (∏ p ∈ s, p) : ℤ) : ℝ)) =
        ∏ p ∈ s, (-1 : ℝ) := by
    rw [hMuInt]
    push_cast
    apply Finset.prod_congr rfl
    intro p hp
    rw [ArithmeticFunction.moebius_apply_prime (hPrime p hp)]
    norm_num
  have hPhi := totient_subsetProduct hs
  rw [signedSubsetWeight, hMuReal, hPhi]
  simp only [primeWeight]
  calc
    (∏ p ∈ s, -(1 / (((p - 1 : ℕ) : ℝ) ^ 2))) =
        ∏ p ∈ s, ((-1 : ℝ) / (((p - 1 : ℕ) : ℝ) ^ 2)) := by
          apply Finset.prod_congr rfl
          intro p _
          ring
    _ = (∏ p ∈ s, (-1 : ℝ)) /
        (∏ p ∈ s, (((p - 1 : ℕ) : ℝ) ^ 2)) := by
          rw [Finset.prod_div_distrib]
    _ = (∏ p ∈ s, (-1 : ℝ)) /
        ((∏ p ∈ s, (((p - 1 : ℕ) : ℝ))) ^ 2) := by
          rw [Finset.prod_pow]
    _ = (∏ p ∈ s, (-1 : ℝ)) /
        ((((∏ p ∈ s, (p - 1) : ℕ) : ℝ)) ^ 2) := by
          norm_cast

private theorem subsetProduct_mem_boundedArithmeticDivisors {N R H : ℕ}
    {s : Finset ℕ} (hs : s ∈ boundedBadPrimeSubsets N R H) :
    (∏ p ∈ s, p) ∈ boundedArithmeticDivisors N R H := by
  have hsData := Finset.mem_filter.mp hs
  have hsSubset : s ⊆ badPrimes N R := Finset.mem_powerset.mp hsData.1
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hsData.2), ?_⟩
  exact ⟨subsetProduct_squarefree hsSubset, subsetProduct_coprime hsSubset,
    by simpa [subsetProduct_primeFactors hsSubset] using hsSubset⟩

private theorem primeFactors_mem_boundedBadPrimeSubsets {N R H d : ℕ}
    (hd : d ∈ boundedArithmeticDivisors N R H) :
    d.primeFactors ∈ boundedBadPrimeSubsets N R H := by
  have hdData := (Finset.mem_filter.mp hd)
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_powerset.mpr hdData.2.2.2, ?_⟩
  rw [Nat.prod_primeFactors_of_squarefree hdData.2.1]
  exact Nat.le_of_lt_succ (Finset.mem_range.mp hdData.1)

/-- Explicit bijection between bounded prime subsets and their exact arithmetic divisor image. -/
noncomputable def boundedSubsetProductEquiv (N R H : ℕ) :
    {s // s ∈ boundedBadPrimeSubsets N R H} ≃
      {d // d ∈ boundedArithmeticDivisors N R H} where
  toFun s := ⟨∏ p ∈ s.1, p, subsetProduct_mem_boundedArithmeticDivisors s.2⟩
  invFun d := ⟨d.1.primeFactors, primeFactors_mem_boundedBadPrimeSubsets d.2⟩
  left_inv s := by
    apply Subtype.ext
    exact subsetProduct_primeFactors
      (Finset.mem_powerset.mp (Finset.mem_filter.mp s.2).1)
  right_inv d := by
    apply Subtype.ext
    exact Nat.prod_primeFactors_of_squarefree (Finset.mem_filter.mp d.2).2.1

/-- The V1.8.38 finite signed subset sum equals an exact Möbius/totient divisor sum.

The divisor carrier retains its explicit prime-factor cutoff; this is not a Ramanujan-prefix
identification. -/
theorem boundedSignedPrimeSum_eq_moebius_totient_sum (N R H : ℕ) :
    boundedSignedPrimeSum N R H =
      ∑ d ∈ boundedArithmeticDivisors N R H,
        (((ArithmeticFunction.moebius d : ℤ) : ℝ) /
          (((Nat.totient d : ℕ) : ℝ) ^ 2)) := by
  unfold boundedSignedPrimeSum
  exact Finset.sum_nbij'
    (fun s => ∏ p ∈ s, p) (fun d => d.primeFactors)
    (fun _ hs => subsetProduct_mem_boundedArithmeticDivisors hs)
    (fun _ hd => primeFactors_mem_boundedBadPrimeSubsets hd)
    (fun _ hs => subsetProduct_primeFactors
      (Finset.mem_powerset.mp (Finset.mem_filter.mp hs).1))
    (fun _ hd => Nat.prod_primeFactors_of_squarefree (Finset.mem_filter.mp hd).2.1)
    (fun _ hs => signedSubsetWeight_eq_moebius_totient
      (Finset.mem_powerset.mp (Finset.mem_filter.mp hs).1))

end GoldbachCircleMethodSquarefreeCoefficientBindingV1839
