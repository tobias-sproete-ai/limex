import GoldbachCircleMethodArithmeticFactorPositiveConvolutionV18428
import Mathlib.Data.Nat.Squarefree

/-!
# Goldbach V1.8.429: subset-to-divisor embedding

The positive powerset convolution from V1.8.428 is embedded into the finite
divisor lattice: the product of every subset of odd prime factors is nonzero,
squarefree, divides the source integer, and uniquely determines the subset.

This is an exact finite combinatorial statement.  It does not yet assert a
prefix mean or any asymptotic estimate.  `proof_status = NO_PROOF`.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodArithmeticSubsetDivisorEmbeddingV18429

open GoldbachCircleMethodArithmeticFactorPositiveConvolutionV18428

/-- The squarefree divisor encoded by a subset of odd prime factors. -/
def subsetDivisor (t : Finset ℕ) : ℕ := ∏ p ∈ t, p

theorem prime_of_mem_oddPrimeFactors {n p : ℕ} (hp : p ∈ oddPrimeFactors n) :
    p.Prime := by
  exact (Nat.mem_primeFactors.mp (Finset.mem_filter.mp hp).1).1

theorem subsetDivisor_ne_zero {n : ℕ} {t : Finset ℕ}
    (ht : t ⊆ oddPrimeFactors n) : subsetDivisor t ≠ 0 := by
  unfold subsetDivisor
  exact Finset.prod_ne_zero_iff.mpr fun p hp =>
    (prime_of_mem_oddPrimeFactors (ht hp)).ne_zero

theorem subsetDivisor_squarefree {n : ℕ} {t : Finset ℕ}
    (ht : t ⊆ oddPrimeFactors n) : Squarefree (subsetDivisor t) := by
  unfold subsetDivisor
  refine Finset.squarefree_prod_of_pairwise_isCoprime (fun p hp q hq hpq => ?_)
    (fun p hp => (prime_of_mem_oddPrimeFactors (ht hp)).squarefree)
  simp only [← Nat.coprime_iff_isRelPrime]
  exact (Nat.coprime_primes
    (prime_of_mem_oddPrimeFactors (ht hp))
    (prime_of_mem_oddPrimeFactors (ht hq))).mpr hpq

theorem subsetDivisor_dvd {n : ℕ} {t : Finset ℕ}
    (ht : t ⊆ oddPrimeFactors n) : subsetDivisor t ∣ n := by
  have ht' : t ⊆ n.primeFactors := fun p hp => (Finset.mem_filter.mp (ht hp)).1
  unfold subsetDivisor
  exact (Finset.prod_dvd_prod_of_subset _ _ (fun p => p) ht').trans
    (Nat.prod_primeFactors_dvd n)

/-- Products are injective on subsets of the odd-prime support. -/
theorem subsetDivisor_injective_on {n : ℕ} {t u : Finset ℕ}
    (ht : t ⊆ oddPrimeFactors n) (hu : u ⊆ oddPrimeFactors n)
    (hprod : subsetDivisor t = subsetDivisor u) : t = u := by
  have htPrime : ∀ p ∈ t, p.Prime := fun p hp =>
    prime_of_mem_oddPrimeFactors (ht hp)
  have huPrime : ∀ p ∈ u, p.Prime := fun p hp =>
    prime_of_mem_oddPrimeFactors (hu hp)
  have htFactors : (subsetDivisor t).primeFactors = t := by
    simpa [subsetDivisor] using Nat.primeFactors_prod htPrime
  have huFactors : (subsetDivisor u).primeFactors = u := by
    simpa [subsetDivisor] using Nat.primeFactors_prod huPrime
  calc
    t = (subsetDivisor t).primeFactors := htFactors.symm
    _ = (subsetDivisor u).primeFactors := by rw [hprod]
    _ = u := huFactors

end GoldbachCircleMethodArithmeticSubsetDivisorEmbeddingV18429
