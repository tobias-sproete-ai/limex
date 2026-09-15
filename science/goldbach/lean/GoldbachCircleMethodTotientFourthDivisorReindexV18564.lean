import GoldbachCircleMethodTotientFourthPositiveConvolutionV18563
import Mathlib.Data.Nat.Squarefree

/-!
# Goldbach V1.8.564: collision-free divisor reindexing

The positive subset convolution from V1.8.563 is reindexed exactly by the
squarefree divisors encoded by prime-support subsets.  The divisor weight is
put in the normal form `30^omega(d)/d`.  This is finite combinatorics only;
the prefix mean remains open.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodTotientFourthDivisorReindexV18564

open GoldbachCircleMethodCollisionTotientRatioEnvelopeV18556
open GoldbachCircleMethodTotientFourthPositiveConvolutionV18563

def totientFourthSubsetDivisor (t : Finset ℕ) : ℕ :=
  ∏ p ∈ t, p

theorem totientFourthSubsetDivisor_ne_zero {n : ℕ} {t : Finset ℕ}
    (ht : t ⊆ n.primeFactors) : totientFourthSubsetDivisor t ≠ 0 := by
  unfold totientFourthSubsetDivisor
  exact Finset.prod_ne_zero_iff.mpr fun p hp =>
    (Nat.prime_of_mem_primeFactors (ht hp)).ne_zero

theorem totientFourthSubsetDivisor_squarefree {n : ℕ} {t : Finset ℕ}
    (ht : t ⊆ n.primeFactors) : Squarefree (totientFourthSubsetDivisor t) := by
  unfold totientFourthSubsetDivisor
  refine Finset.squarefree_prod_of_pairwise_isCoprime
    (fun p hp q hq hpq => ?_) (fun p hp =>
      (Nat.prime_of_mem_primeFactors (ht hp)).squarefree)
  simp only [← Nat.coprime_iff_isRelPrime]
  exact (Nat.coprime_primes
    (Nat.prime_of_mem_primeFactors (ht hp))
    (Nat.prime_of_mem_primeFactors (ht hq))).mpr hpq

theorem totientFourthSubsetDivisor_dvd {n : ℕ} {t : Finset ℕ}
    (ht : t ⊆ n.primeFactors) : totientFourthSubsetDivisor t ∣ n := by
  unfold totientFourthSubsetDivisor
  exact (Finset.prod_dvd_prod_of_subset _ _ (fun p => p) ht).trans
    (Nat.prod_primeFactors_dvd n)

theorem primeFactors_totientFourthSubsetDivisor {n : ℕ} {t : Finset ℕ}
    (ht : t ⊆ n.primeFactors) :
    (totientFourthSubsetDivisor t).primeFactors = t := by
  unfold totientFourthSubsetDivisor
  exact Nat.primeFactors_prod fun p hp =>
    Nat.prime_of_mem_primeFactors (ht hp)

theorem totientFourthSubsetDivisor_injective_on {n : ℕ} {t u : Finset ℕ}
    (ht : t ⊆ n.primeFactors) (hu : u ⊆ n.primeFactors)
    (hprod : totientFourthSubsetDivisor t =
      totientFourthSubsetDivisor u) : t = u := by
  calc
    t = (totientFourthSubsetDivisor t).primeFactors :=
      (primeFactors_totientFourthSubsetDivisor ht).symm
    _ = (totientFourthSubsetDivisor u).primeFactors := by rw [hprod]
    _ = u := primeFactors_totientFourthSubsetDivisor hu

def totientFourthDivisorCarrier (n : ℕ) : Finset ℕ :=
  n.primeFactors.powerset.image totientFourthSubsetDivisor

noncomputable def totientFourthDivisorMajorant (d : ℕ) : ℝ :=
  totientFourthSubsetWeight d.primeFactors

theorem totientFourthDivisorMajorant_nonneg (d : ℕ) :
    0 ≤ totientFourthDivisorMajorant d := by
  exact totientFourthSubsetWeight_nonneg d.primeFactors

/-- Exact, injective subset-to-divisor reindexing. -/
theorem positive_powerset_sum_eq_divisorCarrier_sum (n : ℕ) :
    (∑ t ∈ n.primeFactors.powerset, totientFourthSubsetWeight t) =
      ∑ d ∈ totientFourthDivisorCarrier n,
        totientFourthDivisorMajorant d := by
  unfold totientFourthDivisorCarrier
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro t ht
    unfold totientFourthDivisorMajorant
    rw [primeFactors_totientFourthSubsetDivisor
      (Finset.mem_powerset.mp ht)]
  · intro t ht u hu htu
    exact totientFourthSubsetDivisor_injective_on
      (Finset.mem_powerset.mp ht) (Finset.mem_powerset.mp hu) htu

/-- Normal form of the squarefree divisor-convolution weight. -/
theorem totientFourthDivisorMajorant_eq_pow_div
    {d : ℕ} (hsq : Squarefree d) :
    totientFourthDivisorMajorant d =
      (30 : ℝ) ^ d.primeFactors.card / (d : ℝ) := by
  unfold totientFourthDivisorMajorant totientFourthSubsetWeight
  rw [Finset.prod_div_distrib]
  simp only [Finset.prod_const]
  have hprodR : (∏ p ∈ d.primeFactors, (p : ℝ)) = (d : ℝ) := by
    simpa only [Nat.cast_prod] using
      congrArg (fun m : ℕ => (m : ℝ))
        (Nat.prod_primeFactors_of_squarefree hsq)
  rw [hprodR]

/-- Pointwise reduction of the collision ratio to its exact finite divisor
carrier. -/
theorem levelTotientRatio_pow_four_le_divisorCarrier_sum
    (n : ℕ) (hn : n ≠ 0) :
    levelTotientRatio n ^ 4 ≤
      ∑ d ∈ totientFourthDivisorCarrier n,
        totientFourthDivisorMajorant d := by
  calc
    levelTotientRatio n ^ 4 ≤
        ∑ t ∈ n.primeFactors.powerset, totientFourthSubsetWeight t :=
      levelTotientRatio_pow_four_le_positive_powerset_sum n hn
    _ = ∑ d ∈ totientFourthDivisorCarrier n,
          totientFourthDivisorMajorant d :=
      positive_powerset_sum_eq_divisorCarrier_sum n

end GoldbachCircleMethodTotientFourthDivisorReindexV18564
