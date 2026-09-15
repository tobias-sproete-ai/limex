import GoldbachCircleMethodArithmeticSubsetDivisorEmbeddingV18429

/-!
# Goldbach V1.8.430: exact divisor reindexing

The powerset majorant is reindexed without multiplicity loss onto the image of
the subset-product map.  Every image point is a nonzero squarefree divisor of
the original integer.  No infinite product or mean-value estimate is used.

`proof_status = NO_PROOF`.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodArithmeticDivisorReindexV18430

open GoldbachCircleMethodArithmeticFactorPositiveConvolutionV18428
open GoldbachCircleMethodArithmeticSubsetDivisorEmbeddingV18429

/-- Finite image of odd-prime subsets inside the divisor lattice. -/
def subsetDivisorCarrier (n : ℕ) : Finset ℕ :=
  (oddPrimeFactors n).powerset.image subsetDivisor

/-- The same positive product, now read from the prime factors of a divisor. -/
noncomputable def divisorMajorant (d : ℕ) : ℝ :=
  arithmeticSubsetMajorant d.primeFactors

theorem primeFactors_subsetDivisor {n : ℕ} {t : Finset ℕ}
    (ht : t ⊆ oddPrimeFactors n) :
    (subsetDivisor t).primeFactors = t := by
  unfold subsetDivisor
  exact Nat.primeFactors_prod fun p hp =>
    prime_of_mem_oddPrimeFactors (ht hp)

theorem mem_subsetDivisorCarrier_properties {n d : ℕ}
    (hd : d ∈ subsetDivisorCarrier n) :
    d ≠ 0 ∧ Squarefree d ∧ d ∣ n := by
  rw [subsetDivisorCarrier, Finset.mem_image] at hd
  rcases hd with ⟨t, ht, rfl⟩
  have hsub : t ⊆ oddPrimeFactors n := Finset.mem_powerset.mp ht
  exact ⟨subsetDivisor_ne_zero hsub, subsetDivisor_squarefree hsub,
    subsetDivisor_dvd hsub⟩

/-- Exact, collision-free reindexing of the positive convolution majorant. -/
theorem powerset_majorant_eq_divisorCarrier_sum (n : ℕ) :
    (∑ t ∈ (oddPrimeFactors n).powerset, arithmeticSubsetMajorant t) =
      ∑ d ∈ subsetDivisorCarrier n, divisorMajorant d := by
  unfold subsetDivisorCarrier
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro t ht
    unfold divisorMajorant
    rw [primeFactors_subsetDivisor (Finset.mem_powerset.mp ht)]
  · intro t ht u hu htu
    exact subsetDivisor_injective_on
      (Finset.mem_powerset.mp ht) (Finset.mem_powerset.mp hu) htu

/-- The arithmetic factor is bounded by a genuine finite divisor-carrier sum. -/
theorem arithmeticFactor_le_divisorCarrier_sum (n : ℕ) :
    GoldbachCircleMethodGlobalSieveFiniteFactorV18173.arithmeticFactor n ≤
      ∑ d ∈ subsetDivisorCarrier n, divisorMajorant d := by
  calc
    GoldbachCircleMethodGlobalSieveFiniteFactorV18173.arithmeticFactor n ≤
        ∑ t ∈ (oddPrimeFactors n).powerset, arithmeticSubsetMajorant t :=
      arithmeticFactor_le_positive_powerset_majorant n
    _ = ∑ d ∈ subsetDivisorCarrier n, divisorMajorant d :=
      powerset_majorant_eq_divisorCarrier_sum n

end GoldbachCircleMethodArithmeticDivisorReindexV18430
