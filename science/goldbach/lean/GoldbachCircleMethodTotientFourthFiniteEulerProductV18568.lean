import GoldbachCircleMethodTotientFourthSquarefreeKernelV18567

/-!
# Goldbach V1.8.568: finite Euler-product majorant for the squarefree kernel

The squarefree reciprocal kernel prefix is reindexed injectively by prime
factor subsets and embedded into the full powerset of primes up to `Q`.
This yields a finite Euler-product majorant.  A `Q`-independent numerical
upper bound for that product remains a separate gate.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodTotientFourthFiniteEulerProductV18568

open GoldbachCircleMethodTotientFourthDivisorReindexV18564
open GoldbachCircleMethodTotientFourthSquarefreeKernelV18567

def squarefreePrefixCarrier (Q : ℕ) : Finset ℕ :=
  (Finset.Icc 1 Q).filter Squarefree

def primePrefixCarrier (Q : ℕ) : Finset ℕ :=
  (Finset.Icc 2 Q).filter Nat.Prime

noncomputable def totientFourthSquarefreeSubsetWeight (t : Finset ℕ) : ℝ :=
  ∏ p ∈ t, (30 : ℝ) / (p : ℝ) ^ 2

theorem totientFourthSquarefreeSubsetWeight_nonneg (t : Finset ℕ) :
    0 ≤ totientFourthSquarefreeSubsetWeight t := by
  unfold totientFourthSquarefreeSubsetWeight
  positivity

theorem squarefreePrefixCarrier_mem_pos {Q d : ℕ}
    (hd : d ∈ squarefreePrefixCarrier Q) : 0 < d := by
  exact lt_of_lt_of_le Nat.zero_lt_one
    (Finset.mem_Icc.mp (Finset.mem_filter.mp hd).1).1

theorem squarefreePrefixCarrier_mem_squarefree {Q d : ℕ}
    (hd : d ∈ squarefreePrefixCarrier Q) : Squarefree d :=
  (Finset.mem_filter.mp hd).2

theorem primeFactors_subset_primePrefixCarrier {Q d : ℕ}
    (hd : d ∈ squarefreePrefixCarrier Q) :
    d.primeFactors ⊆ primePrefixCarrier Q := by
  intro p hp
  have hpprime := Nat.prime_of_mem_primeFactors hp
  have hpdvd := Nat.dvd_of_mem_primeFactors hp
  have hdIcc := Finset.mem_Icc.mp (Finset.mem_filter.mp hd).1
  have hp_le_d := Nat.le_of_dvd (squarefreePrefixCarrier_mem_pos hd) hpdvd
  exact Finset.mem_filter.mpr ⟨
    Finset.mem_Icc.mpr ⟨hpprime.two_le, hp_le_d.trans hdIcc.2⟩,
    hpprime⟩

theorem primeFactors_injective_on_squarefreePrefixCarrier
    {Q d e : ℕ}
    (hd : d ∈ squarefreePrefixCarrier Q)
    (he : e ∈ squarefreePrefixCarrier Q)
    (hfac : d.primeFactors = e.primeFactors) : d = e := by
  calc
    d = ∏ p ∈ d.primeFactors, p :=
      (Nat.prod_primeFactors_of_squarefree
        (squarefreePrefixCarrier_mem_squarefree hd)).symm
    _ = ∏ p ∈ e.primeFactors, p := by rw [hfac]
    _ = e := Nat.prod_primeFactors_of_squarefree
      (squarefreePrefixCarrier_mem_squarefree he)

theorem squarefreeKernel_eq_subsetWeight {d : ℕ} (hsq : Squarefree d) :
    squarefreeReciprocalTotientFourthKernel d =
      totientFourthSquarefreeSubsetWeight d.primeFactors := by
  rw [squarefreeReciprocalTotientFourthKernel_eq_pow_div_sq hsq]
  unfold totientFourthSquarefreeSubsetWeight
  rw [Finset.prod_div_distrib]
  simp only [Finset.prod_const]
  have hprodR : (∏ p ∈ d.primeFactors, (p : ℝ)) = (d : ℝ) := by
    simpa only [Nat.cast_prod] using
      congrArg (fun m : ℕ => (m : ℝ))
        (Nat.prod_primeFactors_of_squarefree hsq)
  have hden : (∏ p ∈ d.primeFactors, (p : ℝ) ^ 2) = (d : ℝ) ^ 2 := by
    rw [Finset.prod_pow, hprodR]
  rw [hden]

theorem squarefreeKernelPrefix_eq_carrier_sum (Q : ℕ) :
    (∑ d ∈ Finset.Icc 1 Q,
      squarefreeReciprocalTotientFourthKernel d) =
      ∑ d ∈ squarefreePrefixCarrier Q,
        squarefreeReciprocalTotientFourthKernel d := by
  unfold squarefreePrefixCarrier
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro d hd
  by_cases hsq : Squarefree d
  · simp [squarefreeReciprocalTotientFourthKernel, hsq]
  · simp [squarefreeReciprocalTotientFourthKernel, hsq]

theorem squarefreeCarrier_sum_eq_primeFactors_image_sum (Q : ℕ) :
    (∑ d ∈ squarefreePrefixCarrier Q,
      squarefreeReciprocalTotientFourthKernel d) =
      ∑ t ∈ (squarefreePrefixCarrier Q).image Nat.primeFactors,
        totientFourthSquarefreeSubsetWeight t := by
  symm
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro d hd
    exact (squarefreeKernel_eq_subsetWeight
      (squarefreePrefixCarrier_mem_squarefree hd)).symm
  · intro d hd e he hfac
    exact primeFactors_injective_on_squarefreePrefixCarrier hd he hfac

theorem primeFactors_image_subset_primePrefix_powerset (Q : ℕ) :
    (squarefreePrefixCarrier Q).image Nat.primeFactors ⊆
      (primePrefixCarrier Q).powerset := by
  intro t ht
  rw [Finset.mem_image] at ht
  rcases ht with ⟨d, hd, rfl⟩
  exact Finset.mem_powerset.mpr
    (primeFactors_subset_primePrefixCarrier hd)

theorem squarefreeKernelPrefix_le_powerset_sum (Q : ℕ) :
    (∑ d ∈ Finset.Icc 1 Q,
      squarefreeReciprocalTotientFourthKernel d) ≤
      ∑ t ∈ (primePrefixCarrier Q).powerset,
        totientFourthSquarefreeSubsetWeight t := by
  rw [squarefreeKernelPrefix_eq_carrier_sum,
    squarefreeCarrier_sum_eq_primeFactors_image_sum]
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (primeFactors_image_subset_primePrefix_powerset Q)
    (fun t _ht _hnot => totientFourthSquarefreeSubsetWeight_nonneg t)

theorem primePrefixProduct_eq_powerset_sum (Q : ℕ) :
    (∏ p ∈ primePrefixCarrier Q,
      (1 + (30 : ℝ) / (p : ℝ) ^ 2)) =
      ∑ t ∈ (primePrefixCarrier Q).powerset,
        totientFourthSquarefreeSubsetWeight t := by
  unfold totientFourthSquarefreeSubsetWeight
  exact Finset.prod_one_add (primePrefixCarrier Q)

/-- Finite Euler-product majorant for the exact squarefree reciprocal kernel
prefix. -/
theorem squarefreeKernelPrefix_le_finiteEulerProduct (Q : ℕ) :
    (∑ d ∈ Finset.Icc 1 Q,
      squarefreeReciprocalTotientFourthKernel d) ≤
      ∏ p ∈ primePrefixCarrier Q,
        (1 + (30 : ℝ) / (p : ℝ) ^ 2) := by
  rw [primePrefixProduct_eq_powerset_sum]
  exact squarefreeKernelPrefix_le_powerset_sum Q

end GoldbachCircleMethodTotientFourthFiniteEulerProductV18568
