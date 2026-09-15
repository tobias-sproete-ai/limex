import GoldbachCircleMethodArithmeticSupportedKernelNormalFormV18437

/-!
# Goldbach V1.8.438: support-preserving powerset embedding

The finite supported divisor sum is injected into the powerset of the odd
primes below the cutoff.  This is the finite combinatorial bridge required
before an infinite Euler-product bound may be used.

No uniform product bound and no Goldbach theorem are asserted here.
`proof_status = NO_PROOF` for the top-level Goldbach quest.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodArithmeticSupportedPowersetV18438

open GoldbachCircleMethodArithmeticDivisorWeightNormalFormV18434
open GoldbachCircleMethodArithmeticSupportedKernelV18436
open GoldbachCircleMethodArithmeticSupportedKernelNormalFormV18437

noncomputable def admissibleDivisorsBelow (X : ℕ) : Finset ℕ :=
  (Finset.range X).filter AdmissibleDivisor

def oddPrimesBelow (X : ℕ) : Finset ℕ :=
  (Finset.range X).filter (fun p => p.Prime ∧ 2 < p)

noncomputable def squareKernelTerm (t : Finset ℕ) : ℝ :=
  ∏ p ∈ t, (3 : ℝ) / (p : ℝ) ^ 2

theorem squareKernelTerm_nonneg (t : Finset ℕ) :
    0 ≤ squareKernelTerm t := by
  unfold squareKernelTerm
  positivity

theorem supportedKernel_sum_eq_admissible_sum (X : ℕ) :
    (∑ d ∈ Finset.range X, supportedReciprocalKernel d) =
      ∑ d ∈ admissibleDivisorsBelow X, supportedReciprocalKernel d := by
  classical
  unfold admissibleDivisorsBelow
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro d hd
  by_cases hadm : AdmissibleDivisor d
  · simp [hadm]
  · simp [hadm, supportedReciprocalKernel]

theorem primeFactors_mem_oddPowerset_of_mem_admissibleDivisorsBelow
    {X d : ℕ} (hd : d ∈ admissibleDivisorsBelow X) :
    d.primeFactors ∈ (oddPrimesBelow X).powerset := by
  have hsplit := Finset.mem_filter.mp hd
  have hdX : d < X := Finset.mem_range.mp hsplit.1
  have hadm : AdmissibleDivisor d := hsplit.2
  apply Finset.mem_powerset.mpr
  intro p hp
  rw [oddPrimesBelow, Finset.mem_filter, Finset.mem_range]
  have hpPrime : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hp_le_d : p ≤ d :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero hadm.1.ne_zero) (Nat.dvd_of_mem_primeFactors hp)
  exact ⟨lt_of_le_of_lt hp_le_d hdX, hpPrime, hadm.2 p hp⟩

theorem primeFactors_injective_on_admissibleDivisorsBelow (X : ℕ) :
    Set.InjOn Nat.primeFactors (admissibleDivisorsBelow X) := by
  intro d hd e he hde
  have hdAdm : AdmissibleDivisor d := (Finset.mem_filter.mp hd).2
  have heAdm : AdmissibleDivisor e := (Finset.mem_filter.mp he).2
  calc
    d = ∏ p ∈ d.primeFactors, p :=
      (Nat.prod_primeFactors_of_squarefree hdAdm.1).symm
    _ = ∏ p ∈ e.primeFactors, p := by rw [hde]
    _ = e := Nat.prod_primeFactors_of_squarefree heAdm.1

theorem supportedKernel_eq_squareKernelTerm_of_mem
    {X d : ℕ} (hd : d ∈ admissibleDivisorsBelow X) :
    supportedReciprocalKernel d = squareKernelTerm d.primeFactors := by
  have hadm : AdmissibleDivisor d := (Finset.mem_filter.mp hd).2
  rw [supportedReciprocalKernel_eq_pow_div_sq_of_admissible hadm]
  unfold squareKernelTerm primeOmega
  rw [Finset.prod_div_distrib]
  simp only [Finset.prod_const, Finset.prod_pow]
  have hprodR : (∏ p ∈ d.primeFactors, (p : ℝ)) = (d : ℝ) := by
    simpa only [Nat.cast_prod] using
      congrArg (fun n : ℕ => (n : ℝ))
        (Nat.prod_primeFactors_of_squarefree hadm.1)
  rw [hprodR]

theorem supportedKernelSum_le_oddPowersetSum (X : ℕ) :
    (∑ d ∈ Finset.range X, supportedReciprocalKernel d) ≤
      ∑ t ∈ (oddPrimesBelow X).powerset, squareKernelTerm t := by
  rw [supportedKernel_sum_eq_admissible_sum]
  let imageCarrier := (admissibleDivisorsBelow X).image Nat.primeFactors
  have himage : imageCarrier ⊆ (oddPrimesBelow X).powerset := by
    intro t ht
    change t ∈ (admissibleDivisorsBelow X).image Nat.primeFactors at ht
    rw [Finset.mem_image] at ht
    rcases ht with ⟨d, hd, rfl⟩
    exact primeFactors_mem_oddPowerset_of_mem_admissibleDivisorsBelow hd
  calc
    (∑ d ∈ admissibleDivisorsBelow X, supportedReciprocalKernel d) =
        ∑ t ∈ imageCarrier, squareKernelTerm t := by
      change (∑ d ∈ admissibleDivisorsBelow X, supportedReciprocalKernel d) =
        ∑ t ∈ (admissibleDivisorsBelow X).image Nat.primeFactors, squareKernelTerm t
      rw [Finset.sum_image (primeFactors_injective_on_admissibleDivisorsBelow X)]
      apply Finset.sum_congr rfl
      intro d hd
      exact supportedKernel_eq_squareKernelTerm_of_mem hd
    _ ≤ ∑ t ∈ (oddPrimesBelow X).powerset, squareKernelTerm t := by
      exact Finset.sum_le_sum_of_subset_of_nonneg himage
        (fun t _ _ => squareKernelTerm_nonneg t)

theorem oddPowersetSum_eq_finiteEulerProduct (X : ℕ) :
    (∑ t ∈ (oddPrimesBelow X).powerset, squareKernelTerm t) =
      ∏ p ∈ oddPrimesBelow X, (1 + (3 : ℝ) / (p : ℝ) ^ 2) := by
  symm
  exact Finset.prod_one_add (oddPrimesBelow X)

theorem supportedKernelSum_le_finiteEulerProduct (X : ℕ) :
    (∑ d ∈ Finset.range X, supportedReciprocalKernel d) ≤
      ∏ p ∈ oddPrimesBelow X, (1 + (3 : ℝ) / (p : ℝ) ^ 2) := by
  rw [← oddPowersetSum_eq_finiteEulerProduct]
  exact supportedKernelSum_le_oddPowersetSum X

end GoldbachCircleMethodArithmeticSupportedPowersetV18438
