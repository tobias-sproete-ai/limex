import GoldbachCircleMethodArithmeticPrefixKernelReductionV18435

/-!
# Goldbach V1.8.436: support-preserving kernel reduction

V1.8.435 deliberately enlarged the divisor carrier to all natural indices.
This module restores the exact structural support before the Euler-product
step: only nonzero squarefree integers whose prime factors are all odd can
carry incidence mass.

No Euler-product bound is asserted. `proof_status = NO_PROOF`.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodArithmeticSupportedKernelV18436

open GoldbachCircleMethodArithmeticFactorPositiveConvolutionV18428
open GoldbachCircleMethodArithmeticSubsetDivisorEmbeddingV18429
open GoldbachCircleMethodArithmeticDivisorReindexV18430
open GoldbachCircleMethodArithmeticIncidenceTransposeV18431
open GoldbachCircleMethodArithmeticMultipleCountV18432
open GoldbachCircleMethodArithmeticPrefixDivisorBudgetV18433
open GoldbachCircleMethodArithmeticDivisorWeightNormalFormV18434

def AdmissibleDivisor (d : ℕ) : Prop :=
  Squarefree d ∧ ∀ p ∈ d.primeFactors, 2 < p

theorem admissible_of_mem_subsetDivisorCarrier {n d : ℕ}
    (hd : d ∈ subsetDivisorCarrier n) : AdmissibleDivisor d := by
  have hsq : Squarefree d := (mem_subsetDivisorCarrier_properties hd).2.1
  rw [subsetDivisorCarrier, Finset.mem_image] at hd
  rcases hd with ⟨t, ht, rfl⟩
  have hsub : t ⊆ oddPrimeFactors n := Finset.mem_powerset.mp ht
  refine ⟨hsq, ?_⟩
  intro p hp
  rw [primeFactors_subsetDivisor hsub] at hp
  exact (Finset.mem_filter.mp (hsub hp)).2

noncomputable def supportedReciprocalKernel (d : ℕ) : ℝ :=
  if AdmissibleDivisor d then divisorMajorant d / (d : ℝ) else 0

theorem supportedReciprocalKernel_nonneg (d : ℕ) :
    0 ≤ supportedReciprocalKernel d := by
  unfold supportedReciprocalKernel
  split_ifs
  · exact div_nonneg (le_of_lt (divisorMajorant_pos d)) (Nat.cast_nonneg d)
  · exact le_rfl

theorem incidenceEntry_eq_zero_of_not_admissible {n d : ℕ}
    (hd : ¬ AdmissibleDivisor d) : incidenceEntry n d = 0 := by
  unfold incidenceEntry
  split_ifs with hmem
  · exact False.elim (hd (admissible_of_mem_subsetDivisorCarrier hmem))
  · rfl

theorem incidenceColumn_le_supportedKernel {X d : ℕ} (hX : 1 ≤ X) :
    (∑ n ∈ Finset.Ico 1 X, incidenceEntry n d) ≤
      (X : ℝ) * supportedReciprocalKernel d := by
  by_cases hadm : AdmissibleDivisor d
  · have hd : d ≠ 0 := hadm.1.ne_zero
    have hdR : (0 : ℝ) < d := by positivity
    have hcast : ((((X - 1) / d : ℕ) : ℝ)) ≤
        ((X - 1 : ℕ) : ℝ) / (d : ℝ) := Nat.cast_div_le
    have hsub : (((X - 1 : ℕ) : ℝ)) ≤ (X : ℝ) := by
      exact_mod_cast Nat.sub_le X 1
    have hquot : ((((X - 1) / d : ℕ) : ℝ)) ≤ (X : ℝ) / (d : ℝ) :=
      hcast.trans (div_le_div_of_nonneg_right hsub hdR.le)
    calc
      (∑ n ∈ Finset.Ico 1 X, incidenceEntry n d) ≤
          (((X - 1) / d : ℕ) : ℝ) * divisorMajorant d :=
        incidenceColumn_le_divisorBudget hX
      _ ≤ ((X : ℝ) / (d : ℝ)) * divisorMajorant d :=
        mul_le_mul_of_nonneg_right hquot (le_of_lt (divisorMajorant_pos d))
      _ = (X : ℝ) * supportedReciprocalKernel d := by
        rw [supportedReciprocalKernel, if_pos hadm]
        ring
  · simp only [supportedReciprocalKernel, if_neg hadm, mul_zero]
    apply le_of_eq
    apply Finset.sum_eq_zero
    intro n hn
    exact incidenceEntry_eq_zero_of_not_admissible hadm

theorem arithmeticFactor_prefix_le_scale_mul_supportedKernelSum {X : ℕ} (hX : 1 ≤ X) :
    (∑ n ∈ Finset.Ico 1 X,
      GoldbachCircleMethodGlobalSieveFiniteFactorV18173.arithmeticFactor n) ≤
      (X : ℝ) * ∑ d ∈ Finset.range X, supportedReciprocalKernel d := by
  calc
    (∑ n ∈ Finset.Ico 1 X,
        GoldbachCircleMethodGlobalSieveFiniteFactorV18173.arithmeticFactor n) ≤
        ∑ d ∈ Finset.range X, ∑ n ∈ Finset.Ico 1 X, incidenceEntry n d :=
      arithmeticFactor_prefix_le_divisorFirstMass X
    _ ≤ ∑ d ∈ Finset.range X, (X : ℝ) * supportedReciprocalKernel d := by
      apply Finset.sum_le_sum
      intro d hd
      exact incidenceColumn_le_supportedKernel hX
    _ = (X : ℝ) * ∑ d ∈ Finset.range X, supportedReciprocalKernel d := by
      rw [Finset.mul_sum]

end GoldbachCircleMethodArithmeticSupportedKernelV18436
