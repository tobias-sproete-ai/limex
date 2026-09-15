import GoldbachCircleMethodArithmeticDivisorReindexV18430

/-!
# Goldbach V1.8.431: finite incidence transpose

For positive indices `1 ≤ n < X`, every divisor-carrier point lies in
`range X`.  The carrier sum is padded by zeros to that common range and the
resulting finite incidence matrix is transposed exactly.

No multiplicity estimate is asserted yet. `proof_status = NO_PROOF`.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodArithmeticIncidenceTransposeV18431

open GoldbachCircleMethodArithmeticFactorPositiveConvolutionV18428
open GoldbachCircleMethodArithmeticDivisorReindexV18430

theorem divisorMajorant_nonneg (d : ℕ) : 0 ≤ divisorMajorant d := by
  unfold divisorMajorant arithmeticSubsetMajorant
  positivity

theorem subsetDivisorCarrier_subset_range {X n : ℕ}
    (hn1 : 1 ≤ n) (hnX : n < X) : subsetDivisorCarrier n ⊆ Finset.range X := by
  intro d hd
  have hprops := mem_subsetDivisorCarrier_properties hd
  have hdn : d ≤ n := Nat.le_of_dvd (Nat.zero_lt_of_lt hn1) hprops.2.2
  exact Finset.mem_range.mpr (lt_of_le_of_lt hdn hnX)

/-- Zero-padded incidence entry. -/
noncomputable def incidenceEntry (n d : ℕ) : ℝ :=
  if d ∈ subsetDivisorCarrier n then divisorMajorant d else 0

theorem carrier_sum_eq_padded_range {X n : ℕ}
    (hn1 : 1 ≤ n) (hnX : n < X) :
    (∑ d ∈ subsetDivisorCarrier n, divisorMajorant d) =
      ∑ d ∈ Finset.range X, incidenceEntry n d := by
  have hsub := subsetDivisorCarrier_subset_range hn1 hnX
  simp only [incidenceEntry]
  rw [← Finset.sum_filter]
  apply Finset.sum_congr
  · ext d
    simp only [Finset.mem_filter]
    constructor
    · intro hd
      exact ⟨hsub hd, hd⟩
    · intro hd
      exact hd.2
  · intro d hd
    rfl

/-- Exact finite Fubini step: transpose from source-first to divisor-first. -/
theorem incidence_transpose (X : ℕ) :
    (∑ n ∈ Finset.Ico 1 X, ∑ d ∈ Finset.range X, incidenceEntry n d) =
      ∑ d ∈ Finset.range X, ∑ n ∈ Finset.Ico 1 X, incidenceEntry n d := by
  exact Finset.sum_comm

/-- The arithmetic-factor prefix is reduced to the divisor-first incidence mass. -/
theorem arithmeticFactor_prefix_le_divisorFirstMass (X : ℕ) :
    (∑ n ∈ Finset.Ico 1 X,
      GoldbachCircleMethodGlobalSieveFiniteFactorV18173.arithmeticFactor n) ≤
      ∑ d ∈ Finset.range X, ∑ n ∈ Finset.Ico 1 X, incidenceEntry n d := by
  calc
    (∑ n ∈ Finset.Ico 1 X,
        GoldbachCircleMethodGlobalSieveFiniteFactorV18173.arithmeticFactor n) ≤
        ∑ n ∈ Finset.Ico 1 X,
          ∑ d ∈ subsetDivisorCarrier n, divisorMajorant d := by
      apply Finset.sum_le_sum
      intro n hn
      exact arithmeticFactor_le_divisorCarrier_sum n
    _ = ∑ n ∈ Finset.Ico 1 X, ∑ d ∈ Finset.range X, incidenceEntry n d := by
      apply Finset.sum_congr rfl
      intro n hn
      have hni := Finset.mem_Ico.mp hn
      exact carrier_sum_eq_padded_range hni.1 hni.2
    _ = ∑ d ∈ Finset.range X, ∑ n ∈ Finset.Ico 1 X, incidenceEntry n d :=
      incidence_transpose X

end GoldbachCircleMethodArithmeticIncidenceTransposeV18431
