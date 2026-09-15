import GoldbachCircleMethodArithmeticMultipleCountV18432

/-!
# Goldbach V1.8.433: prefix divisor budget

The transposed incidence column is evaluated as its support cardinality times
the positive divisor weight, then bounded using the exact multiple count from
V1.8.432.  The arithmetic-factor prefix is thereby reduced to an explicit
finite reciprocal-divisor budget.

No uniform constant for that budget is asserted here. `proof_status = NO_PROOF`.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodArithmeticPrefixDivisorBudgetV18433

open GoldbachCircleMethodArithmeticDivisorReindexV18430
open GoldbachCircleMethodArithmeticIncidenceTransposeV18431
open GoldbachCircleMethodArithmeticMultipleCountV18432

theorem incidenceColumn_eq_card_mul (X d : ℕ) :
    (∑ n ∈ Finset.Ico 1 X, incidenceEntry n d) =
      (((Finset.Ico 1 X).filter
        (fun n => d ∈ subsetDivisorCarrier n)).card : ℝ) * divisorMajorant d := by
  unfold incidenceEntry
  rw [← Finset.sum_filter]
  simp

theorem incidenceColumn_le_divisorBudget {X d : ℕ} (hX : 1 ≤ X) :
    (∑ n ∈ Finset.Ico 1 X, incidenceEntry n d) ≤
      (((X - 1) / d : ℕ) : ℝ) * divisorMajorant d := by
  rw [incidenceColumn_eq_card_mul]
  apply mul_le_mul_of_nonneg_right
  · exact_mod_cast incidenceSupport_card_le_div (d := d) hX
  · exact divisorMajorant_nonneg d

/-- Full finite prefix reduction with the reciprocal-divisor multiplicity visible. -/
theorem arithmeticFactor_prefix_le_reciprocalDivisorBudget {X : ℕ} (hX : 1 ≤ X) :
    (∑ n ∈ Finset.Ico 1 X,
      GoldbachCircleMethodGlobalSieveFiniteFactorV18173.arithmeticFactor n) ≤
      ∑ d ∈ Finset.range X,
        (((X - 1) / d : ℕ) : ℝ) * divisorMajorant d := by
  calc
    (∑ n ∈ Finset.Ico 1 X,
        GoldbachCircleMethodGlobalSieveFiniteFactorV18173.arithmeticFactor n) ≤
        ∑ d ∈ Finset.range X, ∑ n ∈ Finset.Ico 1 X, incidenceEntry n d :=
      arithmeticFactor_prefix_le_divisorFirstMass X
    _ ≤ ∑ d ∈ Finset.range X,
        (((X - 1) / d : ℕ) : ℝ) * divisorMajorant d := by
      apply Finset.sum_le_sum
      intro d hd
      exact incidenceColumn_le_divisorBudget hX

end GoldbachCircleMethodArithmeticPrefixDivisorBudgetV18433
