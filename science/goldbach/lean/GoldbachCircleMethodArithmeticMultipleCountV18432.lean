import GoldbachCircleMethodArithmeticIncidenceTransposeV18431

/-!
# Goldbach V1.8.432: exact multiple count

For a fixed nonzero divisor index `d`, the actual incidence support is contained
in the set of positive multiples of `d` below `X`.  That containing set has the
exact cardinality `(X - 1) / d`.

This is the finite source of the required reciprocal-divisor gain.  No
convergence estimate is asserted. `proof_status = NO_PROOF`.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodArithmeticMultipleCountV18432

open GoldbachCircleMethodArithmeticDivisorReindexV18430
open GoldbachCircleMethodArithmeticIncidenceTransposeV18431

def positiveMultiplesBelow (X d : ℕ) : Finset ℕ :=
  (Finset.Ico 1 X).filter (fun n => d ∣ n)

theorem Ico_one_eq_Ioc_zero_pred {X : ℕ} (hX : 1 ≤ X) :
    Finset.Ico 1 X = Finset.Ioc 0 (X - 1) := by
  ext n
  simp only [Finset.mem_Ico, Finset.mem_Ioc]
  omega

theorem positiveMultiplesBelow_card {X d : ℕ} (hX : 1 ≤ X) :
    (positiveMultiplesBelow X d).card = (X - 1) / d := by
  unfold positiveMultiplesBelow
  rw [Ico_one_eq_Ioc_zero_pred hX]
  exact Nat.Ioc_filter_dvd_card_eq_div (X - 1) d

theorem incidence_support_subset_multiples {X d : ℕ} :
    (Finset.Ico 1 X).filter (fun n => d ∈ subsetDivisorCarrier n) ⊆
      positiveMultiplesBelow X d := by
  intro n hn
  have hmem := Finset.mem_filter.mp hn
  rw [positiveMultiplesBelow, Finset.mem_filter]
  exact ⟨hmem.1, (mem_subsetDivisorCarrier_properties hmem.2).2.2⟩

/-- The incidence multiplicity is bounded by the exact multiple count. -/
theorem incidenceSupport_card_le_div {X d : ℕ} (hX : 1 ≤ X) :
    ((Finset.Ico 1 X).filter (fun n => d ∈ subsetDivisorCarrier n)).card ≤
      (X - 1) / d := by
  rw [← positiveMultiplesBelow_card hX]
  exact Finset.card_le_card incidence_support_subset_multiples

end GoldbachCircleMethodArithmeticMultipleCountV18432
