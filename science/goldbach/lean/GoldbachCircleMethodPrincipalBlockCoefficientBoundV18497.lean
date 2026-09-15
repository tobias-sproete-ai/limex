import GoldbachCircleMethodCompanionIntervalEnergyBoundV18496
import GoldbachCircleMethodSupportSeparatedCoefficientMomentsV18490

/-!
# Goldbach V1.8.497: principal block-coefficient bound

The sparse conductor-one moment from V1.8.490 is now bounded by the exact
diagonal coefficient energy plus the retained pairwise-period endpoint cost.
The containing interval `[0,B]` is used explicitly; no equality with the
smaller block is asserted.
-/

set_option autoImplicit false

open scoped BigOperators Classical ComplexConjugate

namespace GoldbachCircleMethodPrincipalBlockCoefficientBoundV18497

open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodFiniteCompanionBindingV18118
open GoldbachCircleMethodLogCutoffPresieveBindingV18120
open GoldbachCircleMethodPrincipalWindowBoundaryV18121
open GoldbachCircleMethodActualCompanionCompleteDiagonalV18204
open GoldbachCircleMethodSupportSeparatedCoefficientMomentsV18490
open GoldbachCircleMethodCompanionIntervalEnergyBoundV18496

/-- The actual principal block moment is controlled without charging a full
character-family cardinality. -/
theorem blockPrincipalCoefficientMoment_le_diagonal_add_quartic
    (Q B : ℕ) (hQ : 1 ≤ Q) (w : ℕ → ℂ)
    (hwReal : ∀ n : ℕ, star (w n) = w n)
    (V : ℝ) (hV : 0 ≤ V)
    (hwBound : ∀ q : PositiveLevel Q,
      (oneLevel hQ).val * q.val ≤ Q ∧
          Nat.Coprime (oneLevel hQ).val q.val →
        ‖w ((oneLevel hQ).val * q.val)‖ ≤ V) :
    blockPrincipalCoefficientMoment Q B w ≤
      ((B + 1 : ℕ) : ℝ) * (∑ q : PositiveLevel Q,
        ‖literalCoefficient (oneLevel hQ) q w‖ ^ 2 *
          (q.val.totient : ℝ)) +
        2 * (Q : ℝ) ^ 4 * V * V := by
  rw [blockPrincipalCoefficientMoment_eq_finiteCompanion Q B hQ w]
  have hsubset : blockCarrier B ⊆ Finset.range (B + 1) := by
    intro n hn
    have hnB : n ≤ B := (Finset.mem_Ioc.mp hn).2
    exact Finset.mem_range.mpr (by omega)
  calc
    (∑ n ∈ blockCarrier B, ‖finiteCompanion (oneLevel hQ) n w‖ ^ 2) ≤
        ∑ n ∈ Finset.range (B + 1),
          ‖finiteCompanion (oneLevel hQ) n w‖ ^ 2 := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
        (fun n _hn _hnot => sq_nonneg ‖finiteCompanion (oneLevel hQ) n w‖)
    _ = ∑ i ∈ Finset.range (B + 1),
          ‖finiteCompanion (oneLevel hQ) (0 + i) w‖ ^ 2 := by simp
    _ ≤ _ := finiteCompanion_interval_energy_le
      (oneLevel hQ) w hwReal 0 (B + 1) V hV hwBound

end GoldbachCircleMethodPrincipalBlockCoefficientBoundV18497
