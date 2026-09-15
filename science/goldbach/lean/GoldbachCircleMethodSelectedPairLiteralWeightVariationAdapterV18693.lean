import GoldbachCircleMethodSelectedPairEvenTargetReindexV18692

/-!
# V1.8.693: literal selected-pair weight-variation adapter

This module closes only the algebraic bookkeeping left visible by V1.8.692.
The terminal half-grid weight at `n=M` is zero because the unchanged target
indicator rejects `2*M`.  A general finite total-variation estimate is proved
against the literal `L1` mass, including the edge cases `T=0` and `T=1`.

The V1.8.692 Abel estimate is then instantiated at `T=M+1`, and finite triangle
inequalities bind the complete ordered selected-pair off-diagonal Gram term to
the fully explicit sum of pair-local ceilings
`q*r*phi(q)*phi(r)` times the literal weight variation.

No smallness, global summability, moment estimate, exceptional-set result, or
Goldbach conclusion is asserted.

`proof_status = NO_PROOF`.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodSelectedPairLiteralWeightVariationAdapterV18693

open GoldbachCircleMethodTwoScaleEvenBlockDefectReserveV1833
open GoldbachCircleMethodOddChannelEventualAbsorptionV18658
open GoldbachCircleMethodFullDenominatorFourClassPartitionV18688
open GoldbachCircleMethodFullChannelPartitionedGramV18689
open GoldbachCircleMethodSelectedPairEvenTargetReindexV18692

/-- The retained target indicator forces the literal terminal weight to zero.
No analytic estimate or cancellation is used. -/
theorem selectedPairHalfExactWeight_terminal_zero
    (M : Nat)
    (q r : PairedOddBase (oddProjectRadius M))
    (a b : Nat) :
    selectedPairHalfExactWeight M q r M a b = 0 := by
  unfold selectedPairHalfExactWeight
  rw [if_neg]
  intro hgate
  have htarget := (mem_evenTargetBlock_iff M (2 * M)).mp hgate.1
  omega

/-- The shifted absolute-value prefix is contained in the full prefix.  This
elementary lemma is valid also for `T=0` and `T=1`. -/
theorem sum_range_pred_shift_abs_le_sum_range_abs
    (w : Nat → Real) (T : Nat) :
    (∑ n ∈ Finset.range (T - 1), |w (n + 1)|) ≤
      ∑ n ∈ Finset.range T, |w n| := by
  induction T with
  | zero => simp
  | succ T ih =>
      cases T with
      | zero => simp
      | succ T =>
          simpa [Finset.sum_range_succ, Nat.succ_eq_add_one,
            Nat.add_assoc] using add_le_add ih (le_refl |w (T + 1)|)

/-- The unshifted predecessor prefix is contained in the full prefix. -/
theorem sum_range_pred_abs_le_sum_range_abs
    (w : Nat → Real) (T : Nat) :
    (∑ n ∈ Finset.range (T - 1), |w n|) ≤
      ∑ n ∈ Finset.range T, |w n| := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro n hn
    have hnlt : n < T - 1 := Finset.mem_range.mp hn
    exact Finset.mem_range.mpr (by omega)
  · intro n _hnT _hnPred
    exact abs_nonneg (w n)

/-- General finite total variation is bounded by twice the literal `L1` mass.
This is deliberately a non-small ceiling and makes no regularity assumption
on `w`. -/
theorem totalVariation_le_two_mul_sum_abs
    (w : Nat → Real) (T : Nat) :
    (∑ n ∈ Finset.range (T - 1), |w (n + 1) - w n|) ≤
      2 * (∑ n ∈ Finset.range T, |w n|) := by
  calc
    (∑ n ∈ Finset.range (T - 1), |w (n + 1) - w n|) ≤
        ∑ n ∈ Finset.range (T - 1), (|w (n + 1)| + |w n|) := by
      apply Finset.sum_le_sum
      intro n _hn
      exact abs_sub (w (n + 1)) (w n)
    _ = (∑ n ∈ Finset.range (T - 1), |w (n + 1)|) +
          ∑ n ∈ Finset.range (T - 1), |w n| := by
      rw [Finset.sum_add_distrib]
    _ ≤ (∑ n ∈ Finset.range T, |w n|) +
          ∑ n ∈ Finset.range T, |w n| :=
      add_le_add
        (sum_range_pred_shift_abs_le_sum_range_abs w T)
        (sum_range_pred_abs_le_sum_range_abs w T)
    _ = 2 * (∑ n ∈ Finset.range T, |w n|) := by ring

/-- The literal V1.8.692 weight variation has a general non-small `L1`
ceiling.  All target/fiber indicators, moving notches, masses and four sinc
radii remain inside the summand. -/
theorem selectedPairHalfWeightVariation_le_two_mul_sum_abs
    (M : Nat)
    (q r : PairedOddBase (oddProjectRadius M))
    (a b T : Nat) :
    selectedPairHalfWeightVariation M q r a b T ≤
      2 * (∑ n ∈ Finset.range T,
        |selectedPairHalfExactWeight M q r n a b|) := by
  exact totalVariation_le_two_mul_sum_abs
    (fun n => selectedPairHalfExactWeight M q r n a b) T

/-- Pair-local ceiling appearing in the exact Abel reduction. -/
noncomputable def selectedPairLocalPrefixCeiling
    {R : Nat} (q r : PairedOddBase R) : Real :=
  ((q.val.val * r.val.val : Nat) : Real) *
    ((q.val.val.totient : Real) * (r.val.val.totient : Real))

/-- Abel at the actual full half-grid length `M+1`.  The terminal term is
removed only through `selectedPairHalfExactWeight_terminal_zero`. -/
theorem selectedPairHalfGrid_sum_abel_variation
    (M : Nat)
    (q r : PairedOddBase (oddProjectRadius M))
    (hrErase : r ∈ Finset.univ.erase q)
    (a b : Nat) :
    |∑ n ∈ Finset.range M.succ,
        selectedPairHalfGridTerm M q r n a b| ≤
      selectedPairLocalPrefixCeiling q r *
        selectedPairHalfWeightVariation M q r a b M.succ := by
  have h := selectedPairEvenStep_actualWeight_abel
    M q r hrErase a b M.succ (Nat.succ_le_succ (Nat.zero_le M))
  unfold selectedPairHalfGridTerm
  simp only [Nat.succ_sub_one] at h
  rw [selectedPairHalfExactWeight_terminal_zero M q r a b] at h
  simpa [selectedPairLocalPrefixCeiling, mul_comm] using h

/-- Finite triangle aggregation over the two literal fiber boxes for one
ordered selected denominator pair. -/
theorem selectedPair_halfGrid_fiber_triangle
    (M : Nat)
    (q r : PairedOddBase (oddProjectRadius M))
    (hrErase : r ∈ Finset.univ.erase q) :
    |∑ n ∈ Finset.range M.succ,
        ∑ a ∈ Finset.range M.succ,
          ∑ b ∈ Finset.range M.succ,
            selectedPairHalfGridTerm M q r n a b| ≤
      ∑ a ∈ Finset.range M.succ,
        ∑ b ∈ Finset.range M.succ,
          selectedPairLocalPrefixCeiling q r *
            selectedPairHalfWeightVariation M q r a b M.succ := by
  have hreindex :
      (∑ n ∈ Finset.range M.succ,
          ∑ a ∈ Finset.range M.succ,
            ∑ b ∈ Finset.range M.succ,
              selectedPairHalfGridTerm M q r n a b) =
        ∑ a ∈ Finset.range M.succ,
          ∑ b ∈ Finset.range M.succ,
            ∑ n ∈ Finset.range M.succ,
              selectedPairHalfGridTerm M q r n a b := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _ha
    rw [Finset.sum_comm]
  rw [hreindex]
  calc
    |∑ a ∈ Finset.range M.succ,
        ∑ b ∈ Finset.range M.succ,
          ∑ n ∈ Finset.range M.succ,
            selectedPairHalfGridTerm M q r n a b| ≤
        ∑ a ∈ Finset.range M.succ,
          |∑ b ∈ Finset.range M.succ,
            ∑ n ∈ Finset.range M.succ,
              selectedPairHalfGridTerm M q r n a b| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a ∈ Finset.range M.succ,
          ∑ b ∈ Finset.range M.succ,
            |∑ n ∈ Finset.range M.succ,
              selectedPairHalfGridTerm M q r n a b| := by
      apply Finset.sum_le_sum
      intro a _ha
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro a _ha
      apply Finset.sum_le_sum
      intro b _hb
      exact selectedPairHalfGrid_sum_abel_variation M q r hrErase a b

/-- Complete exact ordered selected-pair Gram ceiling in the project
normalization.  Every factor is explicit and pair-local; the literal variation
is not asserted small or globally summable. -/
theorem orderedOffDiagonalGram_abs_le_literalWeightVariation
    (M : Nat) :
    |orderedOffDiagonalGram (evenTargetBlock M)
        (projectPairedBaseContribution M)| ≤
      ∑ q : PairedOddBase (oddProjectRadius M),
        ∑ r ∈ Finset.univ.erase q,
          ∑ a ∈ Finset.range M.succ,
            ∑ b ∈ Finset.range M.succ,
              selectedPairLocalPrefixCeiling q r *
                selectedPairHalfWeightVariation M q r a b M.succ := by
  rw [orderedOffDiagonalGram_eq_halfGrid]
  calc
    |∑ q : PairedOddBase (oddProjectRadius M),
        ∑ r ∈ Finset.univ.erase q,
          ∑ n ∈ Finset.range M.succ,
            ∑ a ∈ Finset.range M.succ,
              ∑ b ∈ Finset.range M.succ,
                selectedPairHalfGridTerm M q r n a b| ≤
      ∑ q : PairedOddBase (oddProjectRadius M),
        |∑ r ∈ Finset.univ.erase q,
          ∑ n ∈ Finset.range M.succ,
            ∑ a ∈ Finset.range M.succ,
              ∑ b ∈ Finset.range M.succ,
                selectedPairHalfGridTerm M q r n a b| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ q : PairedOddBase (oddProjectRadius M),
        ∑ r ∈ Finset.univ.erase q,
          |∑ n ∈ Finset.range M.succ,
            ∑ a ∈ Finset.range M.succ,
              ∑ b ∈ Finset.range M.succ,
                selectedPairHalfGridTerm M q r n a b| := by
      apply Finset.sum_le_sum
      intro q _hq
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro q _hq
      apply Finset.sum_le_sum
      intro r hr
      exact selectedPair_halfGrid_fiber_triangle M q r hr

end GoldbachCircleMethodSelectedPairLiteralWeightVariationAdapterV18693
