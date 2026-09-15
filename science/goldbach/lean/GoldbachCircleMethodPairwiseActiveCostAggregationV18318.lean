import GoldbachCircleMethodActiveActivePairwisePeriodV18317
import GoldbachCircleMethodExceptionalWeightBoundaryV18128

/-!
# Goldbach V1.8.318: pairwise active-cost aggregation

The local pairwise-period costs from V1.8.316/317 are summed on the genuine
coupled support `r*l ≤ Q`.  The conductor factor is cancelled by the exact
cardinality bound `#\{l : r*l ≤ Q\} ≤ Q/r`; consequently both principal/active
and active/active total costs remain quartic in `Q`.  No common LCM occurs.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodPairwiseActiveCostAggregationV18318

open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodExceptionalWeightBoundaryV18128
open GoldbachCircleMethodRemovedConvolutionNormV18123

/-- The exact coupled and coprime complement carrier at fixed conductor `r`. -/
def activeComplementCarrier {Q : ℕ} (r : PositiveLevel Q) :
    Finset (PositiveLevel Q) :=
  Finset.univ.filter
    (fun l : PositiveLevel Q => r.val * l.val ≤ Q ∧ Nat.Coprime r.val l.val)

/-- Principal/active pairwise boundary costs on the actual admitted support. -/
noncomputable def principalActivePairwiseCost {Q : ℕ}
    (r : PositiveLevel Q) (V W : ℝ) : ℝ :=
  ∑ l ∈ activeComplementCarrier r, ∑ q : PositiveLevel Q,
    2 * (Nat.lcm q.val (r.val * l.val) : ℝ) * V * ((r.val : ℝ) * W)

/-- Active/active pairwise boundary costs on the actual two coupled supports. -/
noncomputable def activeActivePairwiseCost {Q : ℕ}
    (r : PositiveLevel Q) (V W : ℝ) : ℝ :=
  ∑ l ∈ activeComplementCarrier r, ∑ k ∈ activeComplementCarrier r,
    2 * (Nat.lcm (r.val * l.val) (r.val * k.val) : ℝ) *
      ((r.val : ℝ) * V) * ((r.val : ℝ) * W)

private theorem active_complement_card_mul_conductor_le {Q : ℕ}
    (r : PositiveLevel Q) :
    ((activeComplementCarrier r).card : ℝ) *
        (r.val : ℝ) ≤ (Q : ℝ) := by
  have hsubset : activeComplementCarrier r ⊆
      Finset.univ.filter (fun l : PositiveLevel Q => r.val * l.val ≤ Q) := by
    intro l hl
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (Finset.mem_filter.mp hl).2.1⟩
  have hcard : (activeComplementCarrier r).card ≤ Q / r.val :=
    (Finset.card_le_card hsubset).trans (companion_level_count_le Q r)
  have hmul : (Q / r.val) * r.val ≤ Q :=
    (Nat.div_mul_le_self Q r.val)
  exact_mod_cast (Nat.mul_le_mul_right r.val hcard |>.trans hmul)

/-- The principal/active aggregate retains the old `Q^4` boundary order.
The proof uses the coupled carrier count; a rectangular `Q×Q` estimate would
lose one unnecessary conductor factor. -/
theorem principalActivePairwiseCost_le_quartic {Q : ℕ}
    (r : PositiveLevel Q) (V W : ℝ) (hV : 0 ≤ V) (hW : 0 ≤ W) :
    principalActivePairwiseCost r V W ≤ 2 * (Q : ℝ) ^ 4 * V * W := by
  let S := activeComplementCarrier r
  have hterm : ∀ l ∈ S, ∀ q : PositiveLevel Q,
      2 * (Nat.lcm q.val (r.val * l.val) : ℝ) * V * ((r.val : ℝ) * W) ≤
        2 * (Q : ℝ) ^ 2 * V * ((r.val : ℝ) * W) := by
    intro l hl q
    have hadm : r.val * l.val ≤ Q := (Finset.mem_filter.mp hl).2.1
    have hnat : Nat.lcm q.val (r.val * l.val) ≤ Q * Q :=
      (Nat.lcm_le_mul (Nat.pos_of_ne_zero (NeZero.ne q.val))
        (Nat.mul_pos (NeZero.pos r.val) (NeZero.pos l.val))).trans
          (Nat.mul_le_mul (Finset.mem_Icc.mp q.property).2 hadm)
    have hlcm : (Nat.lcm q.val (r.val * l.val) : ℝ) ≤ (Q : ℝ) ^ 2 := by
      exact_mod_cast (show Nat.lcm q.val (r.val * l.val) ≤ Q ^ 2 by
        simpa only [pow_two] using hnat)
    have hscale : 0 ≤ 2 * V * ((r.val : ℝ) * W) := by positivity
    calc
      _ = (Nat.lcm q.val (r.val * l.val) : ℝ) *
          (2 * V * ((r.val : ℝ) * W)) := by ring
      _ ≤ (Q : ℝ) ^ 2 * (2 * V * ((r.val : ℝ) * W)) :=
        mul_le_mul_of_nonneg_right hlcm hscale
      _ = _ := by ring
  unfold principalActivePairwiseCost
  change (∑ l ∈ S, ∑ q : PositiveLevel Q,
    2 * (Nat.lcm q.val (r.val * l.val) : ℝ) * V * ((r.val : ℝ) * W)) ≤ _
  calc
    _ ≤ ∑ l ∈ S, ∑ _q : PositiveLevel Q,
        2 * (Q : ℝ) ^ 2 * V * ((r.val : ℝ) * W) :=
      Finset.sum_le_sum (fun l hl => Finset.sum_le_sum (fun q _ => hterm l hl q))
    _ = (S.card : ℝ) * (Q : ℝ) *
        (2 * (Q : ℝ) ^ 2 * V * ((r.val : ℝ) * W)) := by
      simp
      ring_nf
    _ = (((S.card : ℝ) * (r.val : ℝ)) *
        (2 * (Q : ℝ) ^ 3 * V * W)) := by ring
    _ ≤ (Q : ℝ) * (2 * (Q : ℝ) ^ 3 * V * W) :=
      mul_le_mul_of_nonneg_right (active_complement_card_mul_conductor_le r) (by positivity)
    _ = _ := by ring

/-- The active/active aggregate also remains quartic: two conductor scales are
cancelled by the two exact coupled-support cardinalities. -/
theorem activeActivePairwiseCost_le_quartic {Q : ℕ}
    (r : PositiveLevel Q) (V W : ℝ) (hV : 0 ≤ V) (hW : 0 ≤ W) :
    activeActivePairwiseCost r V W ≤ 2 * (Q : ℝ) ^ 4 * V * W := by
  let S := activeComplementCarrier r
  have hterm : ∀ l ∈ S, ∀ k ∈ S,
      2 * (Nat.lcm (r.val * l.val) (r.val * k.val) : ℝ) *
          ((r.val : ℝ) * V) * ((r.val : ℝ) * W) ≤
        2 * (Q : ℝ) ^ 2 * ((r.val : ℝ) * V) * ((r.val : ℝ) * W) := by
    intro l hl k hk
    have hadm_l : r.val * l.val ≤ Q := (Finset.mem_filter.mp hl).2.1
    have hadm_k : r.val * k.val ≤ Q := (Finset.mem_filter.mp hk).2.1
    have hnat : Nat.lcm (r.val * l.val) (r.val * k.val) ≤ Q * Q :=
      (Nat.lcm_le_mul
        (Nat.mul_pos (NeZero.pos r.val) (NeZero.pos l.val))
        (Nat.mul_pos (NeZero.pos r.val) (NeZero.pos k.val))).trans
          (Nat.mul_le_mul hadm_l hadm_k)
    have hlcm :
        (Nat.lcm (r.val * l.val) (r.val * k.val) : ℝ) ≤ (Q : ℝ) ^ 2 := by
      exact_mod_cast (show Nat.lcm (r.val * l.val) (r.val * k.val) ≤ Q ^ 2 by
        simpa only [pow_two] using hnat)
    have hscale :
        0 ≤ 2 * ((r.val : ℝ) * V) * ((r.val : ℝ) * W) := by positivity
    calc
      _ = (Nat.lcm (r.val * l.val) (r.val * k.val) : ℝ) *
          (2 * ((r.val : ℝ) * V) * ((r.val : ℝ) * W)) := by ring
      _ ≤ (Q : ℝ) ^ 2 *
          (2 * ((r.val : ℝ) * V) * ((r.val : ℝ) * W)) :=
        mul_le_mul_of_nonneg_right hlcm hscale
      _ = _ := by ring
  unfold activeActivePairwiseCost
  change (∑ l ∈ S, ∑ k ∈ S,
    2 * (Nat.lcm (r.val * l.val) (r.val * k.val) : ℝ) *
      ((r.val : ℝ) * V) * ((r.val : ℝ) * W)) ≤ _
  calc
    _ ≤ ∑ l ∈ S, ∑ k ∈ S,
        2 * (Q : ℝ) ^ 2 * ((r.val : ℝ) * V) * ((r.val : ℝ) * W) :=
      Finset.sum_le_sum (fun l hl => Finset.sum_le_sum (fun k hk => hterm l hl k hk))
    _ = (S.card : ℝ) ^ 2 *
        (2 * (Q : ℝ) ^ 2 * ((r.val : ℝ) * V) * ((r.val : ℝ) * W)) := by
      simp [pow_two]
      ring_nf
    _ = (((S.card : ℝ) * (r.val : ℝ)) ^ 2) *
        (2 * (Q : ℝ) ^ 2 * V * W) := by ring
    _ ≤ ((Q : ℝ) ^ 2) * (2 * (Q : ℝ) ^ 2 * V * W) := by
      have hc := active_complement_card_mul_conductor_le r
      have hs0 : 0 ≤ (S.card : ℝ) * (r.val : ℝ) := by positivity
      have hQ0 : 0 ≤ (Q : ℝ) := by positivity
      have hsq : ((S.card : ℝ) * (r.val : ℝ)) ^ 2 ≤ (Q : ℝ) ^ 2 := by
        nlinarith
      exact mul_le_mul_of_nonneg_right hsq (by positivity)
    _ = _ := by ring

end GoldbachCircleMethodPairwiseActiveCostAggregationV18318
