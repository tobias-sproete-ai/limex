import GoldbachCircleMethodPairwiseActiveAggregateErrorV18319
import GoldbachCircleMethodActualFrozenModelCompleteDiagonalV18213

/-!
# Goldbach V1.8.320: active/principal mirror pairwise-period adapter

The reverse cross channel is proved directly on the same natural interval.
Complete-period commutativity is used only inside the exact finite residue
sum; no unjustified symmetry of the incomplete interval is assumed.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodActivePrincipalPairwisePeriodV18320

open GoldbachCircleMethodActiveActivePairwisePeriodV18317
open GoldbachCircleMethodActualCompanionCompleteDiagonalV18204
open GoldbachCircleMethodActualFrozenModelCompleteDiagonalV18213
open GoldbachCircleMethodActualTwistedCompleteProjectionV18209
open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodFiniteResiduePrefixV1866
open GoldbachCircleMethodPairwiseActiveCostAggregationV18318
open GoldbachCircleMethodPairwisePeriodRemainderBoundV18206
open GoldbachCircleMethodPrincipalActivePairwisePeriodV18316
open GoldbachCircleMethodPrincipalWindowBoundaryV18121
open GoldbachCircleMethodPrimitiveTwistedRamanujanSupportV18208

/-- One active/principal pair on the unchanged interval, completed only on
`lcm(r*l,q)`. -/
theorem active_principal_pair_interval_norm_le {Q : ℕ}
    (hQ : 1 ≤ Q)
    (r l q : PositiveLevel Q)
    (_hadm : r.val * l.val ≤ Q)
    (hcop : Nat.Coprime r.val l.val)
    (chi : {χ : DirichletCharacter ℂ r.val // χ.IsPrimitive})
    (v w : ℕ → ℂ) (N A T : ℕ) (hend : A + T ≤ N + 1)
    (V W : ℝ) (hV : 0 ≤ V) (hW : 0 ≤ W)
    (hv : ‖v (r.val * l.val)‖ ≤ V) (hw : ‖w q.val‖ ≤ W) :
    ‖(∑ i ∈ Finset.range T,
        activeTwistedLiteralTerm r l chi v
            ((N - (A + i) : ℕ) : ZMod (r.val * l.val)) *
          (literalCoefficient (oneLevel hQ) q w *
            unitCharacterSum q.val ((A + i : ℕ) : ZMod q.val))) -
      (T : ℂ) *
        (if q.val = r.val * l.val then
          ((r.val : ℂ) / (r.val.totient : ℂ)) *
            literalCoefficient r l v *
            literalCoefficient (oneLevel hQ) q w *
            twistedRamanujan r.val l.val chi.val
              ((N : ℕ) : ZMod (r.val * l.val))
        else 0)‖ ≤
      2 * (Nat.lcm (r.val * l.val) q.val : ℝ) *
        ((r.val : ℝ) * V) * W := by
  let K := Nat.lcm (r.val * l.val) q.val
  let _ : NeZero K :=
    ⟨Nat.lcm_ne_zero
      (Nat.mul_ne_zero (NeZero.ne r.val) (NeZero.ne l.val))
      (NeZero.ne q.val)⟩
  have hrlK : r.val * l.val ∣ K := Nat.dvd_lcm_left _ _
  have hqK : q.val ∣ K := Nat.dvd_lcm_right _ _
  let f : ZMod K → ℂ := fun x =>
    activeTwistedLiteralTerm r l chi v
      (ZMod.castHom hrlK (ZMod (r.val * l.val)) x)
  let g₀ : ZMod K → ℂ := fun x =>
    literalCoefficient (oneLevel hQ) q w *
      unitCharacterSum q.val (ZMod.castHom hqK (ZMod q.val) x)
  let g : ZMod K → ℂ := fun x => f ((N : ZMod K) - x) * g₀ x
  let d : ℂ :=
    if q.val = r.val * l.val then
      ((r.val : ℂ) / (r.val.totient : ℂ)) *
        literalCoefficient r l v *
        literalCoefficient (oneLevel hQ) q w *
        twistedRamanujan r.val l.val chi.val
          (ZMod.castHom hrlK (ZMod (r.val * l.val)) (N : ZMod K))
    else 0
  have hg : ∀ x, ‖g x‖ ≤ ((r.val : ℝ) * V) * W := by
    intro x
    unfold g f g₀
    rw [norm_mul]
    exact mul_le_mul
      (activeTwistedLiteralTerm_norm_le r l chi v V hV hv _)
      (literal_term_norm_le (oneLevel hQ) q w W hW
        (by simpa [oneLevel] using hw) _)
      (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) hV)
  have hmean : (∑ x : ZMod K, g x) = (K : ℂ) * d := by
    have hcomm := complete_convolution_comm f g₀ (N : ZMod K)
    unfold g
    rw [hcomm]
    unfold f g₀ d activeTwistedLiteralTerm
    rw [show (∑ x : ZMod K,
        (literalCoefficient (oneLevel hQ) q w *
          unitCharacterSum q.val
            (ZMod.castHom hqK (ZMod q.val) ((N : ZMod K) - x))) *
        (((r.val : ℂ) / (r.val.totient : ℂ)) *
          literalCoefficient r l v *
          twistedRamanujan r.val l.val chi.val
            (ZMod.castHom hrlK (ZMod (r.val * l.val)) x))) =
        (literalCoefficient (oneLevel hQ) q w *
          ((r.val : ℂ) / (r.val.totient : ℂ)) *
          literalCoefficient r l v) *
        (∑ x : ZMod K,
          unitCharacterSum q.val
            (ZMod.castHom hqK (ZMod q.val) ((N : ZMod K) - x)) *
          twistedRamanujan r.val l.val chi.val
            (ZMod.castHom hrlK (ZMod (r.val * l.val)) x)) by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro x _hx
          ring]
    rw [twisted_ramanujan_complete_matrix r.val l.val hqK hrlK
      hcop chi.val chi.property (N : ZMod K)]
    by_cases heq : q.val = r.val * l.val
    · rw [if_pos heq, if_pos heq]
      ring
    · rw [if_neg heq, if_neg heq]
      ring
  have hdev := interval_deviation_norm_le g d A T
    (((r.val : ℝ) * V) * W) hg hmean
  have hread :
      (∑ i ∈ Finset.range T, g ((A + i : ℕ) : ZMod K)) =
        ∑ i ∈ Finset.range T,
          activeTwistedLiteralTerm r l chi v
              ((N - (A + i) : ℕ) : ZMod (r.val * l.val)) *
            (literalCoefficient (oneLevel hQ) q w *
              unitCharacterSum q.val ((A + i : ℕ) : ZMod q.val)) := by
    apply Finset.sum_congr rfl
    intro i hi
    have hiN : A + i ≤ N := by
      have := Finset.mem_range.mp hi
      omega
    simp only [g, f, g₀, map_sub, map_natCast, Nat.cast_sub hiN]
  rw [hread] at hdev
  have hdread : d =
      if q.val = r.val * l.val then
        ((r.val : ℂ) / (r.val.totient : ℂ)) *
          literalCoefficient r l v *
          literalCoefficient (oneLevel hQ) q w *
          twistedRamanujan r.val l.val chi.val
            ((N : ℕ) : ZMod (r.val * l.val))
      else 0 := by
    unfold d
    split_ifs
    · congr 1
      simp only [map_natCast]
    · rfl
  rw [hdread] at hdev
  have hmod : ((T % K : ℕ) : ℝ) ≤ (K : ℝ) := by
    exact_mod_cast (Nat.mod_lt T (Nat.pos_of_ne_zero (NeZero.ne K))).le
  exact hdev.trans (by
    dsimp only [K]
    have henv : 0 ≤ ((r.val : ℝ) * V) * W := by positivity
    nlinarith)

/-- Actual centered reverse-cross error. -/
noncomputable def activePrincipalPairError {Q : ℕ} (hQ : 1 ≤ Q)
    (r l q : PositiveLevel Q)
    (chi : {χ : DirichletCharacter ℂ r.val // χ.IsPrimitive})
    (v w : ℕ → ℂ) (N A T : ℕ) : ℂ :=
  (∑ i ∈ Finset.range T,
      activeTwistedLiteralTerm r l chi v
          ((N - (A + i) : ℕ) : ZMod (r.val * l.val)) *
        (literalCoefficient (oneLevel hQ) q w *
          unitCharacterSum q.val ((A + i : ℕ) : ZMod q.val))) -
    (T : ℂ) *
      (if q.val = r.val * l.val then
        ((r.val : ℂ) / (r.val.totient : ℂ)) *
          literalCoefficient r l v *
          literalCoefficient (oneLevel hQ) q w *
          twistedRamanujan r.val l.val chi.val
            ((N : ℕ) : ZMod (r.val * l.val))
      else 0)

/-- Aggregate reverse-cross error on the exact coupled support. -/
noncomputable def activePrincipalAggregateError {Q : ℕ} (hQ : 1 ≤ Q)
    (r : PositiveLevel Q)
    (chi : {χ : DirichletCharacter ℂ r.val // χ.IsPrimitive})
    (v w : ℕ → ℂ) (N A T : ℕ) : ℂ :=
  ∑ l ∈ activeComplementCarrier r, ∑ q : PositiveLevel Q,
    activePrincipalPairError hQ r l q chi v w N A T

theorem activePrincipalAggregateError_norm_le_quartic {Q : ℕ} (hQ : 1 ≤ Q)
    (r : PositiveLevel Q)
    (chi : {χ : DirichletCharacter ℂ r.val // χ.IsPrimitive})
    (v w : ℕ → ℂ) (N A T : ℕ) (hend : A + T ≤ N + 1)
    (V W : ℝ) (hV : 0 ≤ V) (hW : 0 ≤ W)
    (hv : ∀ n : ℕ, ‖v n‖ ≤ V)
    (hw : ∀ q : PositiveLevel Q, ‖w q.val‖ ≤ W) :
    ‖activePrincipalAggregateError hQ r chi v w N A T‖ ≤
      2 * (Q : ℝ) ^ 4 * V * W := by
  apply le_trans (b := principalActivePairwiseCost r W V)
  · unfold activePrincipalAggregateError principalActivePairwiseCost
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro l hl
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro q _hq
    have hsupp := (Finset.mem_filter.mp hl).2
    simpa only [activePrincipalPairError, Nat.lcm_comm, mul_comm,
      mul_left_comm, mul_assoc] using
      (active_principal_pair_interval_norm_le hQ r l q hsupp.1 hsupp.2 chi
        v w N A T hend V W hV hW (hv (r.val * l.val)) (hw q))
  · have h := principalActivePairwiseCost_le_quartic r W V hW hV
    simpa only [mul_comm, mul_left_comm, mul_assoc] using h

end GoldbachCircleMethodActivePrincipalPairwisePeriodV18320
