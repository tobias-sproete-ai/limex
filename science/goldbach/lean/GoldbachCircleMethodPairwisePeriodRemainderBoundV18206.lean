import GoldbachCircleMethodActualCompanionIntervalTransferV18205
set_option autoImplicit false
open scoped BigOperators Classical

namespace GoldbachCircleMethodPairwisePeriodRemainderBoundV18206
open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodFiniteCompanionBindingV18118
open GoldbachCircleMethodFiniteResiduePrefixV1866
open GoldbachCircleMethodActualCompanionPeriodicLiftV18202
open GoldbachCircleMethodMixedRamanujanOrthogonalityV18203
open GoldbachCircleMethodActualCompanionCompleteDiagonalV18204
open GoldbachCircleMethodActualCompanionIntervalTransferV18205
open GoldbachCircleMethodExactPrincipalBoundaryCostV18126

/-- The norm of the exact mean is no larger than a uniform pointwise envelope. -/
theorem complete_mean_norm_le {K : ℕ} [NeZero K]
    (g : ZMod K → ℂ) (d : ℂ) (B : ℝ)
    (hg : ∀ x, ‖g x‖ ≤ B)
    (hmean : (∑ x, g x) = (K : ℂ)*d) : ‖d‖ ≤ B := by
  have h : ‖∑ x, g x‖ ≤ (K : ℝ)*B := by
    calc
      _ ≤ ∑ x, ‖g x‖ := norm_sum_le _ _
      _ ≤ ∑ _x : ZMod K, B := Finset.sum_le_sum (fun x _ => hg x)
      _ = _ := by simp
  rw [hmean, norm_mul, Complex.norm_natCast] at h
  exact le_of_mul_le_mul_left h (show (0 : ℝ)<K by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne K))

/-- Explicit centered interval error. No relation between length T and period K. -/
theorem interval_deviation_norm_le {K : ℕ} [NeZero K]
    (g : ZMod K → ℂ) (d : ℂ) (A T : ℕ) (B : ℝ)
    (hg : ∀ x, ‖g x‖ ≤ B)
    (hmean : (∑ x, g x) = (K : ℂ)*d) :
    ‖(∑ i ∈ Finset.range T, g ((A+i : ℕ) : ZMod K))-(T : ℂ)*d‖ ≤
      2*((T%K : ℕ) : ℝ)*B := by
  have hd := complete_mean_norm_le g d B hg hmean
  have heq :
      (∑ i ∈ Finset.range T, g ((A+i : ℕ) : ZMod K))-(T : ℂ)*d =
        (∑ i ∈ Finset.range (T%K), g ((A+i : ℕ) : ZMod K)) -
          ((T%K : ℕ) : ℂ)*d := by
    rw [residue_interval_decomposition, hmean]
    have hcount : ((T/K : ℕ) : ℂ)*(K : ℂ)+((T%K : ℕ) : ℂ)=(T : ℂ) := by
      exact_mod_cast (show T/K*K+T%K=T by
        rw [Nat.mul_comm (T/K) K, Nat.div_add_mod])
    linear_combination d*hcount
  rw [heq]
  calc
    _ ≤ ‖∑ i ∈ Finset.range (T%K), g ((A+i : ℕ) : ZMod K)‖ +
        ‖((T%K : ℕ) : ℂ)*d‖ := norm_sub_le _ _
    _ ≤ (∑ i ∈ Finset.range (T%K), ‖g ((A+i : ℕ) : ZMod K)‖) +
        ‖((T%K : ℕ) : ℂ)*d‖ := add_le_add (norm_sum_le _ _) le_rfl
    _ ≤ (∑ _i ∈ Finset.range (T%K), B) +
        ((T%K : ℕ) : ℝ)*B := by
      apply add_le_add
      · exact Finset.sum_le_sum (fun i _ => hg _)
      · rw [norm_mul, Complex.norm_natCast]
        exact mul_le_mul_of_nonneg_left hd (Nat.cast_nonneg _)
    _ = _ := by simp; ring

/-- Retain the original cutoff and coprimality when bounding one weighted term. -/
theorem literal_term_norm_le {Q : ℕ} (r q : PositiveLevel Q)
    (w : ℕ → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hw : ‖w (r.val*q.val)‖ ≤ B) (x : ZMod q.val) :
    ‖literalCoefficient r q w * unitCharacterSum q.val x‖ ≤ B := by
  unfold literalCoefficient
  split_ifs
  · have he :
      ((ArithmeticFunction.moebius q.val : ℤ) : ℂ)/(q.val.totient : ℂ) *
        w (r.val*q.val) * unitCharacterSum q.val x =
      (((ArithmeticFunction.moebius q.val : ℤ) : ℂ) *
        unitCharacterSum q.val x / (q.val.totient : ℂ)) * w (r.val*q.val) := by ring
    rw [he, norm_mul]
    exact (mul_le_mul (moebius_character_quotient_norm_le_one q.val x)
      hw (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
  · simpa using hB

/-- Exact mean for one pair on any common period; both literal weights survive. -/
theorem literal_pair_complete_mean {Q K : ℕ} [NeZero K]
    (r s q l : PositiveLevel Q) (v w : ℕ → ℂ)
    (hq : q.val ∣ K) (hl : l.val ∣ K) (N : ℕ) :
    (∑ x : ZMod K,
      (literalCoefficient r q v * unitCharacterSum q.val
        (ZMod.castHom hq (ZMod q.val) ((N : ZMod K)-x))) *
      (literalCoefficient s l w * unitCharacterSum l.val
        (ZMod.castHom hl (ZMod l.val) x))) =
    (K : ℂ) * (if q=l then literalCoefficient r q v * literalCoefficient s q w *
      unitCharacterSum q.val (N : ZMod q.val) else 0) := by
  have he : (∑ x : ZMod K,
      (literalCoefficient r q v * unitCharacterSum q.val
        (ZMod.castHom hq (ZMod q.val) ((N : ZMod K)-x))) *
      (literalCoefficient s l w * unitCharacterSum l.val
        (ZMod.castHom hl (ZMod l.val) x))) =
      (literalCoefficient r q v * literalCoefficient s l w) *
        ∑ x : ZMod K, unitCharacterSum q.val
          (ZMod.castHom hq (ZMod q.val) ((N : ZMod K)-x)) *
          unitCharacterSum l.val (ZMod.castHom hl (ZMod l.val) x) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    ring
  rw [he]
  by_cases h : q=l
  · subst l
    rw [if_pos rfl, lifted_ramanujan_self_convolution hq]
    simp only [map_natCast]
    ring
  · rw [if_neg h, actual_unitCharacterSum_mixed_convolution_zero hq hl
      (fun hv => h (Subtype.ext hv))]
    simp

/-- One actual pair, completed only on lcm(q,l). The error does not use a
common period of all denominators up to Q. Natural endpoints remain exact. -/
theorem literal_pair_interval_norm_le {Q : ℕ}
    (r s q l : PositiveLevel Q) (v w : ℕ → ℂ) (N A T : ℕ)
    (hend : A+T ≤ N+1) (V W : ℝ) (hV : 0 ≤ V) (hW : 0 ≤ W)
    (hv : ‖v (r.val*q.val)‖ ≤ V) (hw : ‖w (s.val*l.val)‖ ≤ W) :
    ‖(∑ i ∈ Finset.range T,
      (literalCoefficient r q v * unitCharacterSum q.val ((N-(A+i) : ℕ) : ZMod q.val)) *
      (literalCoefficient s l w * unitCharacterSum l.val ((A+i : ℕ) : ZMod l.val))) -
      (T : ℂ)*(if q=l then literalCoefficient r q v * literalCoefficient s q w *
        unitCharacterSum q.val (N : ZMod q.val) else 0)‖ ≤
      2*(Nat.lcm q.val l.val : ℝ)*V*W := by
  let K := Nat.lcm q.val l.val
  let _ : NeZero K := ⟨Nat.lcm_ne_zero (NeZero.ne q.val) (NeZero.ne l.val)⟩
  have hq : q.val ∣ K := Nat.dvd_lcm_left _ _
  have hl : l.val ∣ K := Nat.dvd_lcm_right _ _
  let g : ZMod K → ℂ := fun x =>
    (literalCoefficient r q v * unitCharacterSum q.val
      (ZMod.castHom hq (ZMod q.val) ((N : ZMod K)-x))) *
    (literalCoefficient s l w * unitCharacterSum l.val
      (ZMod.castHom hl (ZMod l.val) x))
  have hg : ∀ x, ‖g x‖ ≤ V*W := by
    intro x
    unfold g
    rw [norm_mul]
    exact mul_le_mul (literal_term_norm_le r q v V hV hv _)
      (literal_term_norm_le s l w W hW hw _) (norm_nonneg _) hV
  have hs :
      (∑ i ∈ Finset.range T, g ((A+i : ℕ) : ZMod K)) =
        ∑ i ∈ Finset.range T,
          (literalCoefficient r q v * unitCharacterSum q.val ((N-(A+i) : ℕ) : ZMod q.val)) *
          (literalCoefficient s l w * unitCharacterSum l.val ((A+i : ℕ) : ZMod l.val)) := by
    apply Finset.sum_congr rfl
    intro i hi
    have hiN : A+i ≤ N := by have := Finset.mem_range.mp hi; omega
    simp only [g, map_sub, map_natCast, Nat.cast_sub hiN]
  have h := interval_deviation_norm_le g
    (if q=l then literalCoefficient r q v * literalCoefficient s q w *
      unitCharacterSum q.val (N : ZMod q.val) else 0) A T (V*W) hg
        (literal_pair_complete_mean r s q l v w hq hl N)
  rw [hs] at h
  have hmod : ((T%K : ℕ) : ℝ) ≤ (K : ℝ) := by
    exact_mod_cast (Nat.mod_lt T (Nat.pos_of_ne_zero (NeZero.ne K))).le
  exact h.trans (by dsimp [K] at *; nlinarith [mul_nonneg hV hW])

end GoldbachCircleMethodPairwisePeriodRemainderBoundV18206
