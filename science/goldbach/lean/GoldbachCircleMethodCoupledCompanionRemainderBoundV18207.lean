import GoldbachCircleMethodPairwisePeriodRemainderBoundV18206
set_option autoImplicit false
open scoped BigOperators Classical

namespace GoldbachCircleMethodCoupledCompanionRemainderBoundV18207
open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodFiniteCompanionBindingV18118
open GoldbachCircleMethodFiniteResiduePrefixV1866
open GoldbachCircleMethodActualCompanionCompleteDiagonalV18204
open GoldbachCircleMethodPairwisePeriodRemainderBoundV18206
open GoldbachCircleMethodRemovedConvolutionNormV18123

/-- Exact expansion on natural inputs; no periodic or support replacement. -/
theorem naturalCompanion_expansion {Q : ℕ} (r : PositiveLevel Q)
    (n : ℕ) (w : ℕ → ℂ) :
    finiteCompanion r n w =
      ∑ q : PositiveLevel Q, literalCoefficient r q w *
        unitCharacterSum q.val (n : ZMod q.val) := by
  unfold finiteCompanion literalCoefficient
  apply Finset.sum_congr rfl
  intro q _
  split_ifs <;> ring

/-- Envelope hypotheses apply only on the original two admitted supports.
Inactive pairs contribute exactly zero, not an artificial rectangular error. -/
theorem admitted_pair_interval_norm_le {Q : ℕ}
    (r s q l : PositiveLevel Q) (v w : ℕ → ℂ) (N A T : ℕ)
    (hend : A+T ≤ N+1) (V W : ℝ) (hV : 0 ≤ V) (hW : 0 ≤ W)
    (hv : r.val*q.val ≤ Q ∧ Nat.Coprime r.val q.val → ‖v (r.val*q.val)‖ ≤ V)
    (hw : s.val*l.val ≤ Q ∧ Nat.Coprime s.val l.val → ‖w (s.val*l.val)‖ ≤ W) :
    ‖(∑ i ∈ Finset.range T,
      (literalCoefficient r q v * unitCharacterSum q.val ((N-(A+i) : ℕ) : ZMod q.val)) *
      (literalCoefficient s l w * unitCharacterSum l.val ((A+i : ℕ) : ZMod l.val))) -
      (T : ℂ)*(if q=l then literalCoefficient r q v * literalCoefficient s q w *
        unitCharacterSum q.val (N : ZMod q.val) else 0)‖ ≤
      if (r.val*q.val ≤ Q ∧ Nat.Coprime r.val q.val) ∧
         (s.val*l.val ≤ Q ∧ Nat.Coprime s.val l.val)
      then 2*(Nat.lcm q.val l.val : ℝ)*V*W else 0 := by
  by_cases hr : r.val*q.val ≤ Q ∧ Nat.Coprime r.val q.val
  · by_cases hs : s.val*l.val ≤ Q ∧ Nat.Coprime s.val l.val
    · conv_rhs => rw [if_pos ⟨hr, hs⟩]
      exact literal_pair_interval_norm_le r s q l v w N A T hend V W hV hW
        (hv hr) (hw hs)
    · have hz : literalCoefficient s l w = 0 := by simp [literalCoefficient, hs]
      simp only [hs, and_false, if_false]
      by_cases hql : q=l
      · subst l
        simp [hz]
      · simp [hz, hql]
  · have hz : literalCoefficient r q v = 0 := by simp [literalCoefficient, hr]
    simp only [hr, false_and, if_false]
    simp [hz]

/-- The centered original convolution is exactly the sum of its pairwise errors. -/
theorem actual_centered_convolution_eq_pair_sum {Q : ℕ}
    (r s : PositiveLevel Q) (v w : ℕ → ℂ) (N A T : ℕ) :
    (∑ i ∈ Finset.range T, finiteCompanion r (N-(A+i)) v * finiteCompanion s (A+i) w) -
      (T : ℂ)*(∑ q : PositiveLevel Q, literalCoefficient r q v *
        literalCoefficient s q w * unitCharacterSum q.val (N : ZMod q.val)) =
    ∑ q : PositiveLevel Q, ∑ l : PositiveLevel Q,
      ((∑ i ∈ Finset.range T,
        (literalCoefficient r q v * unitCharacterSum q.val ((N-(A+i) : ℕ) : ZMod q.val)) *
        (literalCoefficient s l w * unitCharacterSum l.val ((A+i : ℕ) : ZMod l.val))) -
        (T : ℂ)*(if q=l then literalCoefficient r q v * literalCoefficient s q w *
          unitCharacterSum q.val (N : ZMod q.val) else 0)) := by
  have he :
      (∑ i ∈ Finset.range T, finiteCompanion r (N-(A+i)) v * finiteCompanion s (A+i) w) =
      ∑ q : PositiveLevel Q, ∑ l : PositiveLevel Q, ∑ i ∈ Finset.range T,
        (literalCoefficient r q v * unitCharacterSum q.val ((N-(A+i) : ℕ) : ZMod q.val)) *
        (literalCoefficient s l w * unitCharacterSum l.val ((A+i : ℕ) : ZMod l.val)) := by
    simp_rw [naturalCompanion_expansion, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro q _
    rw [Finset.sum_comm]
  rw [he]
  simp only [Finset.sum_sub_distrib, mul_ite, mul_zero, Finset.sum_ite_eq,
    Finset.mem_univ, if_true, ← Finset.mul_sum]

/-- Explicit local-period cost summed on the actual coupled supports. -/
theorem actual_companion_interval_coupled_cost {Q : ℕ}
    (r s : PositiveLevel Q) (v w : ℕ → ℂ) (N A T : ℕ)
    (hend : A+T ≤ N+1) (V W : ℝ) (hV : 0 ≤ V) (hW : 0 ≤ W)
    (hv : ∀ q : PositiveLevel Q,
      r.val*q.val ≤ Q ∧ Nat.Coprime r.val q.val → ‖v (r.val*q.val)‖ ≤ V)
    (hw : ∀ l : PositiveLevel Q,
      s.val*l.val ≤ Q ∧ Nat.Coprime s.val l.val → ‖w (s.val*l.val)‖ ≤ W) :
    ‖(∑ i ∈ Finset.range T, finiteCompanion r (N-(A+i)) v * finiteCompanion s (A+i) w) -
      (T : ℂ)*(∑ q : PositiveLevel Q, literalCoefficient r q v *
        literalCoefficient s q w * unitCharacterSum q.val (N : ZMod q.val))‖ ≤
    ∑ q : PositiveLevel Q, ∑ l : PositiveLevel Q,
      if (r.val*q.val ≤ Q ∧ Nat.Coprime r.val q.val) ∧
         (s.val*l.val ≤ Q ∧ Nat.Coprime s.val l.val)
      then 2*(Nat.lcm q.val l.val : ℝ)*V*W else 0 := by
  rw [actual_centered_convolution_eq_pair_sum]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro q _
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro l _
  exact admitted_pair_interval_norm_le r s q l v w N A T hend V W hV hW (hv q) (hw l)

/-- Conservative rectangular majorant of the explicitly retained coupled cost.
This Q^4 loss is not an asymptotic saving. -/
theorem coupled_cost_le_quartic {Q : ℕ} (r s : PositiveLevel Q)
    (V W : ℝ) (hV : 0 ≤ V) (hW : 0 ≤ W) :
    (∑ q : PositiveLevel Q, ∑ l : PositiveLevel Q,
      if (r.val*q.val ≤ Q ∧ Nat.Coprime r.val q.val) ∧
         (s.val*l.val ≤ Q ∧ Nat.Coprime s.val l.val)
      then 2*(Nat.lcm q.val l.val : ℝ)*V*W else 0) ≤
      2*(Q : ℝ)^4*V*W := by
  have hterm : ∀ q l : PositiveLevel Q,
      (if (r.val*q.val ≤ Q ∧ Nat.Coprime r.val q.val) ∧
          (s.val*l.val ≤ Q ∧ Nat.Coprime s.val l.val)
       then 2*(Nat.lcm q.val l.val : ℝ)*V*W else 0) ≤ 2*(Q : ℝ)^2*V*W := by
    intro q l
    have hc : (Nat.lcm q.val l.val : ℝ) ≤ (Q : ℝ)^2 := by
      have hnat : Nat.lcm q.val l.val ≤ Q*Q :=
        (Nat.lcm_le_mul (Nat.pos_of_ne_zero (NeZero.ne q.val))
          (Nat.pos_of_ne_zero (NeZero.ne l.val))).trans (Nat.mul_le_mul
          (Finset.mem_Icc.mp q.property).2 (Finset.mem_Icc.mp l.property).2)
      exact_mod_cast (show Nat.lcm q.val l.val ≤ Q^2 by simpa only [pow_two] using hnat)
    split_ifs
    · exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc (by norm_num)) hV) hW
    · positivity
  calc
    _ ≤ ∑ _q : PositiveLevel Q, ∑ _l : PositiveLevel Q, 2*(Q : ℝ)^2*V*W := by
      exact Finset.sum_le_sum (fun q _ => Finset.sum_le_sum (fun l _ => hterm q l))
    _ = _ := by simp; ring

/-- Whole actual interval convolution, with its exact diagonal and explicit Q^4 cost. -/
theorem actual_companion_interval_quartic_bound {Q : ℕ}
    (r s : PositiveLevel Q) (v w : ℕ → ℂ) (N A T : ℕ)
    (hend : A+T ≤ N+1) (V W : ℝ) (hV : 0 ≤ V) (hW : 0 ≤ W)
    (hv : ∀ q : PositiveLevel Q,
      r.val*q.val ≤ Q ∧ Nat.Coprime r.val q.val → ‖v (r.val*q.val)‖ ≤ V)
    (hw : ∀ l : PositiveLevel Q,
      s.val*l.val ≤ Q ∧ Nat.Coprime s.val l.val → ‖w (s.val*l.val)‖ ≤ W) :
    ‖(∑ i ∈ Finset.range T, finiteCompanion r (N-(A+i)) v * finiteCompanion s (A+i) w) -
      (T : ℂ)*(∑ q : PositiveLevel Q, literalCoefficient r q v *
        literalCoefficient s q w * unitCharacterSum q.val (N : ZMod q.val))‖ ≤
      2*(Q : ℝ)^4*V*W :=
  (actual_companion_interval_coupled_cost r s v w N A T hend V W hV hW hv hw).trans
    (coupled_cost_le_quartic r s V W hV hW)

end GoldbachCircleMethodCoupledCompanionRemainderBoundV18207
