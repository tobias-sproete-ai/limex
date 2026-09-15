import GoldbachCircleMethodLogarithmicBlockDecayV1875
import Mathlib.Data.Nat.Log

/-! # V1.8.76: finite dyadic coverage of the unchanged prime-pair exceptions.
The original closed even blocks only supply upper bounds. Half-open dyadic
assignment is separate, so no disjointness of closed target blocks is assumed.
-/
set_option autoImplicit false
open scoped BigOperators Classical
open GoldbachPurePrimeAdequacyV15
open GoldbachCircleMethodTwoScaleEvenBlockDefectReserveV1833

namespace GoldbachCircleMethodFiniteDyadicExceptionCarrierV1876

noncomputable def globalExceptions (X : ℕ) : Finset ℕ :=
  (Finset.Icc 4 X).filter (fun N => Even N ∧ ¬ GoldbachAt N)

theorem mem_globalExceptions_iff (X N : ℕ) :
    N ∈ globalExceptions X ↔ 4 ≤ N ∧ N ≤ X ∧ Even N ∧ ¬ GoldbachAt N := by
  simp only [globalExceptions, Finset.mem_filter, Finset.mem_Icc]
  tauto

theorem clog_dyadic_assignment (N : ℕ) (hN : 1 < N) :
    0 < Nat.clog 2 N ∧ 2^((Nat.clog 2 N)-1) < N ∧
      N ≤ 2^(Nat.clog 2 N) ∧ 2^(Nat.clog 2 N) < 2*N := by
  have hj := Nat.clog_pos (by norm_num : 1 < (2 : ℕ)) hN
  have hlo := Nat.pow_pred_clog_lt_self (by norm_num : 1 < (2 : ℕ)) hN
  simp only [Nat.pred_eq_sub_one] at hlo
  have hu := Nat.le_pow_clog (by norm_num : 1 < (2 : ℕ)) N
  have heq : 2^(Nat.clog 2 N) = 2^((Nat.clog 2 N)-1)*2 := by
    conv_lhs => rw [show Nat.clog 2 N = ((Nat.clog 2 N)-1)+1 by omega]
    rw [pow_succ]
  refine ⟨hj, hlo, hu, ?_⟩
  rw [heq]
  omega

theorem globalExceptions_pow_subset (m t : ℕ) :
    globalExceptions (2^m) ⊆
      (Finset.Icc 1 (2^t)) ∪
        (Finset.Icc (t+1) m).biUnion (fun j =>
          (evenTargetBlock (2^j)).filter (fun N => ¬ GoldbachAt N)) := by
  intro N hN
  obtain ⟨h4, hM, he, hn⟩ := (mem_globalExceptions_iff _ _).mp hN
  by_cases hsmall : N ≤ 2^t
  · exact Finset.mem_union_left _ (Finset.mem_Icc.mpr ⟨by omega, hsmall⟩)
  · apply Finset.mem_union_right
    apply Finset.mem_biUnion.mpr
    refine ⟨Nat.clog 2 N, Finset.mem_Icc.mpr ⟨?_, ?_⟩, ?_⟩
    · have h := (Nat.lt_clog_iff_pow_lt (by norm_num : 1 < (2 : ℕ))).mpr
        (show 2^t < N by omega)
      omega
    · exact (Nat.clog_le_iff_le_pow (by norm_num : 1 < (2 : ℕ))).mpr hM
    · have ha := clog_dyadic_assignment N (by omega)
      apply Finset.mem_filter.mpr
      refine ⟨(mem_evenTargetBlock_iff _ _).mpr ⟨h4, ha.2.2.1, he, ha.2.2.2.le⟩, hn⟩

theorem globalExceptions_pow_card_le (m t : ℕ) :
    (globalExceptions (2^m)).card ≤
      2^t + ∑ j ∈ Finset.Icc (t+1) m,
        ((evenTargetBlock (2^j)).filter (fun N => ¬ GoldbachAt N)).card := by
  calc
    _ ≤ ((Finset.Icc 1 (2^t)) ∪
        (Finset.Icc (t+1) m).biUnion (fun j =>
          (evenTargetBlock (2^j)).filter (fun N => ¬ GoldbachAt N))).card :=
      Finset.card_le_card (globalExceptions_pow_subset m t)
    _ ≤ (Finset.Icc 1 (2^t)).card +
        ((Finset.Icc (t+1) m).biUnion (fun j =>
          (evenTargetBlock (2^j)).filter (fun N => ¬ GoldbachAt N))).card :=
      Finset.card_union_le _ _
    _ ≤ (Finset.Icc 1 (2^t)).card +
        ∑ j ∈ Finset.Icc (t+1) m,
          ((evenTargetBlock (2^j)).filter (fun N => ¬ GoldbachAt N)).card :=
      Nat.add_le_add_left Finset.card_biUnion_le _
    _ = _ := by simp

theorem globalExceptions_pow_card_le_real (m t : ℕ) (B : ℕ → ℝ)
    (hB : ∀ j ∈ Finset.Icc (t+1) m,
      (((evenTargetBlock (2^j)).filter (fun N => ¬ GoldbachAt N)).card : ℝ) ≤ B j) :
    ((globalExceptions (2^m)).card : ℝ) ≤ (2 : ℝ)^t + ∑ j ∈ Finset.Icc (t+1) m, B j := by
  have hc : ((globalExceptions (2^m)).card : ℝ) ≤ (2 : ℝ)^t +
      ∑ j ∈ Finset.Icc (t+1) m,
        (((evenTargetBlock (2^j)).filter (fun N => ¬ GoldbachAt N)).card : ℝ) := by
    exact_mod_cast globalExceptions_pow_card_le m t
  exact hc.trans (add_le_add le_rfl (Finset.sum_le_sum hB))

theorem dyadic_geometric_sum (m : ℕ) :
    ∑ j ∈ Finset.range (m+1), (2 : ℝ)^j = (2 : ℝ)^(m+1)-1 := by
  induction m with
  | zero => norm_num
  | succ m ih =>
    rw [Finset.sum_range_succ, ih, pow_succ]
    ring

end GoldbachCircleMethodFiniteDyadicExceptionCarrierV1876
