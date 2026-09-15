import GoldbachCircleMethodTotientFourthDivisorReindexV18564
import Mathlib.Data.Nat.Factorization.Basic

/-!
# Goldbach V1.8.565: exact finite divisor-incidence transposition

The squarefree divisor carrier from V1.8.564 is embedded into the full
positive divisor incidence relation.  For a fixed positive divisor `d`, its
multiplicity in `[1,Q]` is exactly `Q / d`.  This is a finite equality; no
Euler-kernel convergence or asymptotic estimate is asserted here.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodDivisorIncidenceTranspositionV18565

open GoldbachCircleMethodTotientFourthDivisorReindexV18564

theorem totientFourthDivisorCarrier_mem_dvd
    {n d : ℕ} (hd : d ∈ totientFourthDivisorCarrier n) : d ∣ n := by
  rw [totientFourthDivisorCarrier, Finset.mem_image] at hd
  rcases hd with ⟨t, ht, rfl⟩
  exact totientFourthSubsetDivisor_dvd (Finset.mem_powerset.mp ht)

theorem totientFourthDivisorCarrier_mem_pos
    {n d : ℕ} (hd : d ∈ totientFourthDivisorCarrier n) : 0 < d := by
  rw [totientFourthDivisorCarrier, Finset.mem_image] at hd
  rcases hd with ⟨t, ht, rfl⟩
  exact Nat.pos_of_ne_zero
    (totientFourthSubsetDivisor_ne_zero (Finset.mem_powerset.mp ht))

theorem totientFourthDivisorCarrier_subset_Icc
    {Q n : ℕ} (hn : n ∈ Finset.Icc 1 Q) :
    totientFourthDivisorCarrier n ⊆ Finset.Icc 1 Q := by
  intro d hd
  have hdpos := totientFourthDivisorCarrier_mem_pos hd
  have hdn := totientFourthDivisorCarrier_mem_dvd hd
  exact Finset.mem_Icc.mpr ⟨hdpos,
    (Nat.le_of_dvd (Finset.mem_Icc.mp hn).1 hdn).trans
      (Finset.mem_Icc.mp hn).2⟩

/-- The positive multiples of `d` in `[1,Q]` are counted exactly by
natural-number division. -/
theorem positive_prefix_divisor_card (Q d : ℕ) :
    ((Finset.Icc 1 Q).filter (fun n => d ∣ n)).card = Q / d := by
  have hIccIoc : Finset.Icc 1 Q = Finset.Ioc 0 Q := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_Ioc]
    omega
  rw [hIccIoc]
  exact Nat.Ioc_filter_dvd_card_eq_div Q d

/-- Exact transposition of a finite weighted divisor-incidence sum. -/
theorem weighted_positive_divisor_incidence_eq
    (Q : ℕ) (w : ℕ → ℝ) :
    (∑ n ∈ Finset.Icc 1 Q,
      ∑ d ∈ Finset.Icc 1 Q, if d ∣ n then w d else 0) =
      ∑ d ∈ Finset.Icc 1 Q, ((Q / d : ℕ) : ℝ) * w d := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _hd
  calc
    (∑ n ∈ Finset.Icc 1 Q, if d ∣ n then w d else 0) =
        ∑ n ∈ (Finset.Icc 1 Q).filter (fun n => d ∣ n), w d := by
      simp only [Finset.sum_filter]
    _ = (((Finset.Icc 1 Q).filter (fun n => d ∣ n)).card : ℝ) * w d := by
      simp
    _ = ((Q / d : ℕ) : ℝ) * w d := by
      rw [positive_prefix_divisor_card]

end GoldbachCircleMethodDivisorIncidenceTranspositionV18565
