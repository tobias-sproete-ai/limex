import GoldbachCircleMethodActualCompanionCompleteDiagonalV18204
set_option autoImplicit false
open scoped BigOperators Classical

namespace GoldbachCircleMethodActualCompanionIntervalTransferV18205

open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodFiniteCompanionBindingV18118
open GoldbachCircleMethodFiniteResiduePrefixV1866
open GoldbachCircleMethodActualCompanionPeriodicLiftV18202
open GoldbachCircleMethodActualCompanionCompleteDiagonalV18204

/-- Quotient/remainder decomposition of the original residue evaluation.
No bound on the remainder, or size of K relative to T, is asserted. -/
theorem residue_interval_decomposition {K : ℕ} [NeZero K]
    (g : ZMod K → ℂ) (A T : ℕ) :
    (∑ i ∈ Finset.range T, g ((A+i : ℕ) : ZMod K)) =
      (T/K : ℕ) * (∑ x : ZMod K, g x) +
        ∑ i ∈ Finset.range (T%K), g ((A+i : ℕ) : ZMod K) := by
  let f : ZMod K → ℂ := fun x => g ((A : ZMod K)+x)
  have hfull : (∑ x : ZMod K, f x) = ∑ x : ZMod K, g x := by
    exact Equiv.sum_comp (Equiv.addLeft (A : ZMod K)) g
  have hsplit :
      (∑ i ∈ Finset.range T, f (i : ZMod K)) =
        (T/K : ℕ) * (∑ x : ZMod K, f x) +
          ∑ i ∈ Finset.range (T%K), f (i : ZMod K) := by
    calc
      _ = ∑ i ∈ Finset.range ((T/K)*K+T%K), f (i : ZMod K) := by
        rw [Nat.mul_comm (T/K) K, Nat.div_add_mod]
      _ = _ := by
        rw [Finset.sum_range_add, repeated_residue_periods_complex]
        simp only [Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, mul_zero, zero_add]
  rw [hfull] at hsplit
  simpa only [f, Nat.cast_add] using hsplit

/-- The diagonal uses exactly the two coefficients of the V204 identity. -/
noncomputable def diagonalValue {Q K : ℕ} [NeZero K]
    (hK : ∀ l : PositiveLevel Q, l.val ∣ K)
    (r s : PositiveLevel Q) (v w : ℕ → ℂ) (N : ℕ) : ℂ :=
  ∑ l : PositiveLevel Q,
    literalCoefficient r l v * literalCoefficient s l w *
      unitCharacterSum l.val (ZMod.castHom (hK l) (ZMod l.val) (N : ZMod K))

/-- The finite remainder is centered by the exact number of residual residues.
It is retained as a signed complex term, never declared negligible. -/
noncomputable def intervalRemainder {Q K : ℕ} [NeZero K]
    (hK : ∀ l : PositiveLevel Q, l.val ∣ K)
    (r s : PositiveLevel Q) (v w : ℕ → ℂ) (N A T : ℕ) : ℂ :=
  (∑ i ∈ Finset.range (T%K),
    periodicCompanion r v ((N : ZMod K)-((A+i : ℕ) : ZMod K)) *
      periodicCompanion s w ((A+i : ℕ) : ZMod K)) -
    (T%K : ℕ) * diagonalValue hK r s v w N

/-- The interval is half-open and its final included point cannot exceed N.
This is the explicit bridge from Nat subtraction to modular subtraction. -/
theorem natural_interval_eq_residue_interval {Q K : ℕ} [NeZero K]
    (hK : ∀ l : PositiveLevel Q, l.val ∣ K)
    (r s : PositiveLevel Q) (v w : ℕ → ℂ) (N A T : ℕ)
    (hend : A+T ≤ N+1) :
    (∑ i ∈ Finset.range T,
      finiteCompanion r (N-(A+i)) v * finiteCompanion s (A+i) w) =
      ∑ i ∈ Finset.range T,
        periodicCompanion r v ((N : ZMod K)-((A+i : ℕ) : ZMod K)) *
          periodicCompanion s w ((A+i : ℕ) : ZMod K) := by
  apply Finset.sum_congr rfl
  intro i hi
  have hiN : A+i ≤ N := by have := Finset.mem_range.mp hi; omega
  rw [← periodicCompanion_natCast hK r v, ← periodicCompanion_natCast hK s w,
    Nat.cast_sub hiN]

/-- Exact interval transfer: the complete-period diagonal is not silently
substituted for the finite interval; the residual is explicit. -/
theorem actual_companion_interval_decomposition {Q K : ℕ} [NeZero K]
    (hK : ∀ l : PositiveLevel Q, l.val ∣ K)
    (r s : PositiveLevel Q) (v w : ℕ → ℂ) (N A T : ℕ)
    (hend : A+T ≤ N+1) :
    (∑ i ∈ Finset.range T,
      finiteCompanion r (N-(A+i)) v * finiteCompanion s (A+i) w) =
      (T : ℂ) * diagonalValue hK r s v w N +
        intervalRemainder hK r s v w N A T := by
  rw [natural_interval_eq_residue_interval hK r s v w N A T hend,
    residue_interval_decomposition
      (fun x : ZMod K => periodicCompanion r v ((N : ZMod K)-x) *
        periodicCompanion s w x) A T,
    actual_companion_complete_diagonal hK]
  change ((T/K : ℕ) : ℂ) * ((K : ℂ) * diagonalValue hK r s v w N) + _ = _
  have hcount : ((T/K : ℕ) : ℂ)*(K : ℂ)+((T%K : ℕ) : ℂ) = (T : ℂ) := by
    exact_mod_cast (show T/K*K+T%K=T by
      rw [Nat.mul_comm (T/K) K, Nat.div_add_mod])
  unfold intervalRemainder
  linear_combination diagonalValue hK r s v w N * hcount

/-- When the interval length is a multiple of K, the remainder is exactly zero. -/
theorem intervalRemainder_eq_zero_of_dvd {Q K : ℕ} [NeZero K]
    (hK : ∀ l : PositiveLevel Q, l.val ∣ K)
    (r s : PositiveLevel Q) (v w : ℕ → ℂ) (N A T : ℕ) (hT : K ∣ T) :
    intervalRemainder hK r s v w N A T = 0 := by
  simp [intervalRemainder, Nat.mod_eq_zero_of_dvd hT]

end GoldbachCircleMethodActualCompanionIntervalTransferV18205
