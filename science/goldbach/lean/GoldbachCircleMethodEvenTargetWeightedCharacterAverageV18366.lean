import GoldbachCircleMethodCharacterAverageSignObstructionV18365
import GoldbachCircleMethodPairwiseAbelVariationV18327
import GoldbachCircleMethodActualCompanionIntervalTransferV18205

/-!
# Goldbach V1.8.366: even-target weighted character average

The pairwise `Q^4` boundary route leaves an exact arithmetic mean rather than
the enormous common-LCM remainder.  This module tests the next possible
interface: averaging the surviving first character marginal over consecutive
even targets.

An affine permutation of `ZMod r` proves exact cancellation over one complete
target period whenever multiplication by two is invertible modulo `r`.
Quotient/remainder decomposition then bounds every incomplete prefix by `r`.
Finite Abel summation transports this to arbitrary real target weights with a
bound `r * (1 + totalVariation)`.

The final theorem records the obstruction that remains: a target-independent
second marginal survives complete target averaging at linear size.  No
exceptional-zero existence, exceptional-set estimate, or Goldbach conclusion
is asserted.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodEvenTargetWeightedCharacterAverageV18366

open GoldbachCircleMethodActualCompanionIntervalTransferV18205
open GoldbachCircleMethodActualCompanionPeriodicLiftV18202
open GoldbachCircleMethodPairwiseAbelVariationV18327

/-- Translation followed by multiplication by a unit permutes the complete
residue system, so a nontrivial character still has zero complete sum. -/
theorem affine_character_sum_eq_zero
    (r : ℕ) [NeZero r]
    (chi : DirichletCharacter ℂ r) (hne : chi ≠ 1)
    (A : ZMod r) (u : (ZMod r)ˣ) :
    ∑ x : ZMod r, chi (A + (u : ZMod r) * x) = 0 := by
  have hbij : Function.Bijective
      (fun x : ZMod r => A + (u : ZMod r) * x) :=
    (Equiv.addLeft A).bijective.comp u.mulLeft_bijective
  calc
    (∑ x : ZMod r, chi (A + (u : ZMod r) * x)) =
        ∑ x : ZMod r, chi x := by
      exact Fintype.sum_bijective
        (fun x : ZMod r => A + (u : ZMod r) * x) hbij _ _ (fun _ => rfl)
    _ = 0 := MulChar.sum_eq_zero_of_ne_one hne

/-- The Moebius-weighted first marginal cancels exactly over one complete
affine target period. -/
theorem affine_first_marginal_sum_eq_zero
    (r : ℕ) [NeZero r]
    (chi : DirichletCharacter ℂ r) (hne : chi ≠ 1)
    (A : ZMod r) (u : (ZMod r)ˣ) :
    ∑ x : ZMod r,
        ((ArithmeticFunction.moebius r : ℤ) : ℂ) *
          chi (A + (u : ZMod r) * x) = 0 := by
  rw [← Finset.mul_sum, affine_character_sum_eq_zero r chi hne A u, mul_zero]

/-- Consecutive even targets form a complete residue system modulo `r` when
`2` is coprime to `r`. -/
theorem even_target_first_marginal_complete_period_eq_zero
    (r : ℕ) [NeZero r]
    (chi : DirichletCharacter ℂ r) (hne : chi ≠ 1)
    (A : ℕ) (h2 : Nat.Coprime 2 r) :
    ∑ i ∈ Finset.range r,
        ((ArithmeticFunction.moebius r : ℤ) : ℂ) *
          chi ((A + 2 * i : ℕ) : ZMod r) = 0 := by
  simp only [Nat.cast_add, Nat.cast_mul]
  let u : (ZMod r)ˣ := ZMod.unitOfCoprime 2 h2
  have hsum := affine_first_marginal_sum_eq_zero
    r chi hne (A : ZMod r) u
  calc
    (∑ i ∈ Finset.range r,
        ((ArithmeticFunction.moebius r : ℤ) : ℂ) *
          chi ((A : ZMod r) + ((2 : ℕ) : ZMod r) * (i : ZMod r))) =
        ∑ x : ZMod r,
          ((ArithmeticFunction.moebius r : ℤ) : ℂ) *
            chi ((A : ZMod r) + ((2 : ℕ) : ZMod r) * x) :=
      by
        convert sum_range_residues_complex r
          (fun x : ZMod r =>
            ((ArithmeticFunction.moebius r : ℤ) : ℂ) *
              chi ((A : ZMod r) + ((2 : ℕ) : ZMod r) * x)) using 1
    _ = 0 := by simpa only [u, ZMod.coe_unitOfCoprime] using hsum

/-- Every incomplete affine first-marginal prefix has norm at most the
conductor.  Complete periods cancel; only the final remainder survives. -/
theorem affine_first_marginal_prefix_norm_le
    (r : ℕ) [NeZero r]
    (chi : DirichletCharacter ℂ r) (hne : chi ≠ 1)
    (A : ZMod r) (u : (ZMod r)ˣ) (T : ℕ) :
    ‖∑ i ∈ Finset.range T,
        ((ArithmeticFunction.moebius r : ℤ) : ℂ) *
          chi (A + (u : ZMod r) * (i : ZMod r))‖ ≤ (r : ℝ) := by
  let g : ZMod r → ℂ := fun x =>
    ((ArithmeticFunction.moebius r : ℤ) : ℂ) *
      chi (A + (u : ZMod r) * x)
  have hfull : (∑ x : ZMod r, g x) = 0 := by
    simpa only [g] using affine_first_marginal_sum_eq_zero r chi hne A u
  have hdecomp := residue_interval_decomposition g 0 T
  have hrem :
      (∑ i ∈ Finset.range T, g (i : ZMod r)) =
        ∑ i ∈ Finset.range (T % r), g (i : ZMod r) := by
    simpa [hfull] using hdecomp
  rw [show (∑ i ∈ Finset.range T,
      ((ArithmeticFunction.moebius r : ℤ) : ℂ) *
        chi (A + (u : ZMod r) * (i : ZMod r))) =
      ∑ i ∈ Finset.range T, g (i : ZMod r) by rfl, hrem]
  calc
    ‖∑ i ∈ Finset.range (T % r), g (i : ZMod r)‖ ≤
        ∑ i ∈ Finset.range (T % r), ‖g (i : ZMod r)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _i ∈ Finset.range (T % r), (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro i _hi
      unfold g
      have hmu :
          ‖((ArithmeticFunction.moebius r : ℤ) : ℂ)‖ ≤ 1 := by
        rw [Complex.norm_intCast]
        exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := r))
      rw [norm_mul]
      exact (mul_le_mul hmu (chi.norm_le_one _) (norm_nonneg _) zero_le_one).trans_eq
        (one_mul 1)
    _ = (T % r : ℕ) := by simp
    _ ≤ (r : ℝ) := by
      exact_mod_cast Nat.le_of_lt
        (Nat.mod_lt T (Nat.pos_of_ne_zero (NeZero.ne r)))

/-- Abel transport of the exact complete-period cancellation.  The weighted
first marginal is controlled by the conductor and the total variation of the
target weights, with no common LCM. -/
theorem weighted_affine_first_marginal_norm_le
    (r : ℕ) [NeZero r]
    (chi : DirichletCharacter ℂ r) (hne : chi ≠ 1)
    (A : ZMod r) (u : (ZMod r)ˣ)
    (w : ℕ → ℝ) (T : ℕ) (V : ℝ)
    (hT : 1 ≤ T)
    (hlast : |w (T - 1)| ≤ 1)
    (hvariation :
      ∑ i ∈ Finset.range (T - 1), |w (i + 1) - w i| ≤ V) :
    ‖∑ i ∈ Finset.range T,
        w i • (((ArithmeticFunction.moebius r : ℤ) : ℂ) *
          chi (A + (u : ZMod r) * (i : ZMod r)))‖ ≤
      (r : ℝ) * (1 + V) := by
  apply weighted_complex_sum_norm_le_of_prefix_bound
    (fun i => ((ArithmeticFunction.moebius r : ℤ) : ℂ) *
      chi (A + (u : ZMod r) * (i : ZMod r)))
    w T (r : ℝ) V (Nat.cast_nonneg r) hT
  · intro k _hk
    exact affine_first_marginal_prefix_norm_le r chi hne A u k
  · exact hlast
  · exact hvariation

/-- Complete target averaging does not cancel a target-independent second
marginal.  In the constant-weight normal form the first marginal vanishes,
but the second survives exactly with linear factor `r`. -/
theorem complete_target_average_leaves_second_marginal
    (r : ℕ) [NeZero r]
    (chi : DirichletCharacter ℂ r) (hne : chi ≠ 1)
    (A : ZMod r) (u : (ZMod r)ˣ) (c : ℂ) :
    (∑ x : ZMod r,
      (((ArithmeticFunction.moebius r : ℤ) : ℂ) *
          chi (A + (u : ZMod r) * x) - c)) = -(r : ℂ) * c := by
  rw [Finset.sum_sub_distrib, affine_first_marginal_sum_eq_zero r chi hne A u]
  simp

end GoldbachCircleMethodEvenTargetWeightedCharacterAverageV18366
