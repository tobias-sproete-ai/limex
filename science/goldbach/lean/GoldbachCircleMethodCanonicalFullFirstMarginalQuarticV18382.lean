import GoldbachCircleMethodCanonicalCoupledFirstMarginalActualBindingV18381
import GoldbachCircleMethodCanonicalCoupledFirstMarginalParityCompleteV18379

/-!
# Goldbach V1.8.382: full normalized first-marginal Q^4 bound

The remaining active-conductor prefactor `r / phi(r)^2` from the exact frozen
model is restored.  Its norm is at most `Q`.  Combined with the source-bound
cubic companion aggregation, this yields the complete first coupled marginal
budget `8 * B * Q^4 * M^2`, with the even-conductor branch identically zero.

This closes the first marginal only.  The second marginal and reserve
absorption remain open.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodCanonicalFullFirstMarginalQuarticV18382

open GoldbachCircleMethodActualFrozenModelCompleteDiagonalV18213
open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodCanonicalCoupledFirstMarginalActualBindingV18381
open GoldbachCircleMethodCanonicalCoupledFirstMarginalAggregationV18378
open GoldbachCircleMethodCanonicalCoupledFirstMarginalParityCompleteV18379

/-- The literal first-marginal contribution including the active-conductor
normalization from the exact V1.8.213 frozen-model diagonal. -/
noncomputable def normalizedActualCoupledFirstMarginal
    {Q K : ℕ} [NeZero K]
    (hK : ∀ q : PositiveLevel Q, q.val ∣ K)
    (r : PositiveLevel Q) (chi : DirichletCharacter ℂ r.val)
    (v w : ℕ → ℂ) (B A T : ℕ) (b : ℝ) : ℂ :=
  ((r.val : ℂ) / ((r.val.totient : ℂ) ^ 2)) *
    actualCoupledFirstMarginalTargetSum hK r chi v w B A T b

/-- The restored active-conductor normalization costs at most one cutoff
power. -/
theorem active_conductor_square_prefactor_norm_le_cutoff {Q : ℕ}
    (r : PositiveLevel Q) :
    ‖(r.val : ℂ) / ((r.val.totient : ℂ) ^ 2)‖ ≤ (Q : ℝ) := by
  have hrpos : 0 < r.val := Nat.pos_of_ne_zero (NeZero.ne r.val)
  have hphi : (1 : ℝ) ≤ r.val.totient := by
    exact_mod_cast Nat.totient_pos.mpr hrpos
  have hphi_sq : (1 : ℝ) ≤ (r.val.totient : ℝ) ^ 2 := by
    nlinarith [sq_nonneg ((r.val.totient : ℝ) - 1)]
  have hrQ : (r.val : ℝ) ≤ (Q : ℝ) := by
    exact_mod_cast (Finset.mem_Icc.mp r.property).2
  rw [norm_div, norm_pow, Complex.norm_natCast]
  simpa only [Complex.norm_natCast] using
    (div_le_self (Nat.cast_nonneg r.val) hphi_sq).trans hrQ

/-- End-to-end parity-complete `Q^4` estimate for the literal normalized first
coupled marginal of the original finite frozen model. -/
theorem normalized_actual_coupled_first_marginal_parity_complete {Q K : ℕ}
    [NeZero K]
    (hKperiod : ∀ q : PositiveLevel Q, q.val ∣ K)
    (r : PositiveLevel Q)
    (chi : DirichletCharacter ℂ r.val) (hne : chi ≠ 1)
    (v w : ℕ → ℂ) (M : ℝ) (hM : 0 ≤ M)
    (hv : ∀ n, ‖v n‖ ≤ M) (hw : ∀ n, ‖w n‖ ≤ M)
    (B A Kgrow S : ℕ) (b : ℝ) (hb : 0 ≤ b) (hA : Even A)
    (hB : 1 ≤ B) (hBA : B ≤ A)
    (hNonempty : 2 * (B / 2 + 1) ≤ A)
    (hKgrow : 1 ≤ Kgrow)
    (hGrowingLast : A + 2 * (Kgrow - 1) ≤
      GoldbachCircleMethodCanonicalTargetWeightPiecewiseGeometryV18368.blockPairTurningTarget B)
    (hS : 1 ≤ S)
    (hShrinkingFirst :
      GoldbachCircleMethodCanonicalTargetWeightPiecewiseGeometryV18368.blockPairTurningTarget B ≤
        A + 2 * Kgrow)
    (hFinal : A + 2 * Kgrow + 2 * (S - 1) ≤ 2 * B) :
    normalizedActualCoupledFirstMarginal
        hKperiod r chi v w B A (Kgrow + S) b = 0 ∨
      ‖normalizedActualCoupledFirstMarginal
        hKperiod r chi v w B A (Kgrow + S) b‖ ≤
          8 * (B : ℝ) * (Q : ℝ) ^ 4 * M ^ 2 := by
  have hpar := canonical_coupled_first_marginal_aggregate_parity_complete
    r chi hne v w M hM hv hw B A Kgrow S b hb hA hB hBA hNonempty
      hKgrow hGrowingLast hS hShrinkingFirst hFinal
  have hbind := canonicalCoupledFirstMarginalAggregate_eq_actual
    hKperiod r chi v w B A (Kgrow + S) b
  rcases hpar with hzero | hbound
  · left
    unfold normalizedActualCoupledFirstMarginal
    rw [← hbind, hzero, mul_zero]
  · right
    have hactual :
        ‖actualCoupledFirstMarginalTargetSum
          hKperiod r chi v w B A (Kgrow + S) b‖ ≤
            8 * (B : ℝ) * (Q : ℝ) ^ 3 * M ^ 2 := by
      rw [← hbind]
      exact hbound
    unfold normalizedActualCoupledFirstMarginal
    rw [norm_mul]
    calc
      _ ≤ (Q : ℝ) * (8 * (B : ℝ) * (Q : ℝ) ^ 3 * M ^ 2) :=
        mul_le_mul (active_conductor_square_prefactor_norm_le_cutoff r)
          hactual (norm_nonneg _) (by positivity)
      _ = 8 * (B : ℝ) * (Q : ℝ) ^ 4 * M ^ 2 := by ring

end GoldbachCircleMethodCanonicalFullFirstMarginalQuarticV18382
