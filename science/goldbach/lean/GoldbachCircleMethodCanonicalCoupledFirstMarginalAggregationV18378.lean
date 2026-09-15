import GoldbachCircleMethodCanonicalCoupledFirstMarginalTwoBranchV18377
import GoldbachCircleMethodPairwiseActiveCostAggregationV18318

/-!
# Goldbach V1.8.378: source-normalized companion aggregation

The one-companion pairwise-period estimate from V1.8.377 is now multiplied by
the exact coefficient occurring in `coupledDiagonal` and summed over the
actual coupled carrier `r*l <= Q`, `Coprime r l`.

The resulting first-marginal boundary cost is cubic in `Q`, hence in
particular quartic, and no common LCM is introduced.  This controls only the
first coupled marginal.  It does not control the second marginal, establish a
reserve sign, or prove Goldbach.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodCanonicalCoupledFirstMarginalAggregationV18378

open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodCanonicalCoupledFirstMarginalAbelV18376
open GoldbachCircleMethodCanonicalCoupledFirstMarginalTwoBranchV18377
open GoldbachCircleMethodPairwiseActiveCostAggregationV18318
open GoldbachCircleMethodRemovedConvolutionNormV18123

/-- The exact companion coefficient from the finite coupled diagonal. -/
noncomputable def coupledFirstMarginalCoefficient {Q : ℕ}
    (r l : PositiveLevel Q) (v w : ℕ → ℂ) : ℂ :=
  (((ArithmeticFunction.moebius l.val : ℤ) : ℂ) ^ 2) /
      ((l.val.totient : ℂ) ^ 2) *
    v (r.val * l.val) * w (r.val * l.val)

/-- Source-normalized sum of all one-companion first-marginal target sums. -/
noncomputable def canonicalCoupledFirstMarginalAggregate {Q : ℕ}
    (r : PositiveLevel Q) (chi : DirichletCharacter ℂ r.val)
    (v w : ℕ → ℂ) (B A T : ℕ) (b : ℝ) : ℂ :=
  ∑ l ∈ activeComplementCarrier r,
    coupledFirstMarginalCoefficient r l v w *
      canonicalCoupledFirstMarginalTargetSum r.val l.val chi B A T b

/-- The Möbius/totient-square normalization has norm at most one. -/
theorem moebius_square_totient_square_norm_le_one
    (l : ℕ) [NeZero l] :
    ‖(((ArithmeticFunction.moebius l : ℤ) : ℂ) ^ 2) /
        ((l.totient : ℂ) ^ 2)‖ ≤ 1 := by
  have hmu : ‖((ArithmeticFunction.moebius l : ℤ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_intCast]
    exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := l))
  have hphi : (1 : ℝ) ≤ l.totient := by
    exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne l))
  have hmu_sq : ‖((ArithmeticFunction.moebius l : ℤ) : ℂ)‖ ^ 2 ≤ 1 := by
    simpa only [one_pow] using
      pow_le_pow_left₀ (norm_nonneg _ ) hmu 2
  have hphi_sq : (1 : ℝ) ≤ (l.totient : ℝ) ^ 2 := by
    nlinarith [sq_nonneg ((l.totient : ℝ) - 1)]
  have hphi_sq_pos : 0 < (l.totient : ℝ) ^ 2 := lt_of_lt_of_le zero_lt_one hphi_sq
  rw [norm_div, norm_pow, norm_pow, Complex.norm_natCast]
  exact (div_le_one hphi_sq_pos).mpr (hmu_sq.trans hphi_sq)

/-- The exact source coefficient costs at most the product weight envelope. -/
theorem coupledFirstMarginalCoefficient_norm_le {Q : ℕ}
    (r l : PositiveLevel Q) (v w : ℕ → ℂ) (M : ℝ)
    (hM : 0 ≤ M) (hv : ∀ n, ‖v n‖ ≤ M) (hw : ∀ n, ‖w n‖ ≤ M) :
    ‖coupledFirstMarginalCoefficient r l v w‖ ≤ M ^ 2 := by
  unfold coupledFirstMarginalCoefficient
  rw [norm_mul, norm_mul]
  have hvw : ‖v (r.val * l.val)‖ * ‖w (r.val * l.val)‖ ≤ M * M :=
    mul_le_mul (hv _) (hw _) (norm_nonneg _) hM
  calc
    _ = ‖(((ArithmeticFunction.moebius l.val : ℤ) : ℂ) ^ 2) /
          ((l.val.totient : ℂ) ^ 2)‖ *
        (‖v (r.val * l.val)‖ * ‖w (r.val * l.val)‖) := by ring
    _ ≤ 1 * (M * M) := mul_le_mul
      (moebius_square_totient_square_norm_le_one l.val) hvw
      (by positivity) zero_le_one
    _ = M ^ 2 := by ring

/-- The active complement carrier has at most `Q` elements. -/
theorem activeComplementCarrier_card_le_cutoff {Q : ℕ}
    (r : PositiveLevel Q) :
    (activeComplementCarrier r).card ≤ Q := by
  calc
    (activeComplementCarrier r).card ≤ Fintype.card (PositiveLevel Q) :=
      Finset.card_le_univ _
    _ = Q := positive_level_card Q

/-- After exact source normalization, the complete companion aggregation has
at most cubic cutoff cost.  The stronger cubic statement is retained before
the quartic corollary so that no artificial power is hidden. -/
theorem canonical_coupled_first_marginal_aggregate_norm_le_cubic {Q : ℕ}
    (r : PositiveLevel Q)
    (chi : DirichletCharacter ℂ r.val) (hne : chi ≠ 1)
    (h2 : Nat.Coprime 2 r.val)
    (v w : ℕ → ℂ) (M : ℝ) (hM : 0 ≤ M)
    (hv : ∀ n, ‖v n‖ ≤ M) (hw : ∀ n, ‖w n‖ ≤ M)
    (B A K S : ℕ) (b : ℝ) (hb : 0 ≤ b)
    (hB : 1 ≤ B) (hBA : B ≤ A)
    (hNonempty : 2 * (B / 2 + 1) ≤ A)
    (hK : 1 ≤ K)
    (hGrowingLast : A + 2 * (K - 1) ≤
      GoldbachCircleMethodCanonicalTargetWeightPiecewiseGeometryV18368.blockPairTurningTarget B)
    (hS : 1 ≤ S)
    (hShrinkingFirst :
      GoldbachCircleMethodCanonicalTargetWeightPiecewiseGeometryV18368.blockPairTurningTarget B ≤
        A + 2 * K)
    (hFinal : A + 2 * K + 2 * (S - 1) ≤ 2 * B) :
    ‖canonicalCoupledFirstMarginalAggregate r chi v w B A (K + S) b‖ ≤
      8 * (B : ℝ) * (Q : ℝ) ^ 3 * M ^ 2 := by
  let C : ℝ := 8 * (B : ℝ) * (Q : ℝ) ^ 2 * M ^ 2
  have hC : 0 ≤ C := by positivity
  have hterm : ∀ l ∈ activeComplementCarrier r,
      ‖coupledFirstMarginalCoefficient r l v w *
        canonicalCoupledFirstMarginalTargetSum
          r.val l.val chi B A (K + S) b‖ ≤ C := by
    intro l hl
    have hdata := (Finset.mem_filter.mp hl).2
    have hrl_nat : r.val * l.val ≤ Q := hdata.1
    have hcop : Nat.Coprime r.val l.val := hdata.2
    have hlQ : l.val ≤ Q := (Finset.mem_Icc.mp l.property).2
    have hphi_nat : l.val.totient ≤ Q := (Nat.totient_le l.val).trans hlQ
    have hrl : ((r.val * l.val : ℕ) : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hrl_nat
    have hphi : (l.val.totient : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hphi_nat
    have htarget := canonical_coupled_first_marginal_two_branch_norm_le
      r.val l.val hcop chi hne h2 B A K S b hb hB hBA hNonempty hK
        hGrowingLast hS hShrinkingFirst hFinal
    have htargetQ :
        ‖canonicalCoupledFirstMarginalTargetSum
          r.val l.val chi B A (K + S) b‖ ≤ 8 * (B : ℝ) * (Q : ℝ) ^ 2 := by
      calc
        _ ≤ (((r.val * l.val : ℕ) : ℝ) * (l.val.totient : ℝ)) *
              (8 * B) := htarget
        _ ≤ ((Q : ℝ) * (Q : ℝ)) * (8 * B) := by
          apply mul_le_mul
          · exact mul_le_mul hrl hphi (by positivity) (by positivity)
          · rfl
          · positivity
          · positivity
        _ = 8 * (B : ℝ) * (Q : ℝ) ^ 2 := by ring
    rw [norm_mul]
    calc
      _ ≤ M ^ 2 * (8 * (B : ℝ) * (Q : ℝ) ^ 2) :=
        mul_le_mul (coupledFirstMarginalCoefficient_norm_le r l v w M hM hv hw)
          htargetQ (norm_nonneg _) (by positivity)
      _ = C := by ring
  unfold canonicalCoupledFirstMarginalAggregate
  calc
    _ ≤ ∑ l ∈ activeComplementCarrier r,
        ‖coupledFirstMarginalCoefficient r l v w *
          canonicalCoupledFirstMarginalTargetSum
            r.val l.val chi B A (K + S) b‖ := norm_sum_le _ _
    _ ≤ ∑ _l ∈ activeComplementCarrier r, C :=
      Finset.sum_le_sum (fun l hl => hterm l hl)
    _ = ((activeComplementCarrier r).card : ℝ) * C := by simp
    _ ≤ (Q : ℝ) * C := by
      exact mul_le_mul_of_nonneg_right
        (by exact_mod_cast activeComplementCarrier_card_le_cutoff r) hC
    _ = 8 * (B : ℝ) * (Q : ℝ) ^ 3 * M ^ 2 := by
      dsimp [C]
      ring

/-- The cubic result implies the requested `Q^4` budget for every nonempty
cutoff.  This is a pairwise-period bound, not a global-LCM estimate. -/
theorem canonical_coupled_first_marginal_aggregate_norm_le_quartic {Q : ℕ}
    (hQ : 1 ≤ Q) (r : PositiveLevel Q)
    (chi : DirichletCharacter ℂ r.val) (hne : chi ≠ 1)
    (h2 : Nat.Coprime 2 r.val)
    (v w : ℕ → ℂ) (M : ℝ) (hM : 0 ≤ M)
    (hv : ∀ n, ‖v n‖ ≤ M) (hw : ∀ n, ‖w n‖ ≤ M)
    (B A K S : ℕ) (b : ℝ) (hb : 0 ≤ b)
    (hB : 1 ≤ B) (hBA : B ≤ A)
    (hNonempty : 2 * (B / 2 + 1) ≤ A)
    (hK : 1 ≤ K)
    (hGrowingLast : A + 2 * (K - 1) ≤
      GoldbachCircleMethodCanonicalTargetWeightPiecewiseGeometryV18368.blockPairTurningTarget B)
    (hS : 1 ≤ S)
    (hShrinkingFirst :
      GoldbachCircleMethodCanonicalTargetWeightPiecewiseGeometryV18368.blockPairTurningTarget B ≤
        A + 2 * K)
    (hFinal : A + 2 * K + 2 * (S - 1) ≤ 2 * B) :
    ‖canonicalCoupledFirstMarginalAggregate r chi v w B A (K + S) b‖ ≤
      8 * (B : ℝ) * (Q : ℝ) ^ 4 * M ^ 2 := by
  have hcubic := canonical_coupled_first_marginal_aggregate_norm_le_cubic
    r chi hne h2 v w M hM hv hw B A K S b hb hB hBA hNonempty hK
      hGrowingLast hS hShrinkingFirst hFinal
  have hQreal : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  calc
    _ ≤ 8 * (B : ℝ) * (Q : ℝ) ^ 3 * M ^ 2 := hcubic
    _ ≤ 8 * (B : ℝ) * (Q : ℝ) ^ 4 * M ^ 2 := by
      have hpow : (Q : ℝ) ^ 3 ≤ (Q : ℝ) ^ 4 := by
        calc
          (Q : ℝ) ^ 3 = (Q : ℝ) ^ 3 * 1 := by ring
          _ ≤ (Q : ℝ) ^ 3 * (Q : ℝ) :=
            mul_le_mul_of_nonneg_left hQreal (by positivity)
          _ = (Q : ℝ) ^ 4 := by ring
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hpow (by positivity)) (sq_nonneg M)

end GoldbachCircleMethodCanonicalCoupledFirstMarginalAggregationV18378
