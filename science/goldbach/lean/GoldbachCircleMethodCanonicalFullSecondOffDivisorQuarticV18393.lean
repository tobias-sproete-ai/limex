import GoldbachCircleMethodCoupledSecondLowFrequencyClassificationV18392
import GoldbachCircleMethodCanonicalFullFirstMarginalQuarticV18382

/-!
# Goldbach V1.8.393: full normalized off-divisor second-marginal Q^4 bound

The active-level factor `r/phi(r)^2` and the character value at `-1` are
restored.  The exact coupled-carrier relation `card(L_r) * r <= Q` absorbs the
active conductor, so the complete off-divisor second marginal remains quartic:

`2 * B * (3 + 4*b) * Q^4 * M^2`.

This theorem does not bound or sign the three low product channels
`(1,1)`, `(1,2)`, `(2,1)` and does not prove reserve absorption or Goldbach.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodCanonicalFullSecondOffDivisorQuarticV18393

open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodCanonicalCoupledFirstMarginalAggregationV18378
open GoldbachCircleMethodCanonicalCoupledSecondMarginalAbelV18388
open GoldbachCircleMethodCanonicalCoupledSecondMarginalAggregationV18390
open GoldbachCircleMethodCanonicalCoupledSecondMarginalSourceBindingV18391
open GoldbachCircleMethodCanonicalCoupledSecondMarginalTwoBranchV18389
open GoldbachCircleMethodPairwiseActiveCostAggregationV18318

/-- Literal off-divisor second-marginal contribution including the remaining
active-level normalization and the character value at `-1`. -/
noncomputable def normalizedOffDivisorCoupledSecondMarginal {Q : ℕ}
    (r : PositiveLevel Q) (chi : DirichletCharacter ℂ r.val)
    (v w : ℕ → ℂ) (B A T : ℕ) (b : ℝ) : ℂ :=
  ((r.val : ℂ) / ((r.val.totient : ℂ) ^ 2)) * chi (-1) *
    sourceCoupledSecondMarginalTargetSum r v w B A T b

/-- The off-divisor carrier count cancels one active-conductor factor. -/
theorem off_divisor_card_mul_conductor_le {Q : ℕ}
    (r : PositiveLevel Q) :
    ((offDivisorSecondCarrier r).card : ℝ) * (r.val : ℝ) ≤ (Q : ℝ) := by
  have hsubset : offDivisorSecondCarrier r ⊆
      Finset.univ.filter (fun l : PositiveLevel Q => r.val * l.val ≤ Q) := by
    intro l hl
    have hactive := (Finset.mem_filter.mp hl).1
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (Finset.mem_filter.mp hactive).2.1⟩
  have hcard : (offDivisorSecondCarrier r).card ≤ Q / r.val :=
    (Finset.card_le_card hsubset).trans
      (GoldbachCircleMethodExceptionalWeightBoundaryV18128.companion_level_count_le Q r)
  have hmul : (Q / r.val) * r.val ≤ Q := Nat.div_mul_le_self Q r.val
  exact_mod_cast (Nat.mul_le_mul_right r.val hcard |>.trans hmul)

/-- The active normalization alone has norm at most its conductor. -/
theorem active_square_prefactor_norm_le_conductor {Q : ℕ}
    (r : PositiveLevel Q) :
    ‖(r.val : ℂ) / ((r.val.totient : ℂ) ^ 2)‖ ≤ (r.val : ℝ) := by
  have hrpos : 0 < r.val := Nat.pos_of_ne_zero (NeZero.ne r.val)
  have hphi : (1 : ℝ) ≤ r.val.totient := by
    exact_mod_cast Nat.totient_pos.mpr hrpos
  have hphi_sq : (1 : ℝ) ≤ (r.val.totient : ℝ) ^ 2 := by
    nlinarith [sq_nonneg ((r.val.totient : ℝ) - 1)]
  rw [norm_div, norm_pow, Complex.norm_natCast]
  simpa only [Complex.norm_natCast] using
    div_le_self (Nat.cast_nonneg r.val) hphi_sq

/-- Before the final active prefactor, the source aggregate is bounded by its
exact carrier cardinality times the cubic per-companion cutoff budget. -/
theorem source_off_divisor_norm_le_card_mul_cubic {Q : ℕ}
    (r : PositiveLevel Q)
    (v w : ℕ → ℂ) (M : ℝ) (hM : 0 ≤ M)
    (hv : ∀ n, ‖v n‖ ≤ M) (hw : ∀ n, ‖w n‖ ≤ M)
    (B A K S : ℕ) (b : ℝ) (hb : 0 ≤ b)
    (hB : 2 ≤ B) (hBA : B ≤ A)
    (hNonempty : 2 * (B / 2 + 1) ≤ A)
    (hK : 1 ≤ K)
    (hGrowingLast : A + 2 * (K - 1) ≤
      GoldbachCircleMethodCanonicalTargetWeightPiecewiseGeometryV18368.blockPairTurningTarget B)
    (hS : 1 ≤ S)
    (hShrinkingFirst :
      GoldbachCircleMethodCanonicalTargetWeightPiecewiseGeometryV18368.blockPairTurningTarget B ≤
        A + 2 * K)
    (hFinal : A + 2 * K + 2 * (S - 1) ≤ 2 * B) :
    ‖sourceCoupledSecondMarginalTargetSum r v w B A (K + S) b‖ ≤
      ((offDivisorSecondCarrier r).card : ℝ) *
        (2 * (B : ℝ) * (3 + 4 * b) * (Q : ℝ) ^ 3 * M ^ 2) := by
  rw [← canonicalCoupledSecondMarginalAggregate_eq_source]
  let C : ℝ := 2 * (B : ℝ) * (3 + 4 * b) * (Q : ℝ) ^ 3 * M ^ 2
  have hterm : ∀ l ∈ offDivisorSecondCarrier r,
      ‖coupledFirstMarginalCoefficient r l v w *
        canonicalCoupledSecondMarginalTargetSum
          r.val l.val B A (K + S) b‖ ≤ C := by
    intro l hl
    have hoff := Finset.mem_filter.mp hl
    have hactive := hoff.1
    have hprod : 2 < r.val * l.val := hoff.2
    have hdata := (Finset.mem_filter.mp hactive).2
    have hrl_nat : r.val * l.val ≤ Q := hdata.1
    have hcop : Nat.Coprime r.val l.val := hdata.2
    have hrQ : r.val ≤ Q := (Finset.mem_Icc.mp r.property).2
    have hlQ : l.val ≤ Q := (Finset.mem_Icc.mp l.property).2
    have hphir_nat : r.val.totient ≤ Q := (Nat.totient_le r.val).trans hrQ
    have hphil_nat : l.val.totient ≤ Q := (Nat.totient_le l.val).trans hlQ
    have hrl : ((r.val * l.val : ℕ) : ℝ) ≤ (Q : ℝ) := by
      exact_mod_cast hrl_nat
    have hphir : (r.val.totient : ℝ) ≤ (Q : ℝ) := by
      exact_mod_cast hphir_nat
    have hphil : (l.val.totient : ℝ) ≤ (Q : ℝ) := by
      exact_mod_cast hphil_nat
    have htarget := canonical_coupled_second_marginal_two_branch_norm_le
      r.val l.val hcop hprod B A K S b hb hB hBA hNonempty hK
        hGrowingLast hS hShrinkingFirst hFinal
    have htargetQ :
        ‖canonicalCoupledSecondMarginalTargetSum
          r.val l.val B A (K + S) b‖ ≤
          2 * (B : ℝ) * (3 + 4 * b) * (Q : ℝ) ^ 3 := by
      calc
        _ ≤ (((r.val * l.val : ℕ) : ℝ) *
              ((r.val.totient : ℝ) * (l.val.totient : ℝ))) *
                (2 * ((B : ℝ) * (3 + 4 * b))) := htarget
        _ ≤ ((Q : ℝ) * ((Q : ℝ) * (Q : ℝ))) *
              (2 * ((B : ℝ) * (3 + 4 * b))) := by
          apply mul_le_mul
          · exact mul_le_mul hrl (mul_le_mul hphir hphil (by positivity) (by positivity))
              (by positivity) (by positivity)
          · rfl
          · positivity
          · positivity
        _ = 2 * (B : ℝ) * (3 + 4 * b) * (Q : ℝ) ^ 3 := by ring
    rw [norm_mul]
    calc
      _ ≤ M ^ 2 *
          (2 * (B : ℝ) * (3 + 4 * b) * (Q : ℝ) ^ 3) :=
        mul_le_mul
          (coupledFirstMarginalCoefficient_norm_le r l v w M hM hv hw)
          htargetQ (norm_nonneg _) (by positivity)
      _ = C := by
        dsimp [C]
        ring
  unfold canonicalCoupledSecondMarginalAggregate
  calc
    _ ≤ ∑ l ∈ offDivisorSecondCarrier r,
        ‖coupledFirstMarginalCoefficient r l v w *
          canonicalCoupledSecondMarginalTargetSum
            r.val l.val B A (K + S) b‖ := norm_sum_le _ _
    _ ≤ ∑ _l ∈ offDivisorSecondCarrier r, C :=
      Finset.sum_le_sum (fun l hl => hterm l hl)
    _ = ((offDivisorSecondCarrier r).card : ℝ) * C := by simp

/-- End-to-end normalized off-divisor `Q^4` estimate. -/
theorem normalized_off_divisor_coupled_second_marginal_norm_le_quartic {Q : ℕ}
    (r : PositiveLevel Q) (chi : DirichletCharacter ℂ r.val)
    (v w : ℕ → ℂ) (M : ℝ) (hM : 0 ≤ M)
    (hv : ∀ n, ‖v n‖ ≤ M) (hw : ∀ n, ‖w n‖ ≤ M)
    (B A K S : ℕ) (b : ℝ) (hb : 0 ≤ b)
    (hB : 2 ≤ B) (hBA : B ≤ A)
    (hNonempty : 2 * (B / 2 + 1) ≤ A)
    (hK : 1 ≤ K)
    (hGrowingLast : A + 2 * (K - 1) ≤
      GoldbachCircleMethodCanonicalTargetWeightPiecewiseGeometryV18368.blockPairTurningTarget B)
    (hS : 1 ≤ S)
    (hShrinkingFirst :
      GoldbachCircleMethodCanonicalTargetWeightPiecewiseGeometryV18368.blockPairTurningTarget B ≤
        A + 2 * K)
    (hFinal : A + 2 * K + 2 * (S - 1) ≤ 2 * B) :
    ‖normalizedOffDivisorCoupledSecondMarginal
        r chi v w B A (K + S) b‖ ≤
      2 * (B : ℝ) * (3 + 4 * b) * (Q : ℝ) ^ 4 * M ^ 2 := by
  have hsource := source_off_divisor_norm_le_card_mul_cubic
    r v w M hM hv hw B A K S b hb hB hBA hNonempty hK
      hGrowingLast hS hShrinkingFirst hFinal
  have hchi : ‖chi (-1)‖ ≤ 1 := chi.norm_le_one (-1)
  unfold normalizedOffDivisorCoupledSecondMarginal
  rw [norm_mul, norm_mul]
  calc
    _ ≤ (r.val : ℝ) * 1 *
        (((offDivisorSecondCarrier r).card : ℝ) *
          (2 * (B : ℝ) * (3 + 4 * b) * (Q : ℝ) ^ 3 * M ^ 2)) := by
      exact mul_le_mul
        (mul_le_mul (active_square_prefactor_norm_le_conductor r) hchi
          (norm_nonneg _) (by positivity))
        hsource (norm_nonneg _) (by positivity)
    _ = (((offDivisorSecondCarrier r).card : ℝ) * (r.val : ℝ)) *
        (2 * (B : ℝ) * (3 + 4 * b) * (Q : ℝ) ^ 3 * M ^ 2) := by ring
    _ ≤ (Q : ℝ) *
        (2 * (B : ℝ) * (3 + 4 * b) * (Q : ℝ) ^ 3 * M ^ 2) :=
      mul_le_mul_of_nonneg_right (off_divisor_card_mul_conductor_le r)
        (by positivity)
    _ = 2 * (B : ℝ) * (3 + 4 * b) * (Q : ℝ) ^ 4 * M ^ 2 := by ring

end GoldbachCircleMethodCanonicalFullSecondOffDivisorQuarticV18393
