import GoldbachCircleMethodAdmittedSourceVariableCorrectionBudgetV18397
import GoldbachCircleMethodActualLogWeightSquareBindingV18219

/-!
# Goldbach V1.8.398: real source-correction binding

V1.8.396--397 bound a complex two-marginal correction by a pairwise-period
`Q^4` budget.  The actual scalar source identity in V1.8.340 contains the
product of the real coupled diagonal and the real correction.  This module
closes that adequacy seam for the canonical real logarithmic weights: the
coupled diagonal has zero imaginary part, so the real part of the complex
correction is exactly the scalar correction occurring in the source model.

No principal reserve, source positivity, exceptional-set estimate, or
Goldbach conclusion is asserted.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodSourceRealCorrectionBindingV18398

open GoldbachCircleMethodActualCoupledDiagonalRealReadbackV18218
open GoldbachCircleMethodActualFrozenModelCompleteDiagonalV18213
open GoldbachCircleMethodActualLogWeightSquareBindingV18219
open GoldbachCircleMethodAdmittedSourceVariableCorrectionBudgetV18397
open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodCanonicalBumpPrincipalFloorV18220
open GoldbachCircleMethodCompanionSquarefreeGcdBindingV18139
open GoldbachCircleMethodFiniteResiduePrefixV1866
open GoldbachCircleMethodLogCutoffPresieveBindingV18120
open GoldbachCircleMethodSourceBoundVariableCoupledCorrectionV18396
open GoldbachCircleMethodStructurallyAdmissibleActiveSlotV18258
open GoldbachCircleMethodVariableMeanCombinedReserveV18340
open GoldbachCircleMethodVariableUnitPairExactCorrectionV18344

theorem neg_triple_re_of_first_second_real
    (a x y : ℂ) (ha : a.im = 0) (hx : x.im = 0) :
    (-(a * x * y)).re = -(a.re * x.re * y.re) := by
  rw [Complex.neg_re, Complex.mul_re, Complex.mul_re, Complex.mul_im, ha, hx]
  ring

/-- For real denominator weights, every surviving summand of the coupled
diagonal is real.  The proof uses the exact squarefree gcd formula rather
than a conjugation heuristic. -/
theorem coupledDiagonal_realWeight_im_zero
    {Q K : ℕ} [NeZero K]
    (hK : ∀ q : PositiveLevel Q, q.val ∣ K)
    (r : PositiveLevel Q) (N : ℕ) (w : ℕ → ℝ) :
    (coupledDiagonal hK r (fun q => (w q : ℂ)) (fun _ => 1)
      (N : ZMod K)).im = 0 := by
  unfold coupledDiagonal
  change Complex.imCLM
      (∑ l : PositiveLevel Q,
        if r.val * l.val ≤ Q ∧ Nat.Coprime r.val l.val then
          (((ArithmeticFunction.moebius l.val : ℤ) : ℂ) ^ 2) /
              (l.val.totient : ℂ) ^ 2 *
            unitCharacterSum l.val
              (ZMod.castHom (hK l) (ZMod l.val) (N : ZMod K)) *
            (w (r.val * l.val) : ℂ) * 1
        else 0) = 0
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro l _hl
  by_cases hcut : r.val * l.val ≤ Q ∧ Nat.Coprime r.val l.val
  · rw [if_pos hcut, castHom_natCast]
    by_cases hsq : Squarefree l.val
    · have hphi : ((l.val.totient : ℕ) : ℂ) ≠ 0 := by
        exact_mod_cast (Nat.totient_pos.mpr
          (Nat.pos_of_ne_zero (NeZero.ne l.val))).ne'
      have hrel := moebius_character_quotient_gcd l.val N hsq
      have hrewrite :
          (((ArithmeticFunction.moebius l.val : ℤ) : ℂ) ^ 2) /
                (l.val.totient : ℂ) ^ 2 *
              unitCharacterSum l.val (N : ZMod l.val) =
            (((ArithmeticFunction.moebius l.val : ℤ) : ℂ) /
                (l.val.totient : ℂ)) *
              ((((ArithmeticFunction.moebius (Nat.gcd l.val N) : ℤ) : ℂ) /
                ((l.val / Nat.gcd l.val N).totient : ℂ))) := by
        rw [← hrel]
        field_simp
      rw [hrewrite]
      have hreality :
          (((ArithmeticFunction.moebius l.val : ℤ) : ℂ) /
                (l.val.totient : ℂ)) *
              ((((ArithmeticFunction.moebius (Nat.gcd l.val N) : ℤ) : ℂ) /
                ((l.val / Nat.gcd l.val N).totient : ℂ))) *
              (w (r.val * l.val) : ℂ) =
            ((((ArithmeticFunction.moebius l.val : ℤ) : ℝ) /
                (l.val.totient : ℝ) *
              (((ArithmeticFunction.moebius (Nat.gcd l.val N) : ℤ) : ℝ) /
                ((l.val / Nat.gcd l.val N).totient : ℝ)) *
              w (r.val * l.val) : ℝ) : ℂ) := by
        norm_cast
      rw [mul_one, hreality]
      rfl
    · rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq]
      simp
  · simp [hcut]

/-- Canonical two-log-weight coupled diagonals are real as complex numbers. -/
theorem coupledDiagonal_canonicalLogWeight_im_zero
    {Q K : ℕ} [NeZero K]
    (hK : ∀ q : PositiveLevel Q, q.val ∣ K)
    (r : PositiveLevel Q) (N : ℕ) (R : ℝ) :
    (coupledDiagonal hK r
      (logWeight R canonicalLogBump)
      (logWeight R canonicalLogBump) (N : ZMod K)).im = 0 := by
  rw [coupledDiagonal_logWeight_square_eq hK r N R canonicalLogBump]
  exact coupledDiagonal_realWeight_im_zero hK r N
    (squaredLogWeightReal R canonicalLogBump)

/-- The actual scalar correction appearing in V1.8.340, summed over a target
block.  This definition keeps the product of real parts exactly as it occurs
in the source identity. -/
noncomputable def sourceRealActualVariableCorrectionTargetSum
    {Q K : ℕ} [NeZero K]
    (hK : ∀ q : PositiveLevel Q, q.val ∣ K)
    (e : StructurallyAdmissibleActiveSlot Q)
    (v w : ℕ → ℂ) (B A T : ℕ) (b : ℝ) : ℝ :=
  ∑ i ∈ Finset.range T,
    -(((e.val.1.val : ℝ) / (e.val.1.val.totient : ℝ) ^ 2) *
      (coupledDiagonal hK e.val.1 v w
        ((A + 2 * i : ℕ) : ZMod K)).re *
      (variableUnitPairCorrectionSum e.val.1.val (A + 2 * i)
        (GoldbachCircleMethodBlockPairCarrierV18227.blockPairLower B (A + 2 * i))
        (GoldbachCircleMethodBlockPairCarrierV18227.blockPairUpper B (A + 2 * i) -
          GoldbachCircleMethodBlockPairCarrierV18227.blockPairLower B (A + 2 * i) + 1)
        e.val.2.val b).re)

/-- For canonical real log weights, the complex marginal correction of
V1.8.396 has exactly the real source meaning required by V1.8.340. -/
theorem sourceNormalizedActualVariableCorrectionTargetSum_re_eq_sourceReal
    {Q K : ℕ} [NeZero K]
    (hK : ∀ q : PositiveLevel Q, q.val ∣ K)
    (e : StructurallyAdmissibleActiveSlot Q)
    (R : ℝ) (B A T : ℕ) (b : ℝ) :
    (sourceNormalizedActualVariableCorrectionTargetSum hK e
      (logWeight R canonicalLogBump)
      (logWeight R canonicalLogBump) B A T b).re =
      sourceRealActualVariableCorrectionTargetSum hK e
        (logWeight R canonicalLogBump)
        (logWeight R canonicalLogBump) B A T b := by
  unfold sourceNormalizedActualVariableCorrectionTargetSum
    sourceRealActualVariableCorrectionTargetSum
  change Complex.reCLM
      (∑ i ∈ Finset.range T,
        -(((e.val.1.val : ℂ) / ((e.val.1.val.totient : ℂ) ^ 2)) *
          coupledDiagonal hK e.val.1
            (logWeight R canonicalLogBump)
            (logWeight R canonicalLogBump)
            ((A + 2 * i : ℕ) : ZMod K) *
          variableUnitPairCorrectionSum e.val.1.val (A + 2 * i)
            (GoldbachCircleMethodBlockPairCarrierV18227.blockPairLower B (A + 2 * i))
            (GoldbachCircleMethodBlockPairCarrierV18227.blockPairUpper B (A + 2 * i) -
              GoldbachCircleMethodBlockPairCarrierV18227.blockPairLower B (A + 2 * i) + 1)
            e.val.2.val b)) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  have him := coupledDiagonal_canonicalLogWeight_im_zero hK e.val.1
    (A + 2 * i) R
  let a : ℂ := (e.val.1.val : ℂ) / ((e.val.1.val.totient : ℂ) ^ 2)
  let x : ℂ := coupledDiagonal hK e.val.1
    (logWeight R canonicalLogBump)
    (logWeight R canonicalLogBump) ((A + 2 * i : ℕ) : ZMod K)
  let y : ℂ := variableUnitPairCorrectionSum e.val.1.val (A + 2 * i)
    (GoldbachCircleMethodBlockPairCarrierV18227.blockPairLower B (A + 2 * i))
    (GoldbachCircleMethodBlockPairCarrierV18227.blockPairUpper B (A + 2 * i) -
      GoldbachCircleMethodBlockPairCarrierV18227.blockPairLower B (A + 2 * i) + 1)
    e.val.2.val b
  have hscalar : a =
      ((((e.val.1.val : ℕ) : ℝ) /
        (((e.val.1.val.totient : ℕ) : ℝ) ^ 2) : ℝ) : ℂ) := by
    dsimp only [a]
    push_cast
    rfl
  have ha : a.im = 0 := by
    rw [hscalar]
    rfl
  have hx : x.im = 0 := by simpa only [x] using him
  have hare : a.re =
      ((e.val.1.val : ℝ) / (e.val.1.val.totient : ℝ) ^ 2) := by
    rw [hscalar]
    rfl
  change (-(a * x * y)).re =
    -(((e.val.1.val : ℝ) / (e.val.1.val.totient : ℝ) ^ 2) *
      x.re * y.re)
  rw [neg_triple_re_of_first_second_real a x y ha hx, hare]

end GoldbachCircleMethodSourceRealCorrectionBindingV18398
