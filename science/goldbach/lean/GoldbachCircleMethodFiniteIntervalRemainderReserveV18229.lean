import GoldbachCircleMethodSupportedModelIntervalDiagonalV18228
import GoldbachCircleMethodCoupledCompanionRemainderBoundV18207
import GoldbachCircleMethodPositivePrincipalDiagonalV18221
import GoldbachCircleMethodCanonicalBumpResidualMomentsV18222

/-!
# Goldbach V1.8.229: finite interval remainder reserve

The exact interval remainder retained by V1.8.228 is given the conservative
V1.8.207 quartic norm bound for the actual canonical conductor-one companion.
Combining it with the positive principal diagonal yields an explicit signed
real-part floor and a conditional strict-positivity criterion.  No claim is
made here that the displayed numerical criterion holds at any scale.
-/

open scoped BigOperators Classical

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace GoldbachCircleMethodFiniteIntervalRemainderReserveV18229

open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodFiniteCompanionBindingV18118
open GoldbachCircleMethodFiniteResiduePrefixV1866
open GoldbachCircleMethodLogCutoffPresieveBindingV18120
open GoldbachCircleMethodPrincipalWindowBoundaryV18121
open GoldbachCircleMethodActualCompanionCompleteDiagonalV18204
open GoldbachCircleMethodActualCompanionIntervalTransferV18205
open GoldbachCircleMethodCoupledCompanionRemainderBoundV18207
open GoldbachCircleMethodActualFrozenModelCompleteDiagonalV18213
open GoldbachCircleMethodCanonicalBumpPrincipalFloorV18220
open GoldbachCircleMethodPositivePrincipalDiagonalV18221
open GoldbachCircleMethodCanonicalBumpResidualMomentsV18222
open GoldbachCircleMethodActualResidualExactDecompositionV18225
open GoldbachCircleMethodBlockPairCarrierV18227
open GoldbachCircleMethodSupportedModelIntervalDiagonalV18228

/-- The fixed canonical logarithmic weight has norm at most one at every
denominator. -/
theorem norm_logWeight_canonical_le_one (R : ℝ) (q : ℕ) :
    ‖logWeight R canonicalLogBump q‖ ≤ 1 := by
  simpa only [logWeight, Complex.norm_real, Real.norm_eq_abs] using
    abs_canonicalLogBump_le_one
      (Real.log (q : ℝ) / Real.log R)

/-- Algebraic bridge from a centered interval estimate to the exact remainder
object of V1.8.205. -/
theorem intervalRemainder_norm_le_of_centered_bound
    {Q K : ℕ} [NeZero K]
    (hK : ∀ q : PositiveLevel Q, q.val ∣ K)
    (r s : PositiveLevel Q) (v w : ℕ → ℂ)
    (N A T : ℕ) (hend : A + T ≤ N + 1) (E : ℝ)
    (hbound :
      ‖(∑ i ∈ Finset.range T,
          finiteCompanion r (N - (A + i)) v * finiteCompanion s (A + i) w) -
        (T : ℂ) * diagonalValue hK r s v w N‖ ≤ E) :
    ‖intervalRemainder hK r s v w N A T‖ ≤ E := by
  have hdecomp := actual_companion_interval_decomposition
    hK r s v w N A T hend
  have hrem :
      intervalRemainder hK r s v w N A T =
        (∑ i ∈ Finset.range T,
          finiteCompanion r (N - (A + i)) v * finiteCompanion s (A + i) w) -
          (T : ℂ) * diagonalValue hK r s v w N := by
    rw [hdecomp]
    ring
  rw [hrem]
  exact hbound

/-- Named definitional bridge for the diagonal expression exposed by
V1.8.207. -/
theorem diagonalValue_eq_literal_sum
    {Q K : ℕ} [NeZero K]
    (hK : ∀ q : PositiveLevel Q, q.val ∣ K)
    (r s : PositiveLevel Q) (v w : ℕ → ℂ) (N : ℕ) :
    diagonalValue hK r s v w N =
      ∑ q : PositiveLevel Q,
        literalCoefficient r q v * literalCoefficient s q w *
          unitCharacterSum q.val (N : ZMod q.val) := by
  unfold diagonalValue
  apply Finset.sum_congr rfl
  intro q _hq
  simp only [map_natCast]

/-- Quartic remainder bound for any conductor-one weight uniformly bounded by
one.  This small interface isolates the V1.8.207 estimate from scale-specific
definitions. -/
theorem principal_intervalRemainder_norm_le_quartic
    {Q K : ℕ} [NeZero K] (hQ : 1 ≤ Q)
    (hK : ∀ q : PositiveLevel Q, q.val ∣ K)
    (v : ℕ → ℂ) (hv : ∀ q : ℕ, ‖v q‖ ≤ 1)
    (N A T : ℕ) (hend : A + T ≤ N + 1) :
    ‖intervalRemainder hK (oneLevel hQ) (oneLevel hQ) v v N A T‖ ≤
      2 * (Q : ℝ) ^ 4 := by
  let r : PositiveLevel Q := oneLevel hQ
  have hadm : ∀ q : PositiveLevel Q,
      r.val * q.val ≤ Q ∧ Nat.Coprime r.val q.val →
        ‖v (r.val * q.val)‖ ≤ (1 : ℝ) := by
    intro q _hq
    simpa [r, oneLevel] using hv q.val
  have hraw := actual_companion_interval_quartic_bound
    r r v v N A T hend 1 1 (by norm_num) (by norm_num) hadm hadm
  rw [← diagonalValue_eq_literal_sum hK r r v v N] at hraw
  have hbound :
      ‖(∑ i ∈ Finset.range T,
          finiteCompanion r (N - (A + i)) v * finiteCompanion r (A + i) v) -
        (T : ℂ) * diagonalValue hK r r v v N‖ ≤ 2 * (Q : ℝ) ^ 4 := by
    nlinarith
  exact intervalRemainder_norm_le_of_centered_bound
    hK r r v v N A T hend (2 * (Q : ℝ) ^ 4) hbound

/-- Conservative explicit norm bound for the exact V1.8.228 remainder.  The
quartic loss is inherited transparently from V1.8.207 and is not called small. -/
theorem canonical_intervalRemainder_norm_le_quartic
    {K : ℕ} [NeZero K]
    (B N : ℕ) (rho : ℝ) (hR : 1 < (B : ℝ) ^ rho)
    (_hB : 1 ≤ B) (hBN : B ≤ N)
    (hInterval : blockPairLower B N ≤ blockPairUpper B N)
    (hK : ∀ q : PositiveLevel ⌊((B : ℝ) ^ rho) ^ 2⌋₊, q.val ∣ K) :
    ‖intervalRemainder hK
        (oneLevel (log_cutoff_contains_one ((B : ℝ) ^ rho) hR))
        (oneLevel (log_cutoff_contains_one ((B : ℝ) ^ rho) hR))
        (logWeight ((B : ℝ) ^ rho) canonicalLogBump)
        (logWeight ((B : ℝ) ^ rho) canonicalLogBump)
        N (blockPairLower B N)
        (blockPairUpper B N - blockPairLower B N + 1)‖ ≤
      2 * (⌊((B : ℝ) ^ rho) ^ 2⌋₊ : ℝ) ^ 4 := by
  let A := blockPairLower B N
  let U := blockPairUpper B N
  let T := U - A + 1
  let Q := ⌊((B : ℝ) ^ rho) ^ 2⌋₊
  have hQ : 1 ≤ Q := by
    dsimp [Q]
    exact log_cutoff_contains_one ((B : ℝ) ^ rho) hR
  let wt := logWeight ((B : ℝ) ^ rho) canonicalLogBump
  have hUN : U ≤ N := by
    dsimp [U, blockPairUpper]
    omega
  have hend : A + T ≤ N + 1 := by
    dsimp [T]
    omega
  exact principal_intervalRemainder_norm_le_quartic hQ hK wt
    (norm_logWeight_canonical_le_one ((B : ℝ) ^ rho)) N A T hend

/-- Explicit real-part floor for the actual finite supported principal model.
The positive complete-period contribution and the finite remainder cost both
remain visible. -/
theorem canonicalPrincipalModelAt_real_floor
    {K : ℕ} [NeZero K]
    (B N : ℕ) (rho : ℝ) (hR : 1 < (B : ℝ) ^ rho)
    (hB : 1 ≤ B) (hBN : B ≤ N)
    (hInterval : blockPairLower B N ≤ blockPairUpper B N)
    (hEven : Even N)
    (hK : ∀ q : PositiveLevel ⌊((B : ℝ) ^ rho) ^ 2⌋₊, q.val ∣ K) :
    ((blockPairUpper B N - blockPairLower B N + 1 : ℕ) : ℝ) *
          (2 - Real.exp (Real.pi ^ 2 / 24)) -
        2 * (⌊((B : ℝ) ^ rho) ^ 2⌋₊ : ℝ) ^ 4 ≤
      (canonicalPrincipalModelAt B rho (N : ℤ)).re := by
  let T := blockPairUpper B N - blockPairLower B N + 1
  let Q := ⌊((B : ℝ) ^ rho) ^ 2⌋₊
  let d := principalDiagonal hK
    (logWeight ((B : ℝ) ^ rho) canonicalLogBump)
    (logWeight ((B : ℝ) ^ rho) canonicalLogBump) (N : ZMod K)
  let e := intervalRemainder hK
    (oneLevel (log_cutoff_contains_one ((B : ℝ) ^ rho) hR))
    (oneLevel (log_cutoff_contains_one ((B : ℝ) ^ rho) hR))
    (logWeight ((B : ℝ) ^ rho) canonicalLogBump)
    (logWeight ((B : ℝ) ^ rho) canonicalLogBump)
    N (blockPairLower B N) T
  have hdecomp :=
    canonicalPrincipalModelAt_eq_length_mul_diagonal_add_remainder
      B N rho hR hB hBN hInterval hK
  have hd : 2 - Real.exp (Real.pi ^ 2 / 24) ≤ d.re := by
    exact actual_principalDiagonal_canonicalLogBump_floor
      ((B : ℝ) ^ rho) hR hK hEven
  have heNorm : ‖e‖ ≤ 2 * (Q : ℝ) ^ 4 := by
    exact canonical_intervalRemainder_norm_le_quartic
      B N rho hR hB hBN hInterval hK
  have heAbs : |e.re| ≤ ‖e‖ := Complex.abs_re_le_norm e
  have hTnonneg : 0 ≤ (T : ℝ) := Nat.cast_nonneg T
  change (T : ℝ) * (2 - Real.exp (Real.pi ^ 2 / 24)) -
      2 * (Q : ℝ) ^ 4 ≤ (canonicalPrincipalModelAt B rho (N : ℤ)).re
  rw [hdecomp]
  simp only [Complex.add_re, Complex.mul_re, Complex.natCast_re,
    Complex.natCast_im, zero_mul, sub_zero]
  nlinarith [mul_le_mul_of_nonneg_left hd hTnonneg, neg_abs_le e.re]

/-- Strict positivity follows only when the explicit interval length dominates
the retained quartic boundary cost. -/
theorem canonicalPrincipalModelAt_real_pos_of_explicit_budget
    {K : ℕ} [NeZero K]
    (B N : ℕ) (rho : ℝ) (hR : 1 < (B : ℝ) ^ rho)
    (hB : 1 ≤ B) (hBN : B ≤ N)
    (hInterval : blockPairLower B N ≤ blockPairUpper B N)
    (hEven : Even N)
    (hK : ∀ q : PositiveLevel ⌊((B : ℝ) ^ rho) ^ 2⌋₊, q.val ∣ K)
    (hbudget :
      2 * (⌊((B : ℝ) ^ rho) ^ 2⌋₊ : ℝ) ^ 4 <
        ((blockPairUpper B N - blockPairLower B N + 1 : ℕ) : ℝ) *
          (2 - Real.exp (Real.pi ^ 2 / 24))) :
    0 < (canonicalPrincipalModelAt B rho (N : ℤ)).re :=
  lt_of_lt_of_le (by linarith)
    (canonicalPrincipalModelAt_real_floor
      B N rho hR hB hBN hInterval hEven hK)

end GoldbachCircleMethodFiniteIntervalRemainderReserveV18229
