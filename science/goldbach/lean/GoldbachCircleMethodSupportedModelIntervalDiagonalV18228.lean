import GoldbachCircleMethodBlockPairCarrierV18227
import GoldbachCircleMethodActualCompanionIntervalTransferV18205
import GoldbachCircleMethodActualFrozenModelCompleteDiagonalV18213

/-!
# Goldbach V1.8.228: supported model interval diagonal

The exact block-pair interval from V1.8.227 is reindexed to the half-open
interval expected by V1.8.205.  The canonical supported principal-model
coefficient is then decomposed into interval length times the actual complete
principal diagonal plus the literal finite-period remainder.  The remainder is
retained exactly and receives no sign or size claim in this module.
-/

open scoped BigOperators Classical

set_option autoImplicit false

namespace GoldbachCircleMethodSupportedModelIntervalDiagonalV18228

open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodFiniteCompanionBindingV18118
open GoldbachCircleMethodLogCutoffPresieveBindingV18120
open GoldbachCircleMethodPrincipalWindowBoundaryV18121
open GoldbachCircleMethodActualCompanionCompleteDiagonalV18204
open GoldbachCircleMethodActualCompanionIntervalTransferV18205
open GoldbachCircleMethodActualPrincipalTwistCrossDiagonalV18210
open GoldbachCircleMethodActualFrozenModelCompleteDiagonalV18213
open GoldbachCircleMethodUncorrectedSupportedErrorConvolutionV18184
open GoldbachCircleMethodCanonicalBumpPrincipalFloorV18220
open GoldbachCircleMethodActualResidualExactDecompositionV18225
open GoldbachCircleMethodBlockPairCarrierV18227

/-- Exact reindexing of a nonempty closed natural interval to a shifted range. -/
theorem sum_Icc_eq_sum_range_shift
    {M : Type*} [AddCommMonoid M] (A U : ℕ) (hAU : A ≤ U) (f : ℕ → M) :
    (∑ n ∈ Finset.Icc A U, f n) =
      ∑ i ∈ Finset.range (U - A + 1), f (A + i) := by
  symm
  apply Finset.sum_bij (fun i _hi => A + i)
  · intro i hi
    simp only [Finset.mem_range] at hi
    simp only [Finset.mem_Icc]
    omega
  · intro i₁ hi₁ i₂ hi₂ heq
    omega
  · intro n hn
    simp only [Finset.mem_Icc] at hn
    refine ⟨n - A, ?_, ?_⟩
    · simp only [Finset.mem_range]
      omega
    · omega
  · intro i hi
    rfl

/-- On its declared block, the supported principal model is literally the
conductor-one finite companion. -/
theorem supportedPrincipalModel_eq_finiteCompanion_on_block
    (B n : ℕ) (rho : ℝ) (hR : 1 < (B : ℝ) ^ rho)
    (hn : n ∈ blockCarrier B) :
    supportedPrincipalModel B n ((B : ℝ) ^ rho) canonicalLogBump =
      finiteCompanion
        (oneLevel (log_cutoff_contains_one ((B : ℝ) ^ rho) hR)) n
        (logWeight ((B : ℝ) ^ rho) canonicalLogBump) := by
  unfold supportedPrincipalModel
  rw [dif_pos hR]
  have hn' : n ∈ Finset.Ioc (B / 2) B := by
    simpa only [blockCarrier] using hn
  rw [if_pos hn']

/-- The V1.8.205 literal diagonal at conductor one is definitionally the
V1.8.213 actual principal diagonal. -/
theorem diagonalValue_one_eq_principalDiagonal
    {Q K : ℕ} [NeZero K] (hQ : 1 ≤ Q)
    (hK : ∀ q : PositiveLevel Q, q.val ∣ K)
    (v w : ℕ → ℂ) (N : ℕ) :
    diagonalValue hK (oneLevel hQ) (oneLevel hQ) v w N =
      principalDiagonal hK v w (N : ZMod K) := by
  unfold diagonalValue principalDiagonal
  apply Finset.sum_congr rfl
  intro q _hq
  rw [principal_literalCoefficient hQ q v,
    principal_literalCoefficient hQ q w]
  ring

/-- The canonical supported principal-model coefficient is exactly a finite
companion convolution over the endpoint-explicit pair interval. -/
theorem canonicalPrincipalModelAt_nat_eq_finiteCompanion_interval
    (B N : ℕ) (rho : ℝ) (hR : 1 < (B : ℝ) ^ rho)
    (hB : 1 ≤ B) (hBN : B ≤ N) :
    canonicalPrincipalModelAt B rho (N : ℤ) =
      ∑ n ∈ Finset.Icc (blockPairLower B N) (blockPairUpper B N),
        finiteCompanion
            (oneLevel (log_cutoff_contains_one ((B : ℝ) ^ rho) hR))
            (N - n) (logWeight ((B : ℝ) ^ rho) canonicalLogBump) *
          finiteCompanion
            (oneLevel (log_cutoff_contains_one ((B : ℝ) ^ rho) hR))
            n (logWeight ((B : ℝ) ^ rho) canonicalLogBump) := by
  rw [canonicalPrincipalModelAt_nat_eq_interval B N rho hB hBN]
  apply Finset.sum_congr rfl
  intro n hn
  have hpair : n ∈ pairFirstCarrier (blockCarrier B) N := by
    rw [pairFirstCarrier_block_eq_Icc B N hB hBN]
    exact hn
  have hnBlock : n ∈ blockCarrier B := (Finset.mem_filter.mp hpair).1
  have hcompBlock : N - n ∈ blockCarrier B := (Finset.mem_filter.mp hpair).2
  rw [supportedPrincipalModel_eq_finiteCompanion_on_block B n rho hR hnBlock,
    supportedPrincipalModel_eq_finiteCompanion_on_block B (N - n) rho hR hcompBlock]
  ring

/-- Exact finite-interval decomposition of the canonical supported principal
model.  The interval remainder is retained as an explicit signed complex term. -/
theorem canonicalPrincipalModelAt_eq_length_mul_diagonal_add_remainder
    {K : ℕ} [NeZero K]
    (B N : ℕ) (rho : ℝ) (hR : 1 < (B : ℝ) ^ rho)
    (hB : 1 ≤ B) (hBN : B ≤ N)
    (hInterval : blockPairLower B N ≤ blockPairUpper B N)
    (hK : ∀ q : PositiveLevel ⌊((B : ℝ) ^ rho) ^ 2⌋₊, q.val ∣ K) :
    canonicalPrincipalModelAt B rho (N : ℤ) =
      ((blockPairUpper B N - blockPairLower B N + 1 : ℕ) : ℂ) *
          principalDiagonal hK
            (logWeight ((B : ℝ) ^ rho) canonicalLogBump)
            (logWeight ((B : ℝ) ^ rho) canonicalLogBump) (N : ZMod K) +
        intervalRemainder hK
          (oneLevel (log_cutoff_contains_one ((B : ℝ) ^ rho) hR))
          (oneLevel (log_cutoff_contains_one ((B : ℝ) ^ rho) hR))
          (logWeight ((B : ℝ) ^ rho) canonicalLogBump)
          (logWeight ((B : ℝ) ^ rho) canonicalLogBump)
          N (blockPairLower B N)
          (blockPairUpper B N - blockPairLower B N + 1) := by
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
  rw [canonicalPrincipalModelAt_nat_eq_finiteCompanion_interval B N rho hR hB hBN]
  change (∑ n ∈ Finset.Icc A U,
      finiteCompanion (oneLevel hQ) (N - n) wt *
        finiteCompanion (oneLevel hQ) n wt) = _
  rw [sum_Icc_eq_sum_range_shift A U hInterval]
  rw [actual_companion_interval_decomposition hK (oneLevel hQ) (oneLevel hQ)
    wt wt N A T hend]
  rw [diagonalValue_one_eq_principalDiagonal hQ hK wt wt N]

end GoldbachCircleMethodSupportedModelIntervalDiagonalV18228
