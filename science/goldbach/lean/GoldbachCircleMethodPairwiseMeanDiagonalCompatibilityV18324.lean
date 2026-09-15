import GoldbachCircleMethodFullFrozenPairwiseIntervalV18323
import GoldbachCircleMethodActualFrozenModelCompleteDiagonalV18213

/-!
# Goldbach V1.8.324: pairwise means agree with the complete diagonal

The channel means obtained by completing each denominator pair separately are
identified with the earlier complete-period diagonal.  Thus the pairwise
route changes only the boundary-cost proof; it does not change the arithmetic
main term.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodPairwiseMeanDiagonalCompatibilityV18324

open GoldbachCircleMethodActiveActivePairwisePeriodV18317
open GoldbachCircleMethodActualCompanionCompleteDiagonalV18204
open GoldbachCircleMethodActualFrozenModelCompleteDiagonalV18213
open GoldbachCircleMethodActualPrincipalTwistCrossDiagonalV18210
open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodFiniteResiduePrefixV1866
open GoldbachCircleMethodFullFrozenPairwiseIntervalV18323
open GoldbachCircleMethodPairwiseActiveCostAggregationV18318
open GoldbachCircleMethodPairwiseChannelBindingV18322
open GoldbachCircleMethodPrincipalWindowBoundaryV18121
open GoldbachCircleMethodPrimitiveTwistedRamanujanSupportV18208

theorem principalPrincipalChannelMean_eq_principalDiagonal
    {Q K : ℕ} [NeZero K] (hQ : 1 ≤ Q)
    (hK : ∀ q : PositiveLevel Q, q.val ∣ K)
    (v w : ℕ → ℂ) (N : ℕ) :
    principalPrincipalChannelMean hQ v w N =
      principalDiagonal hK v w (N : ZMod K) := by
  unfold principalPrincipalChannelMean principalDiagonal
  apply Finset.sum_congr rfl
  intro q _hq
  simp only [map_natCast]
  rw [principal_literalCoefficient hQ, principal_literalCoefficient hQ]
  ring

/-- The pairwise principal/active mean is exactly the established complete
cross diagonal. -/
theorem principalActiveChannelMean_eq_crossDiagonal
    {Q K : ℕ} [NeZero K] (hQ : 1 ≤ Q)
    (hK : ∀ q : PositiveLevel Q, q.val ∣ K)
    (r : PositiveLevel Q)
    (chi : {χ : DirichletCharacter ℂ r.val // χ.IsPrimitive})
    (v w : ℕ → ℂ) (N : ℕ) :
    principalActiveChannelMean hQ r chi v w N =
      ((r.val : ℂ) * ((ArithmeticFunction.moebius r.val : ℤ) : ℂ) /
          (r.val.totient : ℂ) ^ 2) *
        chi.val (ZMod.castHom (hK r) (ZMod r.val) (N : ZMod K)) *
        coupledDiagonal hK r v w (N : ZMod K) := by
  unfold principalActiveChannelMean coupledDiagonal
  rw [Finset.mul_sum]
  simp only [mul_ite, mul_zero]
  rw [← Finset.sum_filter]
  change (∑ l ∈ activeComplementCarrier r, ∑ q : PositiveLevel Q,
      if q.val = r.val * l.val then
        literalCoefficient (oneLevel hQ) q v *
          ((r.val : ℂ) / (r.val.totient : ℂ)) *
          literalCoefficient r l w *
          twistedRamanujan r.val l.val chi.val
            ((N : ℕ) : ZMod (r.val * l.val))
      else 0) =
    ∑ l ∈ activeComplementCarrier r,
      (((r.val : ℂ) * ((ArithmeticFunction.moebius r.val : ℤ) : ℂ) /
          (r.val.totient : ℂ) ^ 2) *
        chi.val (ZMod.castHom (hK r) (ZMod r.val) (N : ZMod K))) *
      ((((ArithmeticFunction.moebius l.val : ℤ) : ℂ) ^ 2) /
          (l.val.totient : ℂ) ^ 2 *
        unitCharacterSum l.val
          (ZMod.castHom (hK l) (ZMod l.val) (N : ZMod K)) *
        v (r.val * l.val) * w (r.val * l.val))
  apply Finset.sum_congr rfl
  intro l hl
  have hsupp := (Finset.mem_filter.mp hl).2
  let qprod : PositiveLevel Q := boundedProductLevel r l hsupp.1
  rw [Finset.sum_eq_single qprod]
  · rw [if_pos]
    · rw [principal_literalCoefficient hQ]
      dsimp only [qprod, boundedProductLevel]
      unfold literalCoefficient twistedRamanujan
      rw [if_pos hsupp]
      simp only [map_natCast]
      have hc := coprime_cross_coefficient r.val l.val hsupp.2
        (v (r.val * l.val)) (w (r.val * l.val))
      calc
        _ = (((r.val : ℂ) / (r.val.totient : ℂ)) *
              ((((ArithmeticFunction.moebius l.val : ℤ) : ℂ) /
                  (l.val.totient : ℂ)) * w (r.val * l.val)) *
              ((((ArithmeticFunction.moebius (r.val * l.val) : ℤ) : ℂ) /
                  ((r.val * l.val).totient : ℂ)) * v (r.val * l.val))) *
            (chi.val ((N : ℕ) : ZMod r.val) *
              unitCharacterSum l.val ((N : ℕ) : ZMod l.val)) := by ring
        _ = (((r.val : ℂ) * ((ArithmeticFunction.moebius r.val : ℤ) : ℂ) /
                (r.val.totient : ℂ) ^ 2) *
              ((((ArithmeticFunction.moebius l.val : ℤ) : ℂ) ^ 2) /
                (l.val.totient : ℂ) ^ 2 *
                v (r.val * l.val) * w (r.val * l.val))) *
            (chi.val ((N : ℕ) : ZMod r.val) *
              unitCharacterSum l.val ((N : ℕ) : ZMod l.val)) := by rw [hc]
        _ = _ := by ring
    · rfl
  · intro q _hq hne
    rw [if_neg]
    intro heq
    apply hne
    apply Subtype.ext
    simpa [qprod, boundedProductLevel] using heq
  · simp

theorem activePrincipalChannelMean_eq_principalActiveSwap
    {Q : ℕ} (hQ : 1 ≤ Q) (r : PositiveLevel Q)
    (chi : {χ : DirichletCharacter ℂ r.val // χ.IsPrimitive})
    (v w : ℕ → ℂ) (N : ℕ) :
    activePrincipalChannelMean hQ r chi v w N =
      principalActiveChannelMean hQ r chi w v N := by
  unfold activePrincipalChannelMean principalActiveChannelMean
  apply Finset.sum_congr rfl
  intro l _hl
  apply Finset.sum_congr rfl
  intro q _hq
  split_ifs <;> ring

theorem activePrincipalChannelMean_eq_crossDiagonal
    {Q K : ℕ} [NeZero K] (hQ : 1 ≤ Q)
    (hK : ∀ q : PositiveLevel Q, q.val ∣ K)
    (r : PositiveLevel Q)
    (chi : {χ : DirichletCharacter ℂ r.val // χ.IsPrimitive})
    (v w : ℕ → ℂ) (N : ℕ) :
    activePrincipalChannelMean hQ r chi v w N =
      ((r.val : ℂ) * ((ArithmeticFunction.moebius r.val : ℤ) : ℂ) /
          (r.val.totient : ℂ) ^ 2) *
        chi.val (ZMod.castHom (hK r) (ZMod r.val) (N : ZMod K)) *
        coupledDiagonal hK r v w (N : ZMod K) := by
  rw [activePrincipalChannelMean_eq_principalActiveSwap,
    principalActiveChannelMean_eq_crossDiagonal hQ hK,
    coupledDiagonal_comm hK r w v]

/-- The pairwise active/active mean is the same complete self-convolution
diagonal as in V1.8.212. -/
theorem activeActiveChannelMean_eq_selfDiagonal
    {Q K : ℕ} [NeZero K]
    (hK : ∀ q : PositiveLevel Q, q.val ∣ K)
    (r : PositiveLevel Q)
    (chi : {χ : DirichletCharacter ℂ r.val // χ.IsPrimitive})
    (v w : ℕ → ℂ) (N : ℕ) :
    activeActiveChannelMean r chi v w N =
      ((r.val : ℂ) / (r.val.totient : ℂ) ^ 2) * chi.val (-1) *
        unitCharacterSum r.val
          (ZMod.castHom (hK r) (ZMod r.val) (N : ZMod K)) *
        coupledDiagonal hK r v w (N : ZMod K) := by
  unfold activeActiveChannelMean coupledDiagonal
  rw [Finset.mul_sum]
  simp only [mul_ite, mul_zero]
  rw [← Finset.sum_filter]
  change (∑ l ∈ activeComplementCarrier r,
      ∑ k ∈ activeComplementCarrier r, activeActivePairMean r l k chi v w N) =
    ∑ l ∈ activeComplementCarrier r,
      ((((r.val : ℂ) / (r.val.totient : ℂ) ^ 2) * chi.val (-1) *
          unitCharacterSum r.val
            (ZMod.castHom (hK r) (ZMod r.val) (N : ZMod K))) *
        ((((ArithmeticFunction.moebius l.val : ℤ) : ℂ) ^ 2) /
          (l.val.totient : ℂ) ^ 2 *
          unitCharacterSum l.val
            (ZMod.castHom (hK l) (ZMod l.val) (N : ZMod K)) *
          v (r.val * l.val) * w (r.val * l.val)))
  apply Finset.sum_congr rfl
  intro l hl
  have hsupp := (Finset.mem_filter.mp hl).2
  rw [Finset.sum_eq_single l]
  · unfold activeActivePairMean
    rw [if_pos rfl]
    unfold literalCoefficient
    rw [if_pos hsupp, if_pos hsupp]
    simp only [map_natCast]
    ring
  · intro k hk hne
    unfold activeActivePairMean
    rw [if_neg]
    intro heq
    exact hne (Subtype.ext heq.symm)
  · intro hnot
    exact (hnot hl).elim

/-- Pairwise completion preserves the complete frozen-model arithmetic mean. -/
theorem fullFrozenPairwiseMean_eq_completeDiagonal
    {Q K : ℕ} [NeZero K] (hQ : 1 ≤ Q)
    (hK : ∀ q : PositiveLevel Q, q.val ∣ K)
    (r : PositiveLevel Q)
    (chi : {χ : DirichletCharacter ℂ r.val // χ.IsPrimitive})
    (v w : ℕ → ℂ) (t₁ t₂ : ℂ) (N : ℕ) :
    fullFrozenPairwiseMean hQ r chi v w t₁ t₂ N =
      principalDiagonal hK v w (N : ZMod K) +
        ((r.val : ℂ) / (r.val.totient : ℂ) ^ 2) *
        (t₁ * t₂ * chi.val (-1) *
            unitCharacterSum r.val
              (ZMod.castHom (hK r) (ZMod r.val) (N : ZMod K)) -
          (t₁ + t₂) * ((ArithmeticFunction.moebius r.val : ℤ) : ℂ) *
            chi.val (ZMod.castHom (hK r) (ZMod r.val) (N : ZMod K))) *
        coupledDiagonal hK r v w (N : ZMod K) := by
  unfold fullFrozenPairwiseMean
  rw [principalPrincipalChannelMean_eq_principalDiagonal hQ hK,
    principalActiveChannelMean_eq_crossDiagonal hQ hK,
    activePrincipalChannelMean_eq_crossDiagonal hQ hK,
    activeActiveChannelMean_eq_selfDiagonal hK]
  ring

/-- Readback against the old common-period theorem.  The common period occurs
only in this compatibility statement, never in the new boundary budget. -/
theorem normalized_complete_frozen_eq_pairwiseMean
    {Q K : ℕ} [NeZero K] (hQ : 1 ≤ Q)
    (hK : ∀ q : PositiveLevel Q, q.val ∣ K)
    (r : PositiveLevel Q)
    (chi : {χ : DirichletCharacter ℂ r.val // χ.IsPrimitive})
    (hInv : chi.val⁻¹ = chi.val)
    (v w : ℕ → ℂ) (t₁ t₂ : ℂ) (N : ℕ) :
    (∑ x : ZMod K,
      frozenCoefficient hQ r chi v t₁ ((N : ZMod K) - x) *
        frozenCoefficient hQ r chi w t₂ x) / (K : ℂ) =
      fullFrozenPairwiseMean hQ r chi v w t₁ t₂ N := by
  rw [actual_frozen_model_complete_diagonal hQ hK r chi hInv]
  exact (fullFrozenPairwiseMean_eq_completeDiagonal
    hQ hK r chi v w t₁ t₂ N).symm

end GoldbachCircleMethodPairwiseMeanDiagonalCompatibilityV18324
