import GoldbachCircleMethodLiteralExpansionWithoutCommonPeriodV18321

/-!
# Goldbach V1.8.322: pairwise channel binding

The three channels containing at least one active factor are identified
exactly with the aggregate pairwise errors from V1.8.319/320.  These are
finite distributive identities on natural inputs; no periodic replacement or
common-LCM hypothesis occurs.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodPairwiseChannelBindingV18322

open GoldbachCircleMethodActiveActivePairwisePeriodV18317
open GoldbachCircleMethodActivePrincipalPairwisePeriodV18320
open GoldbachCircleMethodActualCompanionCompleteDiagonalV18204
open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodFiniteCompanionBindingV18118
open GoldbachCircleMethodFiniteResiduePrefixV1866
open GoldbachCircleMethodLiteralExpansionWithoutCommonPeriodV18321
open GoldbachCircleMethodPairwiseActiveAggregateErrorV18319
open GoldbachCircleMethodPairwiseActiveCostAggregationV18318
open GoldbachCircleMethodPrincipalActivePairwisePeriodV18316
open GoldbachCircleMethodPrincipalWindowBoundaryV18121
open GoldbachCircleMethodPrimitiveTwistedRamanujanSupportV18208

noncomputable def principalActiveChannelMean {Q : ℕ} (hQ : 1 ≤ Q)
    (r : PositiveLevel Q)
    (chi : {χ : DirichletCharacter ℂ r.val // χ.IsPrimitive})
    (v w : ℕ → ℂ) (N : ℕ) : ℂ :=
  ∑ l ∈ activeComplementCarrier r, ∑ q : PositiveLevel Q,
    if q.val = r.val * l.val then
      literalCoefficient (oneLevel hQ) q v *
        ((r.val : ℂ) / (r.val.totient : ℂ)) *
        literalCoefficient r l w *
        twistedRamanujan r.val l.val chi.val
          ((N : ℕ) : ZMod (r.val * l.val))
    else 0

noncomputable def activePrincipalChannelMean {Q : ℕ} (hQ : 1 ≤ Q)
    (r : PositiveLevel Q)
    (chi : {χ : DirichletCharacter ℂ r.val // χ.IsPrimitive})
    (v w : ℕ → ℂ) (N : ℕ) : ℂ :=
  ∑ l ∈ activeComplementCarrier r, ∑ q : PositiveLevel Q,
    if q.val = r.val * l.val then
      ((r.val : ℂ) / (r.val.totient : ℂ)) *
        literalCoefficient r l v *
        literalCoefficient (oneLevel hQ) q w *
        twistedRamanujan r.val l.val chi.val
          ((N : ℕ) : ZMod (r.val * l.val))
    else 0

noncomputable def activeActiveChannelMean {Q : ℕ}
    (r : PositiveLevel Q)
    (chi : {χ : DirichletCharacter ℂ r.val // χ.IsPrimitive})
    (v w : ℕ → ℂ) (N : ℕ) : ℂ :=
  ∑ l ∈ activeComplementCarrier r, ∑ k ∈ activeComplementCarrier r,
    activeActivePairMean r l k chi v w N

noncomputable def principalActiveChannelError {Q : ℕ} (hQ : 1 ≤ Q)
    (r : PositiveLevel Q)
    (chi : {χ : DirichletCharacter ℂ r.val // χ.IsPrimitive})
    (v w : ℕ → ℂ) (N A T : ℕ) : ℂ :=
  (∑ i ∈ Finset.range T,
      finiteCompanion (oneLevel hQ) (N - (A + i)) v *
        windowCoefficient r (A + i) w chi) -
    (T : ℂ) * principalActiveChannelMean hQ r chi v w N

noncomputable def activePrincipalChannelError {Q : ℕ} (hQ : 1 ≤ Q)
    (r : PositiveLevel Q)
    (chi : {χ : DirichletCharacter ℂ r.val // χ.IsPrimitive})
    (v w : ℕ → ℂ) (N A T : ℕ) : ℂ :=
  (∑ i ∈ Finset.range T,
      windowCoefficient r (N - (A + i)) v chi *
        finiteCompanion (oneLevel hQ) (A + i) w) -
    (T : ℂ) * activePrincipalChannelMean hQ r chi v w N

noncomputable def activeActiveChannelError {Q : ℕ}
    (r : PositiveLevel Q)
    (chi : {χ : DirichletCharacter ℂ r.val // χ.IsPrimitive})
    (v w : ℕ → ℂ) (N A T : ℕ) : ℂ :=
  (∑ i ∈ Finset.range T,
      windowCoefficient r (N - (A + i)) v chi *
        windowCoefficient r (A + i) w chi) -
    (T : ℂ) * activeActiveChannelMean r chi v w N

theorem principalActiveChannelError_eq_aggregate {Q : ℕ} (hQ : 1 ≤ Q)
    (r : PositiveLevel Q)
    (chi : {χ : DirichletCharacter ℂ r.val // χ.IsPrimitive})
    (v w : ℕ → ℂ) (N A T : ℕ) :
    principalActiveChannelError hQ r chi v w N A T =
      principalActiveAggregateError hQ r chi v w N A T := by
  have he :
      (∑ i ∈ Finset.range T,
        finiteCompanion (oneLevel hQ) (N - (A + i)) v *
          windowCoefficient r (A + i) w chi) =
      ∑ l ∈ activeComplementCarrier r, ∑ q : PositiveLevel Q,
        ∑ i ∈ Finset.range T,
          (literalCoefficient (oneLevel hQ) q v *
            unitCharacterSum q.val ((N - (A + i) : ℕ) : ZMod q.val)) *
          activeTwistedLiteralTerm r l chi w
            ((A + i : ℕ) : ZMod (r.val * l.val)) := by
    simp_rw [finiteCompanion_eq_literalSum,
      windowCoefficient_eq_activeLiteralSum, Finset.sum_mul, Finset.mul_sum]
    calc
      _ = ∑ q : PositiveLevel Q, ∑ i ∈ Finset.range T,
          ∑ l ∈ activeComplementCarrier r,
            (literalCoefficient (oneLevel hQ) q v *
              unitCharacterSum q.val ((N - (A + i) : ℕ) : ZMod q.val)) *
            activeTwistedLiteralTerm r l chi w
              ((A + i : ℕ) : ZMod (r.val * l.val)) := by
            rw [Finset.sum_comm]
      _ = ∑ q : PositiveLevel Q, ∑ l ∈ activeComplementCarrier r,
          ∑ i ∈ Finset.range T,
            (literalCoefficient (oneLevel hQ) q v *
              unitCharacterSum q.val ((N - (A + i) : ℕ) : ZMod q.val)) *
            activeTwistedLiteralTerm r l chi w
              ((A + i : ℕ) : ZMod (r.val * l.val)) := by
            apply Finset.sum_congr rfl
            intro q _hq
            rw [Finset.sum_comm]
      _ = _ := by rw [Finset.sum_comm]
  unfold principalActiveChannelError principalActiveAggregateError
    principalActivePairError principalActiveChannelMean
  rw [he]
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum]

theorem activePrincipalChannelError_eq_aggregate {Q : ℕ} (hQ : 1 ≤ Q)
    (r : PositiveLevel Q)
    (chi : {χ : DirichletCharacter ℂ r.val // χ.IsPrimitive})
    (v w : ℕ → ℂ) (N A T : ℕ) :
    activePrincipalChannelError hQ r chi v w N A T =
      activePrincipalAggregateError hQ r chi v w N A T := by
  have he :
      (∑ i ∈ Finset.range T,
        windowCoefficient r (N - (A + i)) v chi *
          finiteCompanion (oneLevel hQ) (A + i) w) =
      ∑ l ∈ activeComplementCarrier r, ∑ q : PositiveLevel Q,
        ∑ i ∈ Finset.range T,
          activeTwistedLiteralTerm r l chi v
              ((N - (A + i) : ℕ) : ZMod (r.val * l.val)) *
            (literalCoefficient (oneLevel hQ) q w *
              unitCharacterSum q.val ((A + i : ℕ) : ZMod q.val)) := by
    simp_rw [finiteCompanion_eq_literalSum,
      windowCoefficient_eq_activeLiteralSum, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro l _hl
    rw [Finset.sum_comm]
  unfold activePrincipalChannelError activePrincipalAggregateError
    activePrincipalPairError activePrincipalChannelMean
  rw [he]
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum]

theorem activeActiveChannelError_eq_aggregate {Q : ℕ}
    (r : PositiveLevel Q)
    (chi : {χ : DirichletCharacter ℂ r.val // χ.IsPrimitive})
    (v w : ℕ → ℂ) (N A T : ℕ) :
    activeActiveChannelError r chi v w N A T =
      activeActiveAggregateError r chi v w N A T := by
  have he :
      (∑ i ∈ Finset.range T,
        windowCoefficient r (N - (A + i)) v chi *
          windowCoefficient r (A + i) w chi) =
      ∑ l ∈ activeComplementCarrier r, ∑ k ∈ activeComplementCarrier r,
        ∑ i ∈ Finset.range T,
          activeTwistedLiteralTerm r l chi v
              ((N - (A + i) : ℕ) : ZMod (r.val * l.val)) *
            activeTwistedLiteralTerm r k chi w
              ((A + i : ℕ) : ZMod (r.val * k.val)) := by
    simp_rw [windowCoefficient_eq_activeLiteralSum,
      Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro l _hl
    rw [Finset.sum_comm]
  unfold activeActiveChannelError activeActiveAggregateError
    activeActivePairError activeActiveChannelMean
  rw [he]
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum]

end GoldbachCircleMethodPairwiseChannelBindingV18322
