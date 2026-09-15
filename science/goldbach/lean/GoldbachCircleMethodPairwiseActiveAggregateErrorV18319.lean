import GoldbachCircleMethodPairwiseActiveCostAggregationV18318

/-!
# Goldbach V1.8.319: aggregate pairwise active interval errors

The actual principal/active and active/active pair errors are summed on the
unchanged coupled carrier.  Triangle inequality plus the exact V1.8.316/317
pair bounds identifies their costs with V1.8.318 and hence gives a quartic
aggregate bound.  This still concerns frozen literal coefficients; spatial
power-weight transport is a later, separate obligation.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodPairwiseActiveAggregateErrorV18319

open GoldbachCircleMethodActiveActivePairwisePeriodV18317
open GoldbachCircleMethodActualCompanionCompleteDiagonalV18204
open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodFiniteResiduePrefixV1866
open GoldbachCircleMethodPairwiseActiveCostAggregationV18318
open GoldbachCircleMethodPrincipalActivePairwisePeriodV18316
open GoldbachCircleMethodPrincipalWindowBoundaryV18121
open GoldbachCircleMethodPrimitiveTwistedRamanujanSupportV18208

/-- Actual centered error for one principal denominator and one admitted active
complement denominator. -/
noncomputable def principalActivePairError {Q : ℕ} (hQ : 1 ≤ Q)
    (r l q : PositiveLevel Q)
    (chi : {χ : DirichletCharacter ℂ r.val // χ.IsPrimitive})
    (v w : ℕ → ℂ) (N A T : ℕ) : ℂ :=
  (∑ i ∈ Finset.range T,
      (literalCoefficient (oneLevel hQ) q v *
        unitCharacterSum q.val ((N - (A + i) : ℕ) : ZMod q.val)) *
      activeTwistedLiteralTerm r l chi w
        ((A + i : ℕ) : ZMod (r.val * l.val))) -
    (T : ℂ) *
      (if q.val = r.val * l.val then
        literalCoefficient (oneLevel hQ) q v *
          ((r.val : ℂ) / (r.val.totient : ℂ)) *
          literalCoefficient r l w *
          twistedRamanujan r.val l.val chi.val
            ((N : ℕ) : ZMod (r.val * l.val))
      else 0)

/-- Actual centered error for one pair of admitted active complements at a
fixed primitive conductor. -/
noncomputable def activeActivePairError {Q : ℕ}
    (r l k : PositiveLevel Q)
    (chi : {χ : DirichletCharacter ℂ r.val // χ.IsPrimitive})
    (v w : ℕ → ℂ) (N A T : ℕ) : ℂ :=
  (∑ i ∈ Finset.range T,
      activeTwistedLiteralTerm r l chi v
          ((N - (A + i) : ℕ) : ZMod (r.val * l.val)) *
        activeTwistedLiteralTerm r k chi w
          ((A + i : ℕ) : ZMod (r.val * k.val))) -
    (T : ℂ) * activeActivePairMean r l k chi v w N

/-- Sum of all principal/active pair errors on the genuine carrier. -/
noncomputable def principalActiveAggregateError {Q : ℕ} (hQ : 1 ≤ Q)
    (r : PositiveLevel Q)
    (chi : {χ : DirichletCharacter ℂ r.val // χ.IsPrimitive})
    (v w : ℕ → ℂ) (N A T : ℕ) : ℂ :=
  ∑ l ∈ activeComplementCarrier r, ∑ q : PositiveLevel Q,
    principalActivePairError hQ r l q chi v w N A T

/-- Sum of all active/active pair errors on the genuine carrier. -/
noncomputable def activeActiveAggregateError {Q : ℕ}
    (r : PositiveLevel Q)
    (chi : {χ : DirichletCharacter ℂ r.val // χ.IsPrimitive})
    (v w : ℕ → ℂ) (N A T : ℕ) : ℂ :=
  ∑ l ∈ activeComplementCarrier r, ∑ k ∈ activeComplementCarrier r,
    activeActivePairError r l k chi v w N A T

theorem principalActiveAggregateError_norm_le_cost {Q : ℕ} (hQ : 1 ≤ Q)
    (r : PositiveLevel Q)
    (chi : {χ : DirichletCharacter ℂ r.val // χ.IsPrimitive})
    (v w : ℕ → ℂ) (N A T : ℕ) (hend : A + T ≤ N + 1)
    (V W : ℝ) (hV : 0 ≤ V) (hW : 0 ≤ W)
    (hv : ∀ q : PositiveLevel Q, ‖v q.val‖ ≤ V)
    (hw : ∀ n : ℕ, ‖w n‖ ≤ W) :
    ‖principalActiveAggregateError hQ r chi v w N A T‖ ≤
      principalActivePairwiseCost r V W := by
  unfold principalActiveAggregateError principalActivePairwiseCost
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro l hl
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro q _hq
  have hsupp := (Finset.mem_filter.mp hl).2
  simpa only [principalActivePairError] using
    (principal_active_pair_interval_norm_le hQ r l q hsupp.1 hsupp.2 chi
      v w N A T hend V W hV hW (hv q) (hw (r.val * l.val)))

theorem activeActiveAggregateError_norm_le_cost {Q : ℕ}
    (r : PositiveLevel Q)
    (chi : {χ : DirichletCharacter ℂ r.val // χ.IsPrimitive})
    (hInv : chi.val⁻¹ = chi.val)
    (v w : ℕ → ℂ) (N A T : ℕ) (hend : A + T ≤ N + 1)
    (V W : ℝ) (hV : 0 ≤ V) (hW : 0 ≤ W)
    (hv : ∀ n : ℕ, ‖v n‖ ≤ V)
    (hw : ∀ n : ℕ, ‖w n‖ ≤ W) :
    ‖activeActiveAggregateError r chi v w N A T‖ ≤
      activeActivePairwiseCost r V W := by
  unfold activeActiveAggregateError activeActivePairwiseCost
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro l hl
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro k hk
  have hsupp_l := (Finset.mem_filter.mp hl).2
  have hsupp_k := (Finset.mem_filter.mp hk).2
  simpa only [activeActivePairError] using
    (active_active_pair_interval_norm_le r l k
      hsupp_l.1 hsupp_k.1 hsupp_l.2 hsupp_k.2 chi hInv
      v w N A T hend V W hV hW
      (hv (r.val * l.val)) (hw (r.val * k.val)))

/-- Full principal/active aggregate error with no common-period loss. -/
theorem principalActiveAggregateError_norm_le_quartic {Q : ℕ} (hQ : 1 ≤ Q)
    (r : PositiveLevel Q)
    (chi : {χ : DirichletCharacter ℂ r.val // χ.IsPrimitive})
    (v w : ℕ → ℂ) (N A T : ℕ) (hend : A + T ≤ N + 1)
    (V W : ℝ) (hV : 0 ≤ V) (hW : 0 ≤ W)
    (hv : ∀ q : PositiveLevel Q, ‖v q.val‖ ≤ V)
    (hw : ∀ n : ℕ, ‖w n‖ ≤ W) :
    ‖principalActiveAggregateError hQ r chi v w N A T‖ ≤
      2 * (Q : ℝ) ^ 4 * V * W :=
  (principalActiveAggregateError_norm_le_cost hQ r chi v w N A T hend
    V W hV hW hv hw).trans
      (principalActivePairwiseCost_le_quartic r V W hV hW)

/-- Full active/active aggregate error with no common-period loss. -/
theorem activeActiveAggregateError_norm_le_quartic {Q : ℕ}
    (r : PositiveLevel Q)
    (chi : {χ : DirichletCharacter ℂ r.val // χ.IsPrimitive})
    (hInv : chi.val⁻¹ = chi.val)
    (v w : ℕ → ℂ) (N A T : ℕ) (hend : A + T ≤ N + 1)
    (V W : ℝ) (hV : 0 ≤ V) (hW : 0 ≤ W)
    (hv : ∀ n : ℕ, ‖v n‖ ≤ V)
    (hw : ∀ n : ℕ, ‖w n‖ ≤ W) :
    ‖activeActiveAggregateError r chi v w N A T‖ ≤
      2 * (Q : ℝ) ^ 4 * V * W :=
  (activeActiveAggregateError_norm_le_cost r chi hInv v w N A T hend
    V W hV hW hv hw).trans
      (activeActivePairwiseCost_le_quartic r V W hV hW)

end GoldbachCircleMethodPairwiseActiveAggregateErrorV18319
