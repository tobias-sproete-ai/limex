import GoldbachCircleMethodFourChannelAbelTransportV18328

/-!
# Goldbach V1.8.329: actual pairwise channel prefix bounds

The four channel errors from V1.8.323 are rewritten as prefix sums of centered
sequences.  Their already audited pairwise-period estimates therefore supply
the exact hypotheses required by finite Abel transport, uniformly for every
prefix of the interval.  No global LCM is used.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodPairwiseCenteredPrefixV18329

open GoldbachCircleMethodActivePrincipalPairwisePeriodV18320
open GoldbachCircleMethodActualCompanionCompleteDiagonalV18204
open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodCoupledCompanionRemainderBoundV18207
open GoldbachCircleMethodFiniteCompanionBindingV18118
open GoldbachCircleMethodFullFrozenPairwiseIntervalV18323
open GoldbachCircleMethodPairwiseActiveAggregateErrorV18319
open GoldbachCircleMethodPairwiseChannelBindingV18322
open GoldbachCircleMethodPrincipalWindowBoundaryV18121

noncomputable def ppCentered {Q : ℕ} (hQ : 1 ≤ Q)
    (v w : ℕ → ℂ) (N A i : ℕ) : ℂ :=
  finiteCompanion (oneLevel hQ) (N - (A + i)) v *
      finiteCompanion (oneLevel hQ) (A + i) w -
    principalPrincipalChannelMean hQ v w N

noncomputable def paCentered {Q : ℕ} (hQ : 1 ≤ Q)
    (r : PositiveLevel Q)
    (chi : {χ : DirichletCharacter ℂ r.val // χ.IsPrimitive})
    (v w : ℕ → ℂ) (N A i : ℕ) : ℂ :=
  finiteCompanion (oneLevel hQ) (N - (A + i)) v *
      windowCoefficient r (A + i) w chi -
    principalActiveChannelMean hQ r chi v w N

noncomputable def apCentered {Q : ℕ} (hQ : 1 ≤ Q)
    (r : PositiveLevel Q)
    (chi : {χ : DirichletCharacter ℂ r.val // χ.IsPrimitive})
    (v w : ℕ → ℂ) (N A i : ℕ) : ℂ :=
  windowCoefficient r (N - (A + i)) v chi *
      finiteCompanion (oneLevel hQ) (A + i) w -
    activePrincipalChannelMean hQ r chi v w N

noncomputable def aaCentered {Q : ℕ}
    (r : PositiveLevel Q)
    (chi : {χ : DirichletCharacter ℂ r.val // χ.IsPrimitive})
    (v w : ℕ → ℂ) (N A i : ℕ) : ℂ :=
  windowCoefficient r (N - (A + i)) v chi *
      windowCoefficient r (A + i) w chi -
    activeActiveChannelMean r chi v w N

theorem sum_ppCentered_eq_error {Q : ℕ} (hQ : 1 ≤ Q)
    (v w : ℕ → ℂ) (N A k : ℕ) :
    ∑ i ∈ Finset.range k, ppCentered hQ v w N A i =
      principalPrincipalChannelError hQ v w N A k := by
  unfold ppCentered principalPrincipalChannelError
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

theorem sum_paCentered_eq_error {Q : ℕ} (hQ : 1 ≤ Q)
    (r : PositiveLevel Q)
    (chi : {χ : DirichletCharacter ℂ r.val // χ.IsPrimitive})
    (v w : ℕ → ℂ) (N A k : ℕ) :
    ∑ i ∈ Finset.range k, paCentered hQ r chi v w N A i =
      principalActiveChannelError hQ r chi v w N A k := by
  unfold paCentered principalActiveChannelError
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

theorem sum_apCentered_eq_error {Q : ℕ} (hQ : 1 ≤ Q)
    (r : PositiveLevel Q)
    (chi : {χ : DirichletCharacter ℂ r.val // χ.IsPrimitive})
    (v w : ℕ → ℂ) (N A k : ℕ) :
    ∑ i ∈ Finset.range k, apCentered hQ r chi v w N A i =
      activePrincipalChannelError hQ r chi v w N A k := by
  unfold apCentered activePrincipalChannelError
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

theorem sum_aaCentered_eq_error {Q : ℕ}
    (r : PositiveLevel Q)
    (chi : {χ : DirichletCharacter ℂ r.val // χ.IsPrimitive})
    (v w : ℕ → ℂ) (N A k : ℕ) :
    ∑ i ∈ Finset.range k, aaCentered r chi v w N A i =
      activeActiveChannelError r chi v w N A k := by
  unfold aaCentered activeActiveChannelError
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- Every principal/principal prefix retains the same quartic boundary budget. -/
theorem ppCentered_prefix_norm_le {Q : ℕ} (hQ : 1 ≤ Q)
    (v w : ℕ → ℂ) (N A T : ℕ) (hend : A + T ≤ N + 1)
    (V W : ℝ) (hV : 0 ≤ V) (hW : 0 ≤ W)
    (hv : ∀ n : ℕ, ‖v n‖ ≤ V) (hw : ∀ n : ℕ, ‖w n‖ ≤ W) :
    ∀ k : ℕ, k ≤ T →
      ‖∑ i ∈ Finset.range k, ppCentered hQ v w N A i‖ ≤
        2 * (Q : ℝ) ^ 4 * V * W := by
  intro k hk
  rw [sum_ppCentered_eq_error]
  simpa [principalPrincipalChannelError, principalPrincipalChannelMean] using
    (actual_companion_interval_quartic_bound
      (oneLevel hQ) (oneLevel hQ) v w N A k (by omega) V W hV hW
      (fun q _hq => by simpa [oneLevel] using hv q.val)
      (fun l _hl => by simpa [oneLevel] using hw l.val))

/-- Every principal/active prefix retains the same quartic boundary budget. -/
theorem paCentered_prefix_norm_le {Q : ℕ} (hQ : 1 ≤ Q)
    (r : PositiveLevel Q)
    (chi : {χ : DirichletCharacter ℂ r.val // χ.IsPrimitive})
    (v w : ℕ → ℂ) (N A T : ℕ) (hend : A + T ≤ N + 1)
    (V W : ℝ) (hV : 0 ≤ V) (hW : 0 ≤ W)
    (hv : ∀ n : ℕ, ‖v n‖ ≤ V) (hw : ∀ n : ℕ, ‖w n‖ ≤ W) :
    ∀ k : ℕ, k ≤ T →
      ‖∑ i ∈ Finset.range k, paCentered hQ r chi v w N A i‖ ≤
        2 * (Q : ℝ) ^ 4 * V * W := by
  intro k hk
  rw [sum_paCentered_eq_error, principalActiveChannelError_eq_aggregate]
  exact principalActiveAggregateError_norm_le_quartic hQ r chi
    v w N A k (by omega) V W hV hW (fun q => hv q.val) hw

/-- Every active/principal prefix retains the same quartic boundary budget. -/
theorem apCentered_prefix_norm_le {Q : ℕ} (hQ : 1 ≤ Q)
    (r : PositiveLevel Q)
    (chi : {χ : DirichletCharacter ℂ r.val // χ.IsPrimitive})
    (v w : ℕ → ℂ) (N A T : ℕ) (hend : A + T ≤ N + 1)
    (V W : ℝ) (hV : 0 ≤ V) (hW : 0 ≤ W)
    (hv : ∀ n : ℕ, ‖v n‖ ≤ V) (hw : ∀ n : ℕ, ‖w n‖ ≤ W) :
    ∀ k : ℕ, k ≤ T →
      ‖∑ i ∈ Finset.range k, apCentered hQ r chi v w N A i‖ ≤
        2 * (Q : ℝ) ^ 4 * V * W := by
  intro k hk
  rw [sum_apCentered_eq_error, activePrincipalChannelError_eq_aggregate]
  exact activePrincipalAggregateError_norm_le_quartic hQ r chi
    v w N A k (by omega) V W hV hW hv (fun q => hw q.val)

/-- Every active/active prefix retains the same quartic boundary budget. -/
theorem aaCentered_prefix_norm_le {Q : ℕ} (_hQ : 1 ≤ Q)
    (r : PositiveLevel Q)
    (chi : {χ : DirichletCharacter ℂ r.val // χ.IsPrimitive})
    (hInv : chi.val⁻¹ = chi.val)
    (v w : ℕ → ℂ) (N A T : ℕ) (hend : A + T ≤ N + 1)
    (V W : ℝ) (hV : 0 ≤ V) (hW : 0 ≤ W)
    (hv : ∀ n : ℕ, ‖v n‖ ≤ V) (hw : ∀ n : ℕ, ‖w n‖ ≤ W) :
    ∀ k : ℕ, k ≤ T →
      ‖∑ i ∈ Finset.range k, aaCentered r chi v w N A i‖ ≤
        2 * (Q : ℝ) ^ 4 * V * W := by
  intro k hk
  rw [sum_aaCentered_eq_error, activeActiveChannelError_eq_aggregate]
  exact activeActiveAggregateError_norm_le_quartic r chi hInv
    v w N A k (by omega) V W hV hW hv hw

end GoldbachCircleMethodPairwiseCenteredPrefixV18329
