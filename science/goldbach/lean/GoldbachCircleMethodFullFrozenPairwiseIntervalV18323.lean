import GoldbachCircleMethodPairwiseChannelBindingV18322
import GoldbachCircleMethodCoupledCompanionRemainderBoundV18207

/-!
# Goldbach V1.8.323: full frozen model on an incomplete interval

The actual natural-input frozen coefficient is decomposed into its four
principal/active channels.  Each channel is then bounded with its own local
pairwise period.  No global common-LCM hypothesis is introduced.

This is a frozen scalar-adjustment result.  It does not yet transport the
spatially varying power weight of the canonical adjusted model.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodFullFrozenPairwiseIntervalV18323

open GoldbachCircleMethodActivePrincipalPairwisePeriodV18320
open GoldbachCircleMethodActualCompanionCompleteDiagonalV18204
open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodCoupledCompanionRemainderBoundV18207
open GoldbachCircleMethodFiniteCompanionBindingV18118
open GoldbachCircleMethodFiniteResiduePrefixV1866
open GoldbachCircleMethodPairwiseActiveAggregateErrorV18319
open GoldbachCircleMethodPairwiseChannelBindingV18322
open GoldbachCircleMethodPrincipalWindowBoundaryV18121
open GoldbachCircleMethodPrimitiveTwistedRamanujanSupportV18208

/-- Principal/principal diagonal written without a common ambient period. -/
noncomputable def principalPrincipalChannelMean {Q : ℕ} (hQ : 1 ≤ Q)
    (v w : ℕ → ℂ) (N : ℕ) : ℂ :=
  ∑ q : PositiveLevel Q,
    literalCoefficient (oneLevel hQ) q v *
      literalCoefficient (oneLevel hQ) q w *
      unitCharacterSum q.val ((N : ℕ) : ZMod q.val)

/-- Natural-input frozen coefficient `principal - t * active`. -/
noncomputable def naturalFrozenCoefficient {Q : ℕ} (hQ : 1 ≤ Q)
    (r : PositiveLevel Q)
    (chi : {χ : DirichletCharacter ℂ r.val // χ.IsPrimitive})
    (v : ℕ → ℂ) (t : ℂ) (n : ℕ) : ℂ :=
  finiteCompanion (oneLevel hQ) n v - t * windowCoefficient r n v chi

/-- The exact four-channel mean corresponding to two frozen coefficients. -/
noncomputable def fullFrozenPairwiseMean {Q : ℕ} (hQ : 1 ≤ Q)
    (r : PositiveLevel Q)
    (chi : {χ : DirichletCharacter ℂ r.val // χ.IsPrimitive})
    (v w : ℕ → ℂ) (t₁ t₂ : ℂ) (N : ℕ) : ℂ :=
  principalPrincipalChannelMean hQ v w N -
    t₂ * principalActiveChannelMean hQ r chi v w N -
    t₁ * activePrincipalChannelMean hQ r chi v w N +
    t₁ * t₂ * activeActiveChannelMean r chi v w N

noncomputable def principalPrincipalChannelError {Q : ℕ} (hQ : 1 ≤ Q)
    (v w : ℕ → ℂ) (N A T : ℕ) : ℂ :=
  (∑ i ∈ Finset.range T,
      finiteCompanion (oneLevel hQ) (N - (A + i)) v *
        finiteCompanion (oneLevel hQ) (A + i) w) -
    (T : ℂ) * principalPrincipalChannelMean hQ v w N

/-- Centered error of the full natural frozen model on `[A,A+T)`. -/
noncomputable def fullFrozenPairwiseError {Q : ℕ} (hQ : 1 ≤ Q)
    (r : PositiveLevel Q)
    (chi : {χ : DirichletCharacter ℂ r.val // χ.IsPrimitive})
    (v w : ℕ → ℂ) (t₁ t₂ : ℂ) (N A T : ℕ) : ℂ :=
  (∑ i ∈ Finset.range T,
      naturalFrozenCoefficient hQ r chi v t₁ (N - (A + i)) *
        naturalFrozenCoefficient hQ r chi w t₂ (A + i)) -
    (T : ℂ) * fullFrozenPairwiseMean hQ r chi v w t₁ t₂ N

/-- Exact finite four-channel expansion on the original incomplete interval. -/
theorem fullFrozenPairwiseError_eq_four_channels {Q : ℕ} (hQ : 1 ≤ Q)
    (r : PositiveLevel Q)
    (chi : {χ : DirichletCharacter ℂ r.val // χ.IsPrimitive})
    (v w : ℕ → ℂ) (t₁ t₂ : ℂ) (N A T : ℕ) :
    fullFrozenPairwiseError hQ r chi v w t₁ t₂ N A T =
      principalPrincipalChannelError hQ v w N A T -
      t₂ * principalActiveChannelError hQ r chi v w N A T -
      t₁ * activePrincipalChannelError hQ r chi v w N A T +
      t₁ * t₂ * activeActiveChannelError r chi v w N A T := by
  have hsum :
      (∑ i ∈ Finset.range T,
        naturalFrozenCoefficient hQ r chi v t₁ (N - (A + i)) *
          naturalFrozenCoefficient hQ r chi w t₂ (A + i)) =
      (∑ i ∈ Finset.range T,
        finiteCompanion (oneLevel hQ) (N - (A + i)) v *
          finiteCompanion (oneLevel hQ) (A + i) w) -
      t₂ * (∑ i ∈ Finset.range T,
        finiteCompanion (oneLevel hQ) (N - (A + i)) v *
          windowCoefficient r (A + i) w chi) -
      t₁ * (∑ i ∈ Finset.range T,
        windowCoefficient r (N - (A + i)) v chi *
          finiteCompanion (oneLevel hQ) (A + i) w) +
      t₁ * t₂ * (∑ i ∈ Finset.range T,
        windowCoefficient r (N - (A + i)) v chi *
          windowCoefficient r (A + i) w chi) := by
    simp only [naturalFrozenCoefficient, Finset.mul_sum,
      ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _hi
    ring
  unfold fullFrozenPairwiseError
  rw [hsum]
  unfold fullFrozenPairwiseMean principalPrincipalChannelError
    principalActiveChannelError activePrincipalChannelError
    activeActiveChannelError
  ring

/-- Four-term norm bookkeeping, isolated from the arithmetic channels. -/
theorem four_channel_norm_le (a b c d t₁ t₂ : ℂ) (B : ℝ)
    (ha : ‖a‖ ≤ B) (hb : ‖b‖ ≤ B) (hc : ‖c‖ ≤ B) (hd : ‖d‖ ≤ B) :
    ‖a - t₂ * b - t₁ * c + t₁ * t₂ * d‖ ≤
      B * (1 + ‖t₁‖) * (1 + ‖t₂‖) := by
  have htri :
      ‖a - t₂ * b - t₁ * c + t₁ * t₂ * d‖ ≤
        ‖a‖ + ‖t₂ * b‖ + ‖t₁ * c‖ + ‖t₁ * t₂ * d‖ := by
    calc
      _ ≤ ‖a - t₂ * b - t₁ * c‖ + ‖t₁ * t₂ * d‖ := norm_add_le _ _
      _ ≤ (‖a - t₂ * b‖ + ‖t₁ * c‖) + ‖t₁ * t₂ * d‖ := by
        gcongr
        exact norm_sub_le _ _
      _ ≤ ((‖a‖ + ‖t₂ * b‖) + ‖t₁ * c‖) + ‖t₁ * t₂ * d‖ := by
        gcongr
        exact norm_sub_le _ _
      _ = _ := by ring
  refine htri.trans ?_
  simp only [norm_mul]
  calc
    ‖a‖ + ‖t₂‖ * ‖b‖ + ‖t₁‖ * ‖c‖ + ‖t₁‖ * ‖t₂‖ * ‖d‖ ≤
        B + ‖t₂‖ * B + ‖t₁‖ * B + ‖t₁‖ * ‖t₂‖ * B := by
      gcongr
    _ = B * (1 + ‖t₁‖) * (1 + ‖t₂‖) := by ring

/-- Full incomplete-interval frozen-model bound.  The quartic pairwise cost
survives assembly of all four channels and no common period is used. -/
theorem fullFrozenPairwiseError_norm_le_quartic {Q : ℕ} (hQ : 1 ≤ Q)
    (r : PositiveLevel Q)
    (chi : {χ : DirichletCharacter ℂ r.val // χ.IsPrimitive})
    (hInv : chi.val⁻¹ = chi.val)
    (v w : ℕ → ℂ) (t₁ t₂ : ℂ) (N A T : ℕ)
    (hend : A + T ≤ N + 1)
    (V W : ℝ) (hV : 0 ≤ V) (hW : 0 ≤ W)
    (hv : ∀ n : ℕ, ‖v n‖ ≤ V)
    (hw : ∀ n : ℕ, ‖w n‖ ≤ W) :
    ‖fullFrozenPairwiseError hQ r chi v w t₁ t₂ N A T‖ ≤
      (2 * (Q : ℝ) ^ 4 * V * W) * (1 + ‖t₁‖) * (1 + ‖t₂‖) := by
  rw [fullFrozenPairwiseError_eq_four_channels]
  apply four_channel_norm_le
  · simpa [principalPrincipalChannelError, principalPrincipalChannelMean] using
      (actual_companion_interval_quartic_bound
        (oneLevel hQ) (oneLevel hQ) v w N A T hend V W hV hW
        (fun q _hq => by simpa [oneLevel] using hv q.val)
        (fun l _hl => by simpa [oneLevel] using hw l.val))
  · rw [principalActiveChannelError_eq_aggregate]
    exact principalActiveAggregateError_norm_le_quartic hQ r chi
      v w N A T hend V W hV hW (fun q => hv q.val) hw
  · rw [activePrincipalChannelError_eq_aggregate]
    exact activePrincipalAggregateError_norm_le_quartic hQ r chi
      v w N A T hend V W hV hW hv (fun q => hw q.val)
  · rw [activeActiveChannelError_eq_aggregate]
    exact activeActiveAggregateError_norm_le_quartic r chi hInv
      v w N A T hend V W hV hW hv hw

end GoldbachCircleMethodFullFrozenPairwiseIntervalV18323
