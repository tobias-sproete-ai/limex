import GoldbachCircleMethodPairwiseCenteredPrefixV18329

/-!
# Goldbach V1.8.330: variable four-channel Abel bound

The literal product of two spatially adjusted principal/active coefficients is
identified with a variable arithmetic mean plus four centered channels.  The
pairwise-prefix estimates and V1.8.328 then give a quartic error controlled by
total variation alone.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodVariableFourChannelAbelV18330

open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodFiniteCompanionBindingV18118
open GoldbachCircleMethodFourChannelAbelTransportV18328
open GoldbachCircleMethodFullFrozenPairwiseIntervalV18323
open GoldbachCircleMethodPairwiseCenteredPrefixV18329
open GoldbachCircleMethodPairwiseChannelBindingV18322
open GoldbachCircleMethodPrincipalWindowBoundaryV18121

/-- Literal variable-weight pair interval before spatial specialization. -/
noncomputable def variableFourChannelPairInterval {Q : ℕ} (hQ : 1 ≤ Q)
    (r : PositiveLevel Q)
    (chi : {χ : DirichletCharacter ℂ r.val // χ.IsPrimitive})
    (v w : ℕ → ℂ) (u z : ℕ → ℝ) (N A T : ℕ) : ℂ :=
  ∑ i ∈ Finset.range T,
    (finiteCompanion (oneLevel hQ) (N - (A + i)) v -
        (u i : ℂ) * windowCoefficient r (N - (A + i)) v chi) *
      (finiteCompanion (oneLevel hQ) (A + i) w -
        (z i : ℂ) * windowCoefficient r (A + i) w chi)

/-- The arithmetic mean follows the spatial weights point by point. -/
noncomputable def variableFourChannelMean {Q : ℕ} (hQ : 1 ≤ Q)
    (r : PositiveLevel Q)
    (chi : {χ : DirichletCharacter ℂ r.val // χ.IsPrimitive})
    (v w : ℕ → ℂ) (u z : ℕ → ℝ) (N T : ℕ) : ℂ :=
  ∑ i ∈ Finset.range T,
    (principalPrincipalChannelMean hQ v w N -
      (z i : ℂ) * principalActiveChannelMean hQ r chi v w N -
      (u i : ℂ) * activePrincipalChannelMean hQ r chi v w N +
      ((u i * z i : ℝ) : ℂ) * activeActiveChannelMean r chi v w N)

/-- Exact distributive identity exposing the four centered sequences. -/
theorem variableFourChannelPairInterval_sub_mean_eq_centered
    {Q : ℕ} (hQ : 1 ≤ Q)
    (r : PositiveLevel Q)
    (chi : {χ : DirichletCharacter ℂ r.val // χ.IsPrimitive})
    (v w : ℕ → ℂ) (u z : ℕ → ℝ) (N A T : ℕ) :
    variableFourChannelPairInterval hQ r chi v w u z N A T -
        variableFourChannelMean hQ r chi v w u z N T =
      ∑ i ∈ Finset.range T,
        (ppCentered hQ v w N A i - z i • paCentered hQ r chi v w N A i -
          u i • apCentered hQ r chi v w N A i +
          (u i * z i) • aaCentered r chi v w N A i) := by
  unfold variableFourChannelPairInterval variableFourChannelMean
    ppCentered paCentered apCentered aaCentered
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _hi
  simp only [Complex.real_smul]
  push_cast
  ring

/-- The actual variable arithmetic centering costs only total variation.
There is no factor proportional to the interval length times a pointwise
freezing error. -/
theorem variableFourChannelPairInterval_centered_norm_le
    {Q : ℕ} (hQ : 1 ≤ Q)
    (r : PositiveLevel Q)
    (chi : {χ : DirichletCharacter ℂ r.val // χ.IsPrimitive})
    (hInv : chi.val⁻¹ = chi.val)
    (v w : ℕ → ℂ) (u z : ℕ → ℝ) (N A T : ℕ)
    (hT : 1 ≤ T) (hend : A + T ≤ N + 1)
    (V W : ℝ) (hV : 0 ≤ V) (hW : 0 ≤ W)
    (hv : ∀ n : ℕ, ‖v n‖ ≤ V) (hw : ∀ n : ℕ, ‖w n‖ ≤ W)
    (U Z : ℝ)
    (hu : ∀ i : ℕ, i < T → |u i| ≤ 1)
    (hz : ∀ i : ℕ, i < T → |z i| ≤ 1)
    (hU : ∑ i ∈ Finset.range (T - 1), |u (i + 1) - u i| ≤ U)
    (hZ : ∑ i ∈ Finset.range (T - 1), |z (i + 1) - z i| ≤ Z) :
    ‖variableFourChannelPairInterval hQ r chi v w u z N A T -
        variableFourChannelMean hQ r chi v w u z N T‖ ≤
      (2 * (Q : ℝ) ^ 4 * V * W) * (4 + 2 * (U + Z)) := by
  rw [variableFourChannelPairInterval_sub_mean_eq_centered]
  apply four_channel_abel_norm_le
  · positivity
  · exact hT
  · exact ppCentered_prefix_norm_le hQ v w N A T hend V W hV hW hv hw
  · exact paCentered_prefix_norm_le hQ r chi v w N A T hend V W hV hW hv hw
  · exact apCentered_prefix_norm_le hQ r chi v w N A T hend V W hV hW hv hw
  · exact aaCentered_prefix_norm_le hQ r chi hInv v w N A T hend V W hV hW hv hw
  · exact hu
  · exact hz
  · exact hU
  · exact hZ

end GoldbachCircleMethodVariableFourChannelAbelV18330
