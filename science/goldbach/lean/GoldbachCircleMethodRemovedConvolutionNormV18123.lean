import GoldbachCircleMethodRemovedPrimePowerMassV18122

set_option autoImplicit false
open scoped BigOperators Classical
open GoldbachCircleMethodFiniteResiduePrefixV1866
open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodFiniteWindowConvolutionV18119
open GoldbachCircleMethodLogCutoffPresieveBindingV18120
open GoldbachCircleMethodRemovedPrimePowerMassV18122

namespace GoldbachCircleMethodRemovedConvolutionNormV18123

/-- Coarse but unconditional finite Ramanujan norm bound. -/
theorem unit_character_norm_le_level (q : ℕ) [NeZero q] (a : ZMod q) :
    ‖unitCharacterSum q a‖ ≤ (q : ℝ) := by
  unfold unitCharacterSum
  calc
    _ ≤ ∑ r : ZMod q, ‖if IsUnit r then ZMod.stdAddChar (a*r) else 0‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _r : ZMod q, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro r _
      by_cases hr : IsUnit r
      · simp only [hr, if_true, standard_character_norm, le_refl]
      · simp only [hr, if_false, norm_zero, zero_le_one]
    _ = _ := by simp

theorem positive_level_card (Q : ℕ) : Fintype.card (PositiveLevel Q) = Q := by
  simp [PositiveLevel, Nat.card_Icc]

/-- No cancellation or denominator pruning is assumed. -/
theorem weighted_kernel_norm_le (Q N U : ℕ) (w : ℕ → ℂ) (M : ℝ) (hM : 0 ≤ M)
    (hw : ∀ q : PositiveLevel Q, ‖w q.val‖ ≤ M) :
    ‖∑ q : PositiveLevel Q, w q.val *
      unitCharacterSum q.val ((N : ZMod q.val)-(U : ZMod q.val))‖ ≤ M*(Q : ℝ)^2 := by
  calc
    _ ≤ ∑ q : PositiveLevel Q, ‖w q.val *
      unitCharacterSum q.val ((N : ZMod q.val)-(U : ZMod q.val))‖ := norm_sum_le _ _
    _ ≤ ∑ _q : PositiveLevel Q, M*(Q : ℝ) := by
      apply Finset.sum_le_sum
      intro q _
      rw [norm_mul]
      apply mul_le_mul (hw q)
        ((unit_character_norm_le_level q.val _).trans
          (Nat.cast_le.mpr (Finset.mem_Icc.mp q.property).2))
        (norm_nonneg _) hM
    _ = _ := by
      rw [Finset.sum_const, nsmul_eq_mul]
      simp only [Finset.card_univ, positive_level_card]
      ring

/-- Pointwise norm control retains the original 1/(2H) normalization. -/
theorem normalized_window_norm_le_mass (Q N : ℕ) (H : ℝ) (hH : 0 < H)
    (J : Finset ℕ) (f w : ℕ → ℂ) (M : ℝ) (hM : 0 ≤ M)
    (hw : ∀ q : PositiveLevel Q, ‖w q.val‖ ≤ M) :
    ‖normalizedWindowConvolution Q N H J f w‖ ≤
      (2*H)⁻¹ * (M*(Q : ℝ)^2) * (∑ U ∈ J, ‖f U‖) := by
  have hc : ‖(2*(H : ℂ))⁻¹‖ = (2*H)⁻¹ := by
    simp [norm_inv, Complex.norm_real, abs_of_pos hH]
  unfold normalizedWindowConvolution
  rw [norm_mul, hc, mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (le_of_lt (mul_pos zero_lt_two hH)))
  calc
    _ ≤ ∑ U ∈ J, ‖if |(N : ℝ)-(U : ℝ)| ≤ H then
        f U * ∑ q : PositiveLevel Q, w q.val *
          unitCharacterSum q.val ((N : ZMod q.val)-(U : ZMod q.val))
        else 0‖ := norm_sum_le _ _
    _ ≤ ∑ U ∈ J, ‖f U‖*(M*(Q : ℝ)^2) := by
      apply Finset.sum_le_sum
      intro U _
      by_cases h : |(N : ℝ)-(U : ℝ)| ≤ H
      · simp only [h, if_true, norm_mul]
        exact mul_le_mul_of_nonneg_left
          (weighted_kernel_norm_le Q N U w M hM hw) (norm_nonneg _)
      · simp only [h, if_false, norm_zero]
        positivity
    _ = _ := by rw [← Finset.sum_mul]; ring

theorem block_carrier_card_le (B : ℕ) : (blockCarrier B).card ≤ B := by
  simp only [blockCarrier, Nat.card_Ioc]
  exact Nat.sub_le B (B/2)

/-- Explicit coarse cost of C(g) on the actual output block.
Only the estimate is coarsened; the kernel, input and window are unchanged. -/
theorem removed_convolution_mass_le (B : ℕ) (hB : 2 ≤ B)
    (R : ℝ) (hR : 1 < R) (G : ℝ → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hG : ∀ x : ℝ, |G x| ≤ M) :
    (∑ N ∈ blockCarrier B,
      ‖normalizedWindowConvolution ⌊R^2⌋₊ N ((B : ℝ)/R^4)
        (blockCarrier B) (removedInput ⌊R^2⌋₊ B) (logWeight R G)‖) ≤
      (M/2)*R^10*Real.log (B : ℝ) := by
  let Q : ℕ := ⌊R^2⌋₊
  let H : ℝ := (B : ℝ)/R^4
  let A : ℝ := (2*H)⁻¹*(M*(Q : ℝ)^2)*(Q : ℝ)*Real.log (B : ℝ)
  have hBpos : 0 < B := lt_of_lt_of_le (by decide : 0 < 2) hB
  have hRpos : 0 < R := lt_trans zero_lt_one hR
  have hH : 0 < H := actual_window_width_positive B hBpos R hR
  have hlogB : 0 ≤ Real.log (B : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (le_trans (by decide : 1 ≤ 2) hB))
  have hQ : (Q : ℝ) ≤ R^2 := Nat.floor_le (sq_nonneg R)
  have hw : ∀ q : PositiveLevel Q, ‖logWeight R G q.val‖ ≤ M := by
    intro q
    simpa only [logWeight, Complex.norm_real, Real.norm_eq_abs] using
      hG (Real.log (q.val : ℝ)/Real.log R)
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hp (N : ℕ) :
      ‖normalizedWindowConvolution Q N H (blockCarrier B)
        (removedInput Q B) (logWeight R G)‖ ≤ A := by
    apply (normalized_window_norm_le_mass Q N H hH (blockCarrier B)
      (removedInput Q B) (logWeight R G) M hM hw).trans
    dsimp only [A]
    have hm := removed_mass_le_Q_log_B Q B hB
    have hcoef : 0 ≤ (2*H)⁻¹*(M*(Q : ℝ)^2) := by positivity
    have hh := mul_le_mul_of_nonneg_left hm hcoef
    simpa only [mul_assoc] using hh
  calc
    _ ≤ ∑ _N ∈ blockCarrier B, A := Finset.sum_le_sum (fun N _ => hp N)
    _ = ((blockCarrier B).card : ℝ)*A := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (B : ℝ)*A :=
      mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (block_carrier_card_le B)) hA
    _ = (M/2)*R^4*(Q : ℝ)^3*Real.log (B : ℝ) := by
      dsimp only [A,H]
      field_simp [ne_of_gt hRpos, ne_of_gt (Nat.cast_pos.mpr hBpos : (0 : ℝ) < B)]
    _ ≤ (M/2)*R^4*(R^2)^3*Real.log (B : ℝ) := by
      gcongr
    _ = _ := by ring

end GoldbachCircleMethodRemovedConvolutionNormV18123
