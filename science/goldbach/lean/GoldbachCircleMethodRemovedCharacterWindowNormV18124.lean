import GoldbachCircleMethodRemovedConvolutionNormV18123
import Mathlib.NumberTheory.DirichletCharacter.Bounds

set_option autoImplicit false
open scoped BigOperators Classical
open GoldbachCircleMethodActualOperatorErrorTransferV1861
open GoldbachCircleMethodFiniteResiduePrefixV1866
open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodFiniteCompanionBindingV18118
open GoldbachCircleMethodFiniteWindowConvolutionV18119
open GoldbachCircleMethodLogCutoffPresieveBindingV18120
open GoldbachCircleMethodPrincipalWindowBoundaryV18121
open GoldbachCircleMethodRemovedPrimePowerMassV18122
open GoldbachCircleMethodRemovedConvolutionNormV18123

namespace GoldbachCircleMethodRemovedCharacterWindowNormV18124

theorem primitive_character_card_le (q : ℕ) [NeZero q] :
    Fintype.card {χ : DirichletCharacter ℂ q // χ.IsPrimitive} ≤ q := by
  calc
    _ ≤ Fintype.card (DirichletCharacter ℂ q) := Fintype.card_subtype_le _
    _ = q.totient := by
      rw [← Nat.card_eq_fintype_card]
      exact DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q
    _ ≤ q := Nat.totient_le q

/-- A coarse norm estimate preserves the product cutoff and original weight. -/
theorem finite_companion_norm_le (Q N : ℕ) (r : PositiveLevel Q)
    (w : ℕ → ℂ) (M : ℝ) (hM : 0 ≤ M) (hw : ∀ n, ‖w n‖ ≤ M) :
    ‖finiteCompanion r N w‖ ≤ M*(Q : ℝ)^2 := by
  unfold finiteCompanion
  calc
    _ ≤ ∑ l : PositiveLevel Q, ‖if r.val*l.val ≤ Q ∧ Nat.Coprime r.val l.val
        then ((ArithmeticFunction.moebius l.val : ℤ) : ℂ) *
          unitCharacterSum l.val (N : ZMod l.val) / (l.val.totient : ℂ) *
            w (r.val*l.val) else 0‖ := norm_sum_le _ _
    _ ≤ ∑ _l : PositiveLevel Q, M*(Q : ℝ) := by
      apply Finset.sum_le_sum
      intro l _
      split_ifs with h
      · have heq :
            ((ArithmeticFunction.moebius l.val : ℤ) : ℂ) *
              unitCharacterSum l.val (N : ZMod l.val) / (l.val.totient : ℂ) =
            (((ArithmeticFunction.moebius l.val : ℤ) : ℂ)/(l.val.totient : ℂ)) *
              unitCharacterSum l.val (N : ZMod l.val) := by ring
        rw [heq, norm_mul, norm_mul]
        have ha := rational_amplitude_norm_le_one l.val
          (Nat.pos_of_ne_zero (NeZero.ne l.val))
        have hc := (unit_character_norm_le_level l.val (N : ZMod l.val)).trans
          (Nat.cast_le.mpr (Finset.mem_Icc.mp l.property).2)
        calc
          _ ≤ (1*(Q : ℝ))*M :=
            mul_le_mul (mul_le_mul ha hc (norm_nonneg _) zero_le_one)
              (hw _) (norm_nonneg _) (by positivity)
          _ = _ := by ring
      · simp only [norm_zero]
        positivity
    _ = _ := by
      rw [Finset.sum_const, nsmul_eq_mul]
      simp only [Finset.card_univ, positive_level_card]
      ring

theorem window_coefficient_norm_le (Q N : ℕ) (r : PositiveLevel Q)
    (w : ℕ → ℂ) (M : ℝ) (hM : 0 ≤ M) (hw : ∀ n, ‖w n‖ ≤ M)
    (χ : {χ : DirichletCharacter ℂ r.val // χ.IsPrimitive}) :
    ‖windowCoefficient r N w χ‖ ≤ M*(Q : ℝ)^3 := by
  have ht : (1 : ℝ) ≤ r.val.totient := by
    exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne r.val))
  have hr : ‖(r.val : ℂ)/(r.val.totient : ℂ)‖ ≤ (Q : ℝ) := by
    rw [norm_div, Complex.norm_natCast, Complex.norm_natCast]
    exact (div_le_self (Nat.cast_nonneg r.val) ht).trans
      (Nat.cast_le.mpr (Finset.mem_Icc.mp r.property).2)
  unfold windowCoefficient
  rw [norm_mul, norm_mul]
  calc
    _ ≤ ((Q : ℝ)*1)*(M*(Q : ℝ)^2) :=
      mul_le_mul (mul_le_mul hr (χ.val.norm_le_one _) (norm_nonneg _) (by positivity))
        (finite_companion_norm_le Q N r w M hM hw) (norm_nonneg _) (by positivity)
    _ = _ := by ring

theorem character_window_input_norm_le (q N : ℕ) (χ : DirichletCharacter ℂ q)
    (H : ℝ) (hH : 0 < H) (J : Finset ℕ) (f : ℕ → ℂ) :
    ‖(2*(H : ℂ))⁻¹ * ∑ U ∈ centeredWindow J N H,
      f U * star (χ (U : ZMod q))‖ ≤ (2*H)⁻¹ * ∑ U ∈ J, ‖f U‖ := by
  have hc : ‖(2*(H : ℂ))⁻¹‖ = (2*H)⁻¹ := by
    simp [norm_inv, Complex.norm_real, abs_of_pos hH]
  rw [norm_mul, hc]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  calc
    _ ≤ ∑ U ∈ centeredWindow J N H, ‖f U * star (χ (U : ZMod q))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ U ∈ centeredWindow J N H, ‖f U‖ := by
      apply Finset.sum_le_sum
      intro U _
      rw [norm_mul, norm_star]
      exact (mul_le_mul_of_nonneg_left (χ.norm_le_one _) (norm_nonneg _)).trans_eq
        (mul_one _)
    _ ≤ ∑ U ∈ J, ‖f U‖ :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun U _ _ => norm_nonneg (f U))

/-- No orthogonality or cancellation is claimed for the removed input. -/
theorem character_operator_norm_le_mass (Q N : ℕ) (H : ℝ) (hH : 0 < H)
    (J : Finset ℕ) (f w : ℕ → ℂ) (M : ℝ) (hM : 0 ≤ M)
    (hw : ∀ n, ‖w n‖ ≤ M) :
    ‖characterWindowOperator Q N H J f w‖ ≤
      M*(Q : ℝ)^5*((2*H)⁻¹ * ∑ U ∈ J, ‖f U‖) := by
  let A : ℝ := (2*H)⁻¹ * ∑ U ∈ J, ‖f U‖
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hi (r : PositiveLevel Q) :
      ‖∑ χ : {χ : DirichletCharacter ℂ r.val // χ.IsPrimitive},
        windowCoefficient r N w χ *
          ((2*(H : ℂ))⁻¹ * ∑ U ∈ centeredWindow J N H,
            f U * star (χ.val (U : ZMod r.val)))‖ ≤
        (Q : ℝ)*(M*(Q : ℝ)^3*A) := by
    calc
      _ ≤ ∑ χ : {χ : DirichletCharacter ℂ r.val // χ.IsPrimitive},
          ‖windowCoefficient r N w χ *
            ((2*(H : ℂ))⁻¹ * ∑ U ∈ centeredWindow J N H,
              f U * star (χ.val (U : ZMod r.val)))‖ := norm_sum_le _ _
      _ ≤ ∑ _χ : {χ : DirichletCharacter ℂ r.val // χ.IsPrimitive},
          M*(Q : ℝ)^3*A := by
        apply Finset.sum_le_sum
        intro χ _
        rw [norm_mul]
        exact mul_le_mul (window_coefficient_norm_le Q N r w M hM hw χ)
          (character_window_input_norm_le r.val N χ.val H hH J f)
          (norm_nonneg _) (by positivity)
      _ = (Fintype.card {χ : DirichletCharacter ℂ r.val // χ.IsPrimitive} : ℝ) *
          (M*(Q : ℝ)^3*A) := by
        rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
      _ ≤ _ := mul_le_mul_of_nonneg_right
          (Nat.cast_le.mpr ((primitive_character_card_le r.val).trans
            (Finset.mem_Icc.mp r.property).2)) (by positivity)
  unfold characterWindowOperator
  calc
    _ ≤ ∑ r : PositiveLevel Q, ‖∑ χ : {χ : DirichletCharacter ℂ r.val // χ.IsPrimitive},
          windowCoefficient r N w χ *
            ((2*(H : ℂ))⁻¹ * ∑ U ∈ centeredWindow J N H,
              f U * star (χ.val (U : ZMod r.val)))‖ := norm_sum_le _ _
    _ ≤ ∑ _r : PositiveLevel Q, (Q : ℝ)*(M*(Q : ℝ)^3*A) :=
      Finset.sum_le_sum (fun r _ => hi r)
    _ = _ := by
      rw [Finset.sum_const, nsmul_eq_mul]
      simp only [Finset.card_univ, positive_level_card]
      dsimp only [A]
      ring

/-- Explicit coarse T(g) cost on the same actual output block. -/
theorem removed_character_window_mass_le (B : ℕ) (hB : 2 ≤ B)
    (R : ℝ) (hR : 1 < R) (G : ℝ → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hG : ∀ x : ℝ, |G x| ≤ M) :
    (∑ N ∈ blockCarrier B,
      ‖characterWindowOperator ⌊R^2⌋₊ N ((B : ℝ)/R^4)
        (blockCarrier B) (removedInput ⌊R^2⌋₊ B) (logWeight R G)‖) ≤
      (M/2)*R^16*Real.log (B : ℝ) := by
  let Q : ℕ := ⌊R^2⌋₊
  let H : ℝ := (B : ℝ)/R^4
  let A : ℝ := M*(Q : ℝ)^5*(2*H)⁻¹*(Q : ℝ)*Real.log (B : ℝ)
  have hBpos : 0 < B := lt_of_lt_of_le (by decide : 0 < 2) hB
  have hRpos : 0 < R := lt_trans zero_lt_one hR
  have hH : 0 < H := actual_window_width_positive B hBpos R hR
  have hlogB : 0 ≤ Real.log (B : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (le_trans (by decide : 1 ≤ 2) hB))
  have hQ : (Q : ℝ) ≤ R^2 := Nat.floor_le (sq_nonneg R)
  have hw : ∀ n, ‖logWeight R G n‖ ≤ M := by
    intro n
    simpa only [logWeight, Complex.norm_real, Real.norm_eq_abs] using
      hG (Real.log (n : ℝ)/Real.log R)
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hp (N : ℕ) :
      ‖characterWindowOperator Q N H (blockCarrier B)
        (removedInput Q B) (logWeight R G)‖ ≤ A := by
    apply (character_operator_norm_le_mass Q N H hH (blockCarrier B)
      (removedInput Q B) (logWeight R G) M hM hw).trans
    dsimp only [A]
    have hm := removed_mass_le_Q_log_B Q B hB
    have hcoef : 0 ≤ M*(Q : ℝ)^5*(2*H)⁻¹ := by positivity
    have hh := mul_le_mul_of_nonneg_left hm hcoef
    simpa only [mul_assoc] using hh
  calc
    _ ≤ ∑ _N ∈ blockCarrier B, A := Finset.sum_le_sum (fun N _ => hp N)
    _ = ((blockCarrier B).card : ℝ)*A := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (B : ℝ)*A :=
      mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (block_carrier_card_le B)) hA
    _ = (M/2)*R^4*(Q : ℝ)^6*Real.log (B : ℝ) := by
      dsimp only [A,H]
      field_simp [ne_of_gt hRpos, ne_of_gt (Nat.cast_pos.mpr hBpos : (0 : ℝ) < B)]
    _ ≤ (M/2)*R^4*(R^2)^6*Real.log (B : ℝ) := by gcongr
    _ = _ := by ring

end GoldbachCircleMethodRemovedCharacterWindowNormV18124

