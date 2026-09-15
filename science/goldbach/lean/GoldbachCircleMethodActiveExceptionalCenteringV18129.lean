import GoldbachCircleMethodExceptionalWeightBoundaryV18128

set_option autoImplicit false
open scoped BigOperators Classical
open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodFiniteCompanionBindingV18118
open GoldbachCircleMethodFiniteWindowConvolutionV18119
open GoldbachCircleMethodLogCutoffPresieveBindingV18120
open GoldbachCircleMethodPrincipalWindowBoundaryV18121
open GoldbachCircleMethodActualCenteredResidualAssemblyV18127
open GoldbachCircleMethodExceptionalWeightBoundaryV18128

namespace GoldbachCircleMethodActiveExceptionalCenteringV18129

/-- Merely packages the two existing finite summation indices. -/
abbrev CharacterSlot (Q : ℕ) :=
  Σ r : PositiveLevel Q, {χ : DirichletCharacter ℂ r.val // χ.IsPrimitive}

/-- The correction is inserted inside the original character-window sum. -/
noncomputable def adjustedCenteredError (Q B N : ℕ) (H b : ℝ)
    (f w : ℕ → ℂ) (e : CharacterSlot Q) : ℂ :=
  ∑ t : CharacterSlot Q, windowCoefficient t.1 N w t.2 *
    ((2*(H : ℂ))⁻¹ * ∑ U ∈ centeredWindow (blockCarrier B) N H,
      ((f U * star (t.2.val (U : ZMod t.1.val)) - if t.1.val = 1 then 1 else 0) +
        if t = e then (powerWeight b U : ℂ) else 0))

theorem adjusted_centered_error_identity (Q B N : ℕ) (H b : ℝ)
    (f w : ℕ → ℂ) (e : CharacterSlot Q) :
    adjustedCenteredError Q B N H b f w e =
      centeredWindowError Q N H (blockCarrier B) f w +
      windowCoefficient e.1 N w e.2 * (normalizedPowerWindow B N H b : ℂ) := by
  have hbase :
      (∑ t : CharacterSlot Q, windowCoefficient t.1 N w t.2 *
        ((2*(H : ℂ))⁻¹ * ∑ U ∈ centeredWindow (blockCarrier B) N H,
          (f U * star (t.2.val (U : ZMod t.1.val)) - if t.1.val = 1 then 1 else 0))) =
        centeredWindowError Q N H (blockCarrier B) f w := by
    rw [Fintype.sum_sigma]
    rfl
  have hcorr :
      (∑ t : CharacterSlot Q, windowCoefficient t.1 N w t.2 *
        ((2*(H : ℂ))⁻¹ * ∑ U ∈ centeredWindow (blockCarrier B) N H,
          if t = e then (powerWeight b U : ℂ) else 0)) =
        windowCoefficient e.1 N w e.2 * (normalizedPowerWindow B N H b : ℂ) := by
    rw [Finset.sum_eq_single e]
    · simp only [if_true]
      simp [normalizedPowerWindow]
    · intro t _ ht
      simp only [ht, if_false, Finset.sum_const_zero, mul_zero]
    · simp only [Finset.mem_univ, not_true_eq_false, false_implies]
  unfold adjustedCenteredError
  simp only [Finset.sum_add_distrib, mul_add]
  rw [hbase, hcorr]

noncomputable def adjustedModel (Q N : ℕ) (hQ : 1 ≤ Q) (b : ℝ)
    (w : ℕ → ℂ) (e : CharacterSlot Q) : ℂ :=
  finiteCompanion (oneLevel hQ) N w -
    windowCoefficient e.1 N w e.2 * (powerWeight b N : ℂ)

/-- Exact finite active-case decomposition. The character is not assumed exceptional. -/
theorem active_character_window_identity (Q B N : ℕ) (hQ : 1 ≤ Q) (H b : ℝ)
    (f w : ℕ → ℂ) (e : CharacterSlot Q) :
    characterWindowOperator Q N H (blockCarrier B) f w =
      adjustedModel Q N hQ b w e +
      adjustedCenteredError Q B N H b f w e +
      GoldbachCircleMethodExactPrincipalBoundaryCostV18126.principalBoundary Q B N hQ H w +
      exceptionalBoundary Q B N e.1 e.2 H b w := by
  rw [adjusted_centered_error_identity, character_window_model_boundary_decomposition
    Q N hQ H (blockCarrier B) f w]
  unfold adjustedModel GoldbachCircleMethodExactPrincipalBoundaryCostV18126.principalBoundary
    exceptionalBoundary
  push_cast
  ring

/-- Defined using the actual input, model and adjusted centered operator. -/
noncomputable def activeCenteredResidual (B N : ℕ) (R : ℝ) (hR : 1 < R)
    (b : ℝ) (G : ℝ → ℝ) (e : CharacterSlot ⌊R^2⌋₊) : ℂ :=
  normalizedWindowConvolution ⌊R^2⌋₊ N ((B : ℝ)/R^4)
    (blockCarrier B) (blockInput B) (logWeight R G) -
  adjustedModel ⌊R^2⌋₊ N (log_cutoff_contains_one R hR) b (logWeight R G) e -
  adjustedCenteredError ⌊R^2⌋₊ B N ((B : ℝ)/R^4) b
    (blockInput B) (logWeight R G) e

theorem active_centered_residual_eq (B N : ℕ) (R : ℝ) (hR : 1 < R)
    (b : ℝ) (G : ℝ → ℝ) (e : CharacterSlot ⌊R^2⌋₊) :
    activeCenteredResidual B N R hR b G e =
      actualCenteredResidual B N R hR G +
      exceptionalBoundary ⌊R^2⌋₊ B N e.1 e.2 ((B : ℝ)/R^4) b (logWeight R G) := by
  unfold activeCenteredResidual
  rw [adjusted_centered_error_identity]
  unfold adjustedModel actualCenteredResidual exceptionalBoundary
  push_cast
  ring

theorem active_centered_residual_mass_le (B : ℕ) (hB : 2 ≤ B)
    (R : ℝ) (hR : 1 < R) (b : ℝ) (hb : 0 ≤ b) (hb1 : b ≤ 1)
    (G : ℝ → ℝ) (M : ℝ) (hM : 0 ≤ M) (hG : ∀ x : ℝ, |G x| ≤ M)
    (hupper : R ≤ (B : ℝ)^((1 : ℝ)/10000))
    (e : CharacterSlot ⌊R^2⌋₊) :
    (∑ N ∈ blockCarrier B, ‖activeCenteredResidual B N R hR b G e‖) ≤
      10*M*(B : ℝ)/R := by
  calc
    _ ≤ ∑ N ∈ blockCarrier B,
        (‖actualCenteredResidual B N R hR G‖+
          ‖exceptionalBoundary ⌊R^2⌋₊ B N e.1 e.2 ((B : ℝ)/R^4) b (logWeight R G)‖) := by
      apply Finset.sum_le_sum
      intro N _
      rw [active_centered_residual_eq]
      exact norm_add_le _ _
    _ = _ + _ := Finset.sum_add_distrib
    _ ≤ (9/2)*M*(B : ℝ)/R + (11/2)*M*(B : ℝ)/R :=
      add_le_add (actual_centered_residual_mass_le B hB R hR G M hM hG hupper)
        (actual_exceptional_boundary_mass_le_existing_range B hB R hR e.1 e.2 b hb hb1
          G M hM hG hupper)
    _ = _ := by ring

noncomputable def activeCenteredResidualFourier (B : ℕ) (R : ℝ) (hR : 1 < R)
    (b : ℝ) (G : ℝ → ℝ) (e : CharacterSlot ⌊R^2⌋₊) (x : UnitAddCircle) : ℂ :=
  ∑ N ∈ blockCarrier B, activeCenteredResidual B N R hR b G e * fourier (N : ℤ) x

theorem active_residual_fourier_norm_le_mass (B : ℕ) (R : ℝ) (hR : 1 < R)
    (b : ℝ) (G : ℝ → ℝ) (e : CharacterSlot ⌊R^2⌋₊) (x : UnitAddCircle) :
    ‖activeCenteredResidualFourier B R hR b G e x‖ ≤
      ∑ N ∈ blockCarrier B, ‖activeCenteredResidual B N R hR b G e‖ := by
  unfold activeCenteredResidualFourier
  calc
    _ ≤ ∑ N ∈ blockCarrier B,
        ‖activeCenteredResidual B N R hR b G e * fourier (N : ℤ) x‖ := norm_sum_le _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro N _
      simp [fourier_apply, Circle.norm_coe]

theorem active_residual_fourier_bound (B : ℕ) (hB : 2 ≤ B)
    (R : ℝ) (hR : 1 < R) (b : ℝ) (hb : 0 ≤ b) (hb1 : b ≤ 1)
    (G : ℝ → ℝ) (M : ℝ) (hM : 0 ≤ M) (hG : ∀ x : ℝ, |G x| ≤ M)
    (hupper : R ≤ (B : ℝ)^((1 : ℝ)/10000))
    (e : CharacterSlot ⌊R^2⌋₊) (x : UnitAddCircle) :
    ‖activeCenteredResidualFourier B R hR b G e x‖ ≤ 10*M*(B : ℝ)/R :=
  (active_residual_fourier_norm_le_mass B R hR b G e x).trans
    (active_centered_residual_mass_le B hB R hR b hb hb1 G M hM hG hupper e)

theorem active_residual_fourier_fits_target_budget (B : ℕ) (hB : 2 ≤ B)
    (R : ℝ) (hR : 1 < R) (b : ℝ) (hb : 0 ≤ b) (hb1 : b ≤ 1)
    (G : ℝ → ℝ) (M : ℝ) (hM : 0 ≤ M) (hG : ∀ x : ℝ, |G x| ≤ M)
    (hupper : R ≤ (B : ℝ)^((1 : ℝ)/10000))
    (e : CharacterSlot ⌊R^2⌋₊) (x : UnitAddCircle) :
    ‖activeCenteredResidualFourier B R hR b G e x‖ ≤ 10*M*(B : ℝ)*R^(-(1 : ℝ)/3) := by
  apply (active_residual_fourier_bound B hB R hR b hb hb1 G M hM hG hupper e x).trans
  rw [div_eq_mul_inv, ← Real.rpow_neg_one]
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hR.le (by norm_num)) (by positivity)

end GoldbachCircleMethodActiveExceptionalCenteringV18129

