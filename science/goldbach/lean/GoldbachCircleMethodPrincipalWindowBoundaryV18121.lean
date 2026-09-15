import GoldbachCircleMethodLogCutoffPresieveBindingV18120

set_option autoImplicit false
open scoped BigOperators Classical
open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodFiniteCompanionBindingV18118
open GoldbachCircleMethodFiniteWindowConvolutionV18119
open GoldbachCircleMethodLogCutoffPresieveBindingV18120

namespace GoldbachCircleMethodPrincipalWindowBoundaryV18121

def oneLevel {Q : ℕ} (hQ : 1 ≤ Q) : PositiveLevel Q :=
  ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, hQ⟩⟩

/-- The conductor-one primitive character is uniquely the principal character. -/
theorem primitive_level_one_unique
    (χ : {χ : DirichletCharacter ℂ 1 // χ.IsPrimitive}) :
    χ = ⟨1, DirichletCharacter.isPrimitive_one_level_one⟩ := by
  apply Subtype.ext
  exact (DirichletCharacter.eq_one_iff_conductor_eq_one (χ := χ.val)).mpr χ.property

theorem level_one_character_value (χ : DirichletCharacter ℂ 1) (N : ℕ) :
    χ (N : ZMod 1) = 1 := by
  have h : (N : ZMod 1) = 1 := Subsingleton.elim _ _
  rw [h, map_one]

noncomputable def windowCoefficient {Q : ℕ} (r : PositiveLevel Q) (N : ℕ)
    (w : ℕ → ℂ) (χ : {χ : DirichletCharacter ℂ r.val // χ.IsPrimitive}) : ℂ :=
  ((r.val : ℂ)/(r.val.totient : ℂ)) * χ.val (N : ZMod r.val) *
    finiteCompanion r N w

/-- Exact conductor-one coefficient sum, including its unique character. -/
theorem principal_coefficient_sum (Q N : ℕ) (hQ : 1 ≤ Q) (w : ℕ → ℂ) :
    (∑ r : PositiveLevel Q,
      ∑ χ : {χ : DirichletCharacter ℂ r.val // χ.IsPrimitive},
        if r.val = 1 then windowCoefficient r N w χ else 0) =
          finiteCompanion (oneLevel hQ) N w := by
  rw [Finset.sum_eq_single (oneLevel hQ)]
  · change (∑ χ : {χ : DirichletCharacter ℂ 1 // χ.IsPrimitive},
      if (1 : ℕ) = 1 then windowCoefficient (oneLevel hQ) N w χ else 0) = _
    rw [Finset.sum_eq_single
      (⟨1, DirichletCharacter.isPrimitive_one_level_one⟩ :
        {χ : DirichletCharacter ℂ 1 // χ.IsPrimitive})]
    · simp only [if_true]
      simp only [windowCoefficient, oneLevel, Nat.totient_one, Nat.cast_one,
        div_one, one_mul]
      erw [level_one_character_value (1 : DirichletCharacter ℂ 1) N]
      rw [one_mul]
    · intro χ _ hχ
      exact False.elim (hχ (primitive_level_one_unique χ))
    · simp only [Finset.mem_univ, not_true_eq_false, false_implies]
  · intro r _ hr
    have h : r.val ≠ 1 := by
      intro heq
      exact hr (Subtype.ext heq)
    simp only [h, if_false, Finset.sum_const_zero]
  · simp only [Finset.mem_univ, not_true_eq_false, false_implies]

/-- The actual finite character-window operator, with the V119 coefficient. -/
noncomputable def characterWindowOperator (Q N : ℕ) (H : ℝ)
    (J : Finset ℕ) (f w : ℕ → ℂ) : ℂ :=
  ∑ r : PositiveLevel Q,
    ∑ χ : {χ : DirichletCharacter ℂ r.val // χ.IsPrimitive},
      windowCoefficient r N w χ *
        ((2*(H : ℂ))⁻¹ *
          ∑ U ∈ centeredWindow J N H, f U * star (χ.val (U : ZMod r.val)))

/-- Centering is inside each genuine finite character-window sum. -/
noncomputable def centeredWindowError (Q N : ℕ) (H : ℝ)
    (J : Finset ℕ) (f w : ℕ → ℂ) : ℂ :=
  ∑ r : PositiveLevel Q,
    ∑ χ : {χ : DirichletCharacter ℂ r.val // χ.IsPrimitive},
      windowCoefficient r N w χ *
        ((2*(H : ℂ))⁻¹ *
          ∑ U ∈ centeredWindow J N H,
            (f U * star (χ.val (U : ZMod r.val)) - if r.val = 1 then 1 else 0))

/-- The discrete cardinality is retained in the principal contribution. -/
theorem character_window_principal_decomposition (Q N : ℕ) (hQ : 1 ≤ Q)
    (H : ℝ) (J : Finset ℕ) (f w : ℕ → ℂ) :
    characterWindowOperator Q N H J f w =
      finiteCompanion (oneLevel hQ) N w *
        (((centeredWindow J N H).card : ℂ)/(2*(H : ℂ))) +
          centeredWindowError Q N H J f w := by
  let k : ℂ := ((centeredWindow J N H).card : ℂ)
  let c : ℂ := (2*(H : ℂ))⁻¹
  have hs :
      characterWindowOperator Q N H J f w =
      centeredWindowError Q N H J f w +
        (∑ r : PositiveLevel Q,
          ∑ χ : {χ : DirichletCharacter ℂ r.val // χ.IsPrimitive},
            if r.val = 1 then windowCoefficient r N w χ else 0) * (c*k) := by
    unfold characterWindowOperator centeredWindowError
    rw [Finset.sum_mul]
    simp only [Finset.sum_mul, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro r _
    apply Finset.sum_congr rfl
    intro χ _
    by_cases hr : r.val = 1
    · simp only [hr, if_true, Finset.sum_sub_distrib, Finset.sum_const,
        nsmul_eq_mul, mul_one]
      dsimp only [k,c]
      ring
    · simp only [hr, if_false, sub_zero, zero_mul, add_zero]
  rw [hs, principal_coefficient_sum Q N hQ w]
  dsimp only [c,k]
  ring

/-- Separates the constant model and the exact non-normalized boundary term. -/
theorem character_window_model_boundary_decomposition (Q N : ℕ) (hQ : 1 ≤ Q)
    (H : ℝ) (J : Finset ℕ) (f w : ℕ → ℂ) :
    characterWindowOperator Q N H J f w =
      finiteCompanion (oneLevel hQ) N w + centeredWindowError Q N H J f w +
        finiteCompanion (oneLevel hQ) N w *
          (((centeredWindow J N H).card : ℂ)/(2*(H : ℂ)) - 1) := by
  rw [character_window_principal_decomposition Q N hQ H J f w]
  ring

/-- Binding back to the already checked actual presieved convolution. -/
theorem presieved_convolution_eq_character_window (B N : ℕ) (R : ℝ) (G : ℝ → ℝ) :
    normalizedWindowConvolution ⌊R^2⌋₊ N ((B : ℝ)/R^4)
      (blockCarrier B) (presievedInput ⌊R^2⌋₊ B) (logWeight R G) =
    characterWindowOperator ⌊R^2⌋₊ N ((B : ℝ)/R^4)
      (blockCarrier B) (presievedInput ⌊R^2⌋₊ B) (logWeight R G) := by
  exact presieved_log_window_expansion B N R G

/-- Exact linearity of the original finite indicator-kernel convolution. -/
theorem normalized_window_add (Q N : ℕ) (H : ℝ) (J : Finset ℕ)
    (f g w : ℕ → ℂ) :
    normalizedWindowConvolution Q N H J (fun U => f U + g U) w =
      normalizedWindowConvolution Q N H J f w +
        normalizedWindowConvolution Q N H J g w := by
  unfold normalizedWindowConvolution
  rw [← mul_add, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro U _
  by_cases h : |(N : ℝ) - (U : ℝ)| ≤ H
  · simp only [h, if_true, add_mul]
  · simp only [h, if_false, add_zero]

/-- The character-window operator is genuinely linear in the input. -/
theorem character_window_add (Q N : ℕ) (H : ℝ) (J : Finset ℕ)
    (f g w : ℕ → ℂ) :
    characterWindowOperator Q N H J (fun U => f U + g U) w =
      characterWindowOperator Q N H J f w +
        characterWindowOperator Q N H J g w := by
  simp only [characterWindowOperator, add_mul, Finset.sum_add_distrib, mul_add]

/-- The unpresieved discrepancy equals exactly the removed-input discrepancy.
It is not silently set to zero or assigned a support-preservation property. -/
theorem actual_removed_input_discrepancy (B N : ℕ) (R : ℝ) (G : ℝ → ℝ) :
    normalizedWindowConvolution ⌊R^2⌋₊ N ((B : ℝ)/R^4)
      (blockCarrier B) (blockInput B) (logWeight R G) -
    characterWindowOperator ⌊R^2⌋₊ N ((B : ℝ)/R^4)
      (blockCarrier B) (blockInput B) (logWeight R G) =
    normalizedWindowConvolution ⌊R^2⌋₊ N ((B : ℝ)/R^4)
      (blockCarrier B) (removedInput ⌊R^2⌋₊ B) (logWeight R G) -
    characterWindowOperator ⌊R^2⌋₊ N ((B : ℝ)/R^4)
      (blockCarrier B) (removedInput ⌊R^2⌋₊ B) (logWeight R G) := by
  have ha : blockInput B = fun U =>
      presievedInput ⌊R^2⌋₊ B U + removedInput ⌊R^2⌋₊ B U :=
    funext (block_input_decomposition ⌊R^2⌋₊ B)
  rw [ha, normalized_window_add, character_window_add,
    presieved_convolution_eq_character_window B N R G]
  ring

theorem log_cutoff_contains_one (R : ℝ) (hR : 1 < R) : 1 ≤ ⌊R^2⌋₊ := by
  apply (Nat.one_le_floor_iff (R^2)).mpr
  nlinarith

/-- Complete exact principal-centered window identity for the ACTUAL Lambda block.
This is an identity, not an estimate for E or for the removed-input residual. -/
theorem actual_lambda_window_decomposition (B N : ℕ) (R : ℝ) (hR : 1 < R)
    (G : ℝ → ℝ) :
    normalizedWindowConvolution ⌊R^2⌋₊ N ((B : ℝ)/R^4)
      (blockCarrier B) (blockInput B) (logWeight R G) =
      finiteCompanion (oneLevel (log_cutoff_contains_one R hR)) N (logWeight R G) +
      centeredWindowError ⌊R^2⌋₊ N ((B : ℝ)/R^4)
        (blockCarrier B) (blockInput B) (logWeight R G) +
      finiteCompanion (oneLevel (log_cutoff_contains_one R hR)) N (logWeight R G) *
        (((centeredWindow (blockCarrier B) N ((B : ℝ)/R^4)).card : ℂ) /
          (2 * (((B : ℝ)/R^4 : ℝ) : ℂ)) - 1) +
      (normalizedWindowConvolution ⌊R^2⌋₊ N ((B : ℝ)/R^4)
        (blockCarrier B) (removedInput ⌊R^2⌋₊ B) (logWeight R G) -
       characterWindowOperator ⌊R^2⌋₊ N ((B : ℝ)/R^4)
        (blockCarrier B) (removedInput ⌊R^2⌋₊ B) (logWeight R G)) := by
  have hd := actual_removed_input_discrepancy B N R G
  have hT := character_window_model_boundary_decomposition ⌊R^2⌋₊ N
    (log_cutoff_contains_one R hR) ((B : ℝ)/R^4) (blockCarrier B)
    (blockInput B) (logWeight R G)
  calc
    _ = (normalizedWindowConvolution ⌊R^2⌋₊ N ((B : ℝ)/R^4)
          (blockCarrier B) (blockInput B) (logWeight R G) -
        characterWindowOperator ⌊R^2⌋₊ N ((B : ℝ)/R^4)
          (blockCarrier B) (blockInput B) (logWeight R G)) +
        characterWindowOperator ⌊R^2⌋₊ N ((B : ℝ)/R^4)
          (blockCarrier B) (blockInput B) (logWeight R G) := by ring
    _ = _ := by rw [hd, hT]; ring


end GoldbachCircleMethodPrincipalWindowBoundaryV18121
