import GoldbachCircleMethodAdjustedSourceThreeTermDecompositionV18479

/-!
# Goldbach V1.8.480: principal and exceptional source energies

The two sparse correction terms in the literal adjusted source are bounded on
the actual centered window. The principal subtraction is supported only at
conductor one, while the exceptional power correction is supported at one
declared slot. These are finite source-energy facts; no global absorption or
Goldbach conclusion is claimed.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodPrincipalExceptionalSourceEnergyV18480

open GoldbachCircleMethodActiveExceptionalCenteringV18129
open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodFiniteWindowConvolutionV18119
open GoldbachCircleMethodLogCutoffPresieveBindingV18120
open GoldbachCircleMethodPrincipalWindowBoundaryV18121
open GoldbachCircleMethodExceptionalWeightBoundaryV18128
open GoldbachCircleMethodRemovedCharacterWindowNormV18124
open GoldbachCircleMethodActualWindowSourceNormalizationV18185
open GoldbachCircleMethodAdjustedSourceThreeTermDecompositionV18479

theorem inverse_normalization_norm_eq
    (H : ℝ) (hH : 0 < H) :
    ‖(2 * (H : ℂ))⁻¹‖ = (2 * H)⁻¹ := by
  simp [norm_inv, Complex.norm_real, abs_of_pos hH]

theorem normalized_centeredWindow_card_le_three_halves
    (J : Finset ℕ) (N : ℕ) (H : ℝ) (hH : 1 ≤ H) :
    ‖(2 * (H : ℂ))⁻¹‖ * ((centeredWindow J N H).card : ℝ) ≤ 3 / 2 := by
  have hHpos : 0 < H := lt_of_lt_of_le zero_lt_one hH
  have hcard := centeredWindow_card_le J N (show 0 ≤ H by linarith)
  rw [inverse_normalization_norm_eq H hHpos]
  apply (inv_mul_le_iff₀ (show 0 < 2 * H by positivity)).mpr
  linarith

theorem principalSlotSource_norm_le_three_halves
    (Q B N : ℕ) (H : ℝ) (hH : 1 ≤ H) (t : CharacterSlot Q) :
    ‖principalSlotSource Q B N H t‖ ≤ 3 / 2 := by
  by_cases ht : t.1.val = 1
  · unfold principalSlotSource
    simp only [ht, if_true, Finset.sum_const, nsmul_eq_mul]
    rw [norm_mul]
    calc
      ‖(2 * (H : ℂ))⁻¹‖ *
          ‖((centeredWindow (blockCarrier B) N H).card : ℂ) * -1‖ =
          ‖(2 * (H : ℂ))⁻¹‖ *
            ((centeredWindow (blockCarrier B) N H).card : ℝ) := by
        rw [norm_mul, Complex.norm_natCast]
        norm_num
      _ ≤ 3 / 2 :=
        normalized_centeredWindow_card_le_three_halves
          (blockCarrier B) N H hH
  · simpa [principalSlotSource, ht] using (show (0 : ℝ) ≤ 3 / 2 by positivity)

theorem principalSlotSource_eq_zero_of_level_ne_one
    (Q B N : ℕ) (H : ℝ) (t : CharacterSlot Q) (ht : t.1.val ≠ 1) :
    principalSlotSource Q B N H t = 0 := by
  simp [principalSlotSource, ht]

theorem principal_level_energy_le_indicator
    (Q B N : ℕ) (H : ℝ) (hH : 1 ≤ H) (q : PositiveLevel Q) :
    (∑ chi : {chi : DirichletCharacter ℂ q.val // chi.IsPrimitive},
        ‖principalSlotSource Q B N H ⟨q, chi⟩‖ ^ 2) ≤
      if q.val = 1 then (9 : ℝ) / 4 else 0 := by
  by_cases hq : q.val = 1
  · simp only [hq, if_true]
    calc
      (∑ chi : {chi : DirichletCharacter ℂ q.val // chi.IsPrimitive},
          ‖principalSlotSource Q B N H ⟨q, chi⟩‖ ^ 2) ≤
          ∑ _chi : {chi : DirichletCharacter ℂ q.val // chi.IsPrimitive},
            (9 : ℝ) / 4 := by
        apply Finset.sum_le_sum
        intro chi _hchi
        have hnorm := principalSlotSource_norm_le_three_halves
          Q B N H hH (⟨q, chi⟩ : CharacterSlot Q)
        nlinarith [norm_nonneg (principalSlotSource Q B N H
          (⟨q, chi⟩ : CharacterSlot Q))]
      _ = (Fintype.card
          {chi : DirichletCharacter ℂ q.val // chi.IsPrimitive} : ℝ) *
            ((9 : ℝ) / 4) := by
        rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
      _ ≤ (1 : ℝ) * ((9 : ℝ) / 4) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact_mod_cast (primitive_character_card_le q.val).trans_eq hq
      _ = (9 : ℝ) / 4 := by ring
  · simp only [hq, if_false]
    calc
      (∑ chi : {chi : DirichletCharacter ℂ q.val // chi.IsPrimitive},
          ‖principalSlotSource Q B N H ⟨q, chi⟩‖ ^ 2) = 0 := by
        apply Finset.sum_eq_zero
        intro chi _hchi
        rw [principalSlotSource_eq_zero_of_level_ne_one Q B N H
          (⟨q, chi⟩ : CharacterSlot Q) hq]
        norm_num
      _ ≤ 0 := le_rfl

theorem principal_indicator_level_sum_le
    (Q : ℕ) :
    (∑ q : PositiveLevel Q, if q.val = 1 then (9 : ℝ) / 4 else 0) ≤
      (9 : ℝ) / 4 := by
  by_cases hQ : 1 ≤ Q
  · rw [Finset.sum_eq_single (oneLevel hQ)]
    · simp [oneLevel]
    · intro q _hq hne
      have hq : q.val ≠ 1 := by
        intro hq1
        apply hne
        exact Subtype.ext hq1
      simp [hq]
    · simp
  · have hzero : ∀ q : PositiveLevel Q, q.val ≠ 1 := by
      intro q hq
      have hqQ := (Finset.mem_Icc.mp q.property).2
      omega
    simpa [hzero] using (show (0 : ℝ) ≤ 9 / 4 by positivity)

/-- The principal subtraction occupies only conductor one and costs at most
`9/4` in normalized source energy. -/
theorem principalSourceEnergy_le_nine_fourths
    (Q B N : ℕ) (H : ℝ) (hH : 1 ≤ H) :
    principalSourceEnergy Q B N H ≤ (9 : ℝ) / 4 := by
  unfold principalSourceEnergy
  rw [Fintype.sum_sigma]
  exact (Finset.sum_le_sum fun q _hq =>
    principal_level_energy_le_indicator Q B N H hH q).trans
      (principal_indicator_level_sum_le Q)

theorem exceptionalPowerSlotSource_norm_le_three_halves
    (Q B N : ℕ) (H b : ℝ) (hH : 1 ≤ H) (hb : 0 ≤ b)
    (e t : CharacterSlot Q) :
    ‖exceptionalPowerSlotSource Q B N H b e t‖ ≤ 3 / 2 := by
  unfold exceptionalPowerSlotSource
  rw [norm_mul]
  calc
    ‖(2 * (H : ℂ))⁻¹‖ *
        ‖∑ U ∈ centeredWindow (blockCarrier B) N H,
          if t = e then (powerWeight b U : ℂ) else 0‖ ≤
        ‖(2 * (H : ℂ))⁻¹‖ *
          ∑ U ∈ centeredWindow (blockCarrier B) N H,
            ‖if t = e then (powerWeight b U : ℂ) else 0‖ := by
      gcongr
      exact norm_sum_le _ _
    _ ≤ ‖(2 * (H : ℂ))⁻¹‖ *
        ((centeredWindow (blockCarrier B) N H).card : ℝ) := by
      gcongr
      calc
        (∑ U ∈ centeredWindow (blockCarrier B) N H,
            ‖if t = e then (powerWeight b U : ℂ) else 0‖) ≤
            ∑ _U ∈ centeredWindow (blockCarrier B) N H, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro U hU
          split_ifs
          · rw [Complex.norm_real, Real.norm_eq_abs]
            exact power_weight_abs_le_one B U b hb
              (Finset.filter_subset _ _ hU)
          · norm_num
        _ = ((centeredWindow (blockCarrier B) N H).card : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul]
          ring
    _ ≤ 3 / 2 :=
      normalized_centeredWindow_card_le_three_halves
        (blockCarrier B) N H hH

theorem exceptionalPowerSlotSource_eq_zero_of_ne
    (Q B N : ℕ) (H b : ℝ) (e t : CharacterSlot Q) (ht : t ≠ e) :
    exceptionalPowerSlotSource Q B N H b e t = 0 := by
  simp [exceptionalPowerSlotSource, ht]

/-- The exceptional correction occupies exactly one declared character slot
and costs at most `9/4` in normalized source energy. -/
theorem exceptionalPowerSourceEnergy_le_nine_fourths
    (Q B N : ℕ) (H b : ℝ) (hH : 1 ≤ H) (hb : 0 ≤ b)
    (e : CharacterSlot Q) :
    exceptionalPowerSourceEnergy Q B N H b e ≤ (9 : ℝ) / 4 := by
  unfold exceptionalPowerSourceEnergy
  rw [Finset.sum_eq_single e]
  · have hnorm := exceptionalPowerSlotSource_norm_le_three_halves
      Q B N H b hH hb e e
    nlinarith [norm_nonneg (exceptionalPowerSlotSource Q B N H b e e)]
  · intro t _ht hte
    rw [exceptionalPowerSlotSource_eq_zero_of_ne Q B N H b e t hte]
    norm_num
  · simp

end GoldbachCircleMethodPrincipalExceptionalSourceEnergyV18480
