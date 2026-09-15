import GoldbachCircleMethodActualWindowInputEnergyV18469

/-!
# Goldbach V1.8.470: actual primitive-source normalization

The literal `1/(2H)` factor is pulled through the finite primitive-character
energy exactly.  A second theorem records the resulting quantitative window
bound conditional only on the still-separate fixed-modulus character-energy
estimate; no estimate is manufactured here.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodActualPrimitiveSourceNormalizationV18470

open GoldbachCircleMethodFiniteCarrierStarCharacterEnergyV18467
open GoldbachCircleMethodActualWindowInputEnergyV18469
open GoldbachCircleMethodLogCutoffPresieveBindingV18120

noncomputable def rawPrimitiveSourceEnergy
    (q B N : ℕ) (H : ℝ) : ℝ :=
  ∑ chi ∈ (Finset.univ.filter
      (fun chi : DirichletCharacter ℂ q => chi.IsPrimitive)),
    ‖(2 * (H : ℂ))⁻¹ *
      ∑ i : ↥(actualWindowCarrier B N H),
        blockInput B i.val * star (chi (i.val : ZMod q))‖ ^ 2

theorem rawPrimitiveSourceEnergy_eq
    (q B N : ℕ) (H : ℝ) :
    rawPrimitiveSourceEnergy q B N H =
      ‖(2 * (H : ℂ))⁻¹‖ ^ 2 *
        conjugateCharacterEnergy q (actualWindowCarrier B N H)
          (fun i => blockInput B i.val)
          (fun chi : DirichletCharacter ℂ q => chi.IsPrimitive) := by
  unfold rawPrimitiveSourceEnergy conjugateCharacterEnergy
  calc
    _ = ∑ chi ∈ (Finset.univ.filter
          (fun chi : DirichletCharacter ℂ q => chi.IsPrimitive)),
        ‖(2 * (H : ℂ))⁻¹‖ ^ 2 *
          ‖∑ i : ↥(actualWindowCarrier B N H),
            blockInput B i.val * star (chi (i.val : ZMod q))‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro chi _hchi
      rw [norm_mul, mul_pow]
    _ = _ := by
      rw [Finset.mul_sum]

theorem rawPrimitiveSourceEnergy_le_of_character_energy
    (q B N : ℕ) (H E : ℝ)
    (hchar : conjugateCharacterEnergy q (actualWindowCarrier B N H)
      (fun i => blockInput B i.val)
      (fun chi : DirichletCharacter ℂ q => chi.IsPrimitive) ≤ E) :
    rawPrimitiveSourceEnergy q B N H ≤
      ‖(2 * (H : ℂ))⁻¹‖ ^ 2 * E := by
  rw [rawPrimitiveSourceEnergy_eq]
  exact mul_le_mul_of_nonneg_left hchar (sq_nonneg _)

theorem rawPrimitiveSourceEnergy_le_window_budget
    (q B N : ℕ) (H : ℝ) (hB : 2 ≤ B) (hH : 0 ≤ H)
    (K : ℝ) (hK : 0 ≤ K)
    (hchar : conjugateCharacterEnergy q (actualWindowCarrier B N H)
      (fun i => blockInput B i.val)
      (fun chi : DirichletCharacter ℂ q => chi.IsPrimitive) ≤
        K * ∑ i : ↥(actualWindowCarrier B N H),
          ‖blockInput B i.val‖ ^ 2) :
    rawPrimitiveSourceEnergy q B N H ≤
      ‖(2 * (H : ℂ))⁻¹‖ ^ 2 *
        (K * ((2 * H + 1) * (Real.log (B : ℝ)) ^ 2)) := by
  rw [rawPrimitiveSourceEnergy_eq]
  apply mul_le_mul_of_nonneg_left
  · exact hchar.trans (mul_le_mul_of_nonneg_left
      (actual_window_blockInput_energy_le B N H hB hH) hK)
  · exact sq_nonneg _

end GoldbachCircleMethodActualPrimitiveSourceNormalizationV18470
