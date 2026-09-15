import GoldbachCircleMethodBoundedUnitResidueInterfaceV18468
import GoldbachCircleMethodActualWindowSourceNormalizationV18185
import GoldbachCircleMethodActualOutputTailBoundV18132

/-!
# Goldbach V1.8.469: actual centered-window input energy

The abstract finite carrier is now instantiated by the literal centered window
inside the dyadic block.  Its elements lie below `B+1`, and the von Mangoldt
input energy is bounded only with the already verified pointwise logarithmic
majorant and the exact window-cardinality estimate.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodActualWindowInputEnergyV18469

open GoldbachCircleMethodFiniteWindowConvolutionV18119
open GoldbachCircleMethodLogCutoffPresieveBindingV18120
open GoldbachCircleMethodActualWindowSourceNormalizationV18185
open GoldbachCircleMethodActualOutputTailBoundV18132

noncomputable def actualWindowCarrier (B N : ℕ) (H : ℝ) : Finset ℕ :=
  centeredWindow (blockCarrier B) N H

theorem actualWindowCarrier_mem_lt_succ
    (B N U : ℕ) (H : ℝ) (hU : U ∈ actualWindowCarrier B N H) :
    U < B + 1 := by
  have hblock : U ∈ blockCarrier B :=
    (mem_centeredWindow (blockCarrier B) N U H).mp hU |>.1
  exact Nat.lt_succ_of_le ((mem_blockCarrier B U).mp hblock).2

theorem actual_window_blockInput_energy_le_card
    (B N : ℕ) (H : ℝ) (hB : 2 ≤ B) :
    (∑ i : ↥(actualWindowCarrier B N H), ‖blockInput B i.val‖ ^ 2) ≤
      ((actualWindowCarrier B N H).card : ℝ) * (Real.log (B : ℝ)) ^ 2 := by
  have hlog : 0 ≤ Real.log (B : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ B by omega))
  calc
    _ ≤ ∑ _i : ↥(actualWindowCarrier B N H), (Real.log (B : ℝ)) ^ 2 := by
      apply Finset.sum_le_sum
      intro i _hi
      have hiWindow : i.val ∈ actualWindowCarrier B N H := i.property
      have hiBlock : i.val ∈ blockCarrier B :=
        (mem_centeredWindow (blockCarrier B) N i.val H).mp hiWindow |>.1
      have hn := block_input_norm_le_log B i.val hiBlock
      nlinarith [norm_nonneg (blockInput B i.val)]
    _ = _ := by
      rw [Finset.sum_const, nsmul_eq_mul]
      simp

theorem actual_window_blockInput_energy_le
    (B N : ℕ) (H : ℝ) (hB : 2 ≤ B) (hH : 0 ≤ H) :
    (∑ i : ↥(actualWindowCarrier B N H), ‖blockInput B i.val‖ ^ 2) ≤
      (2 * H + 1) * (Real.log (B : ℝ)) ^ 2 := by
  have hcard := centeredWindow_card_le (blockCarrier B) N hH
  unfold actualWindowCarrier
  apply (actual_window_blockInput_energy_le_card B N H hB).trans
  exact mul_le_mul_of_nonneg_right hcard (sq_nonneg (Real.log (B : ℝ)))

end GoldbachCircleMethodActualWindowInputEnergyV18469
