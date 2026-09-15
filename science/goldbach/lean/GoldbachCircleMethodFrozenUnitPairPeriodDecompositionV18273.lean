import GoldbachCircleMethodVariableWeightIntervalDiscrepancyV18272
import GoldbachCircleMethodActualCompanionIntervalTransferV18205

/-!
# Goldbach V1.8.273: frozen unit-pair period decomposition

The frozen interval of V1.8.272 is decomposed into complete conductor periods
plus a literal terminal segment.  The terminal segment is retained and bounded;
it is never dropped or declared positive.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodFrozenUnitPairPeriodDecompositionV18273

open GoldbachCircleMethodExceptionalWeightBoundaryV18128
open GoldbachCircleMethodActualUnitPairArithmeticV18194
open GoldbachCircleMethodActualCompanionIntervalTransferV18205
open GoldbachCircleMethodVariableWeightIntervalDiscrepancyV18272

/-- One frozen residue kernel, supported on the literal two-unit carrier. -/
noncomputable def frozenUnitPairKernel
    (r N A : ℕ) [NeZero r] (chi : DirichletCharacter ℂ r) (b : ℝ)
    (x : ZMod r) : ℂ :=
  if x ∈ unitPairResidues r (N : ℤ) then
    (1-(powerWeight b A : ℂ)*chi x) *
      (1-(powerWeight b (N-A) : ℂ)*chi ((N : ZMod r)-x))
  else 0

/-- The exact complete-period value on the literal unit-pair carrier. -/
noncomputable def frozenUnitPairPeriod
    (r N A : ℕ) [NeZero r] (chi : DirichletCharacter ℂ r) (b : ℝ) : ℂ :=
  ∑ x ∈ unitPairResidues r (N : ℤ),
    (1-(powerWeight b A : ℂ)*chi x) *
      (1-(powerWeight b (N-A) : ℂ)*chi ((N : ZMod r)-x))

/-- The literal incomplete terminal segment; its sign is not prescribed. -/
noncomputable def frozenUnitPairTerminal
    (r N A T : ℕ) [NeZero r] (chi : DirichletCharacter ℂ r) (b : ℝ) : ℂ :=
  ∑ i ∈ Finset.range (T % r),
    frozenUnitPairKernel r N A chi b ((A+i : ℕ) : ZMod r)

theorem complete_frozen_kernel_eq_period
    (r N A : ℕ) [NeZero r] (chi : DirichletCharacter ℂ r) (b : ℝ) :
    (∑ x : ZMod r, frozenUnitPairKernel r N A chi b x) =
      frozenUnitPairPeriod r N A chi b := by
  unfold frozenUnitPairKernel frozenUnitPairPeriod
  rw [← Finset.sum_filter]
  simp only [Finset.filter_mem_eq_inter, Finset.univ_inter]

/-- Exact quotient/remainder decomposition on the actual interval carrier. -/
theorem frozen_unit_pair_interval_period_decomposition
    (r N A T : ℕ) [NeZero r] (chi : DirichletCharacter ℂ r) (b : ℝ) :
    frozenUnitPairInterval r N A T chi b =
      (T/r : ℕ) * frozenUnitPairPeriod r N A chi b +
        frozenUnitPairTerminal r N A T chi b := by
  have h := residue_interval_decomposition
    (frozenUnitPairKernel r N A chi b) A T
  rw [complete_frozen_kernel_eq_period] at h
  simpa [frozenUnitPairInterval, frozenUnitPairKernel, frozenUnitPairTerminal] using h

theorem frozen_kernel_norm_le_four
    (r N A B : ℕ) [NeZero r] (chi : DirichletCharacter ℂ r) (b : ℝ)
    (hb : 0 ≤ b) (hA : A ∈ GoldbachCircleMethodLogCutoffPresieveBindingV18120.blockCarrier B)
    (hNA : N-A ∈ GoldbachCircleMethodLogCutoffPresieveBindingV18120.blockCarrier B)
    (x : ZMod r) :
    ‖frozenUnitPairKernel r N A chi b x‖ ≤ 4 := by
  have hwA := power_weight_abs_le_one B A b hb hA
  have hwNA := power_weight_abs_le_one B (N-A) b hb hNA
  have hfac (w : ℝ) (z : ℂ) (hw : |w| ≤ 1) (hz : ‖z‖ ≤ 1) :
      ‖1-(w : ℂ)*z‖ ≤ 2 := by
    calc
      _ ≤ ‖(1 : ℂ)‖ + ‖(w : ℂ)*z‖ := norm_sub_le _ _
      _ = 1 + |w| * ‖z‖ := by simp
      _ ≤ 2 := by
        have hm : |w| * ‖z‖ ≤ 1 * 1 :=
          mul_le_mul hw hz (norm_nonneg z) (by positivity)
        nlinarith
  unfold frozenUnitPairKernel
  split_ifs
  · rw [norm_mul]
    exact (mul_le_mul
      (hfac (powerWeight b A) (chi x) hwA (chi.norm_le_one x))
      (hfac (powerWeight b (N-A)) (chi ((N : ZMod r)-x)) hwNA
        (chi.norm_le_one ((N : ZMod r)-x)))
      (norm_nonneg _) (by positivity)).trans_eq (by norm_num)
  · simp

/-- The terminal segment has an explicit conductor-scale norm cost. -/
theorem frozen_unit_pair_terminal_norm_le
    (r N A T B : ℕ) [NeZero r] (chi : DirichletCharacter ℂ r) (b : ℝ)
    (hb : 0 ≤ b)
    (hA : A ∈ GoldbachCircleMethodLogCutoffPresieveBindingV18120.blockCarrier B)
    (hNA : N-A ∈ GoldbachCircleMethodLogCutoffPresieveBindingV18120.blockCarrier B) :
    ‖frozenUnitPairTerminal r N A T chi b‖ ≤ 4*(T % r : ℕ) := by
  unfold frozenUnitPairTerminal
  calc
    _ ≤ ∑ i ∈ Finset.range (T % r),
        ‖frozenUnitPairKernel r N A chi b ((A+i : ℕ) : ZMod r)‖ := norm_sum_le _ _
    _ ≤ ∑ _i ∈ Finset.range (T % r), (4 : ℝ) :=
      Finset.sum_le_sum (fun i _ => frozen_kernel_norm_le_four r N A B chi b hb hA hNA _)
    _ = 4*(T % r : ℕ) := by simp; ring

/-- Exact full-period specialization: when `r ∣ T`, no terminal survives. -/
theorem frozen_unit_pair_interval_eq_periods_of_dvd
    (r N A T : ℕ) [NeZero r] (chi : DirichletCharacter ℂ r) (b : ℝ)
    (hT : r ∣ T) :
    frozenUnitPairInterval r N A T chi b =
      (T/r : ℕ) * frozenUnitPairPeriod r N A chi b := by
  rw [frozen_unit_pair_interval_period_decomposition]
  simp [frozenUnitPairTerminal, Nat.mod_eq_zero_of_dvd hT]

end GoldbachCircleMethodFrozenUnitPairPeriodDecompositionV18273
