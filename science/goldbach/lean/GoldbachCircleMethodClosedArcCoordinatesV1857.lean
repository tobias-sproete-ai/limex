import GoldbachCircleMethodComplexArcModelBindingV1856
import Mathlib.Analysis.Normed.Group.AddCircle

/-! # V1.8.57: measure-correct local coordinates of the unchanged closed ball.
The Haar measure has mass one and the period is exactly one. Endpoints are
handled by the standard atom-free Icc/Ioc integral identity, not dropped informally.
-/
open MeasureTheory Set

namespace GoldbachCircleMethodClosedArcCoordinatesV1857

theorem integral_closedBall_eq_interval (f : UnitAddCircle → ℂ) (c t : ℝ)
    (ht0 : 0 ≤ t) (ht : t < 1/2) :
    (∫ x in Metric.closedBall (c : UnitAddCircle) t, f x ∂AddCircle.haarAddCircle) =
      ∫ β in (c-t)..(c+t), f (β : UnitAddCircle) := by
  have hs : Ioc (c-1/2) (c+1/2) ⊆ Metric.closedBall c (|(1 : ℝ)|/2) := by
    rw [Real.closedBall_eq_Icc]
    norm_num
    intro x hx
    exact ⟨hx.1.le, hx.2⟩
  have hsub : Icc (c-t) (c+t) ⊆ Ioc (c-1/2) (c+1/2) := by
    intro x hx
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hpre := AddCircle.coe_real_preimage_closedBall_inter_eq
    (p := (1 : ℝ)) (x := c) (ε := t) (Ioc (c-1/2) (c+1/2)) hs
  rw [if_pos (by simpa using ht), Real.closedBall_eq_Icc, inter_eq_left.mpr hsub] at hpre
  have hmeas : MeasurableSet
      (((↑) : ℝ → UnitAddCircle) ⁻¹' Metric.closedBall (c : UnitAddCircle) t) :=
    measurableSet_closedBall.preimage (AddCircle.continuous_mk' (1 : ℝ)).measurable
  rw [← integral_indicator measurableSet_closedBall, AddCircle.integral_haarAddCircle]
  simp only [inv_one, one_smul]
  rw [← AddCircle.integral_preimage (1 : ℝ) (c-1/2)]
  rw [show c-1/2+1 = c+1/2 by ring]
  simp_rw [← Set.indicator_comp_right]
  rw [integral_indicator hmeas, Measure.restrict_restrict hmeas, hpre,
    integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le (by linarith : c-t ≤ c+t)]
  rfl

theorem integral_closedBall_eq_centered_interval (f : UnitAddCircle → ℂ) (c t : ℝ)
    (ht0 : 0 ≤ t) (ht : t < 1/2) :
    (∫ x in Metric.closedBall (c : UnitAddCircle) t, f x ∂AddCircle.haarAddCircle) =
      ∫ β in -t..t, f ((c+β : ℝ) : UnitAddCircle) := by
  rw [integral_closedBall_eq_interval f c t ht0 ht]
  have h := intervalIntegral.integral_comp_add_left
    (f := fun β : ℝ => f (β : UnitAddCircle)) (a := -t) (b := t) c
  simpa only [sub_eq_add_neg, add_comm] using h.symm

end GoldbachCircleMethodClosedArcCoordinatesV1857
