import GoldbachCircleMethodActualRadicalCompanionBoundV18156
import Mathlib.NumberTheory.DirichletCharacter.Bounds

set_option autoImplicit false
open scoped BigOperators Classical ContDiff
open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodFiniteCompanionBindingV18118
open GoldbachCircleMethodFiniteWindowConvolutionV18119
open GoldbachCircleMethodLogCutoffPresieveBindingV18120
open GoldbachCircleMethodPrincipalWindowBoundaryV18121
open GoldbachCircleMethodBumpDecayRadicalEnvelopeV18155
open GoldbachCircleMethodActualRadicalCompanionBoundV18156
namespace GoldbachCircleMethodActualCharacterRadicalErrorV18157

theorem actual_coefficient_zero_off_coprime {Q : ℕ} (r : PositiveLevel Q)
    (N : ℕ) (w : ℕ → ℂ)
    (χ : {χ : DirichletCharacter ℂ r.val // χ.IsPrimitive})
    (hcop : ¬ r.val.Coprime N) :
    windowCoefficient r N w χ = 0 := by
  have hu : ¬ IsUnit (N : ZMod r.val) := by
    intro hu
    exact hcop ((ZMod.isUnit_iff_coprime N r.val).mp hu).symm
  unfold windowCoefficient
  rw [χ.val.map_nonunit hu,mul_zero,zero_mul]

theorem actual_coefficient_norm_le_indicator {Q : ℕ} (r : PositiveLevel Q)
    (N : ℕ) (w : ℕ → ℂ)
    (χ : {χ : DirichletCharacter ℂ r.val // χ.IsPrimitive}) :
    ‖windowCoefficient r N w χ‖ ≤
      if r.val.Coprime N then
        ((r.val : ℝ)/(r.val.totient : ℝ))*‖finiteCompanion r N w‖ else 0 := by
  by_cases hcop : r.val.Coprime N
  · rw [if_pos hcop]
    unfold windowCoefficient
    rw [norm_mul,norm_mul,norm_div,Complex.norm_natCast,Complex.norm_natCast]
    have hb := mul_le_mul_of_nonneg_left (χ.val.norm_le_one (N : ZMod r.val))
      (show 0 ≤ (r.val : ℝ)/(r.val.totient : ℝ) by positivity)
    exact mul_le_mul_of_nonneg_right (by simpa only [mul_one] using hb) (norm_nonneg _)
  · rw [if_neg hcop,actual_coefficient_zero_off_coprime r N w χ hcop,norm_zero]

/-- Uniform coefficient bound; primitive-character nonunits are handled by
their actual zero values, not by assuming all N coprime to every conductor. -/
theorem actual_character_coefficients_radical_bound {G : ℝ → ℝ}
    (hc : HasCompactSupport G) (hd : ContDiff ℝ ∞ G)
    (hG : ∀ t : ℝ, 2 < t → G t = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (R : ℝ) (_hR : 2 ≤ R)
      (r : PositiveLevel ⌊R^2⌋₊) (N : ℕ), 0 < N →
      ∀ χ : {χ : DirichletCharacter ℂ r.val // χ.IsPrimitive},
      ‖windowCoefficient r N (logWeight R G) χ‖ ≤ C*radicalMajorant R N := by
  obtain ⟨C,hC,hbound⟩ := actual_coprime_indicator_radical_bound hc hd hG
  refine ⟨C,hC,?_⟩
  intro R hR r N hN χ
  exact (actual_coefficient_norm_le_indicator r N (logWeight R G) χ).trans (hbound R hR r N hN)

/-- Actual finite fluctuations, with the principal subtraction inside
each centered character window. No distribution estimate is built in. -/
noncomputable def actualFluctuationMass (Q N : ℕ) (H : ℝ)
    (J : Finset ℕ) (f : ℕ → ℂ) : ℝ :=
  ∑ r : PositiveLevel Q,
    ∑ χ : {χ : DirichletCharacter ℂ r.val // χ.IsPrimitive},
      ‖(2*(H : ℂ))⁻¹ * ∑ U ∈ centeredWindow J N H,
        (f U*star (χ.val (U : ZMod r.val))-if r.val=1 then 1 else 0)‖

theorem actualFluctuationMass_nonneg (Q N : ℕ) (H : ℝ)
    (J : Finset ℕ) (f : ℕ → ℂ) : 0 ≤ actualFluctuationMass Q N H J f :=
  Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => norm_nonneg _))

theorem actual_centered_error_le_fluctuation_mass {Q N : ℕ} (H : ℝ)
    (J : Finset ℕ) (f w : ℕ → ℂ) {K : ℝ}
    (hcoef : ∀ (r : PositiveLevel Q)
      (χ : {χ : DirichletCharacter ℂ r.val // χ.IsPrimitive}),
      ‖windowCoefficient r N w χ‖ ≤ K) :
    ‖centeredWindowError Q N H J f w‖ ≤ K*actualFluctuationMass Q N H J f := by
  unfold centeredWindowError actualFluctuationMass
  calc
    _ ≤ ∑ r : PositiveLevel Q, ‖∑ χ : {χ : DirichletCharacter ℂ r.val // χ.IsPrimitive},
      windowCoefficient r N w χ*((2*(H : ℂ))⁻¹*∑ U ∈ centeredWindow J N H,
        (f U*star (χ.val (U : ZMod r.val))-if r.val=1 then 1 else 0))‖ := norm_sum_le _ _
    _ ≤ ∑ r : PositiveLevel Q, ∑ χ : {χ : DirichletCharacter ℂ r.val // χ.IsPrimitive},
      K*‖(2*(H : ℂ))⁻¹*∑ U ∈ centeredWindow J N H,
        (f U*star (χ.val (U : ZMod r.val))-if r.val=1 then 1 else 0)‖ := by
      apply Finset.sum_le_sum
      intro r _
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro χ _
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hcoef r χ) (norm_nonneg _)
    _ = _ := by simp only [Finset.mul_sum]

/-- Actual error bounded by the genuine finite fluctuation mass.
Smallness of that mass remains a separate analytic obligation. -/
theorem actual_centered_error_radical_bound {G : ℝ → ℝ}
    (hc : HasCompactSupport G) (hd : ContDiff ℝ ∞ G)
    (hG : ∀ t : ℝ, 2 < t → G t = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (R : ℝ) (_hR : 2 ≤ R)
      (N : ℕ), 0 < N → ∀ (H : ℝ) (J : Finset ℕ) (f : ℕ → ℂ),
      ‖centeredWindowError ⌊R^2⌋₊ N H J f (logWeight R G)‖ ≤
        C*radicalMajorant R N*actualFluctuationMass ⌊R^2⌋₊ N H J f := by
  obtain ⟨C,hC,hbound⟩ := actual_character_coefficients_radical_bound hc hd hG
  refine ⟨C,hC,?_⟩
  intro R hR N hN H J f
  exact actual_centered_error_le_fluctuation_mass H J f (logWeight R G)
    (fun r χ => hbound R hR r N hN χ)

end GoldbachCircleMethodActualCharacterRadicalErrorV18157
