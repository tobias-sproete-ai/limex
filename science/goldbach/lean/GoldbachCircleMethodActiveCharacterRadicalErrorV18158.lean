import GoldbachCircleMethodActualCharacterRadicalErrorV18157
import GoldbachCircleMethodActiveExceptionalCenteringV18129

set_option autoImplicit false
open scoped BigOperators Classical ContDiff
open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodFiniteWindowConvolutionV18119
open GoldbachCircleMethodLogCutoffPresieveBindingV18120
open GoldbachCircleMethodPrincipalWindowBoundaryV18121
open GoldbachCircleMethodExceptionalWeightBoundaryV18128
open GoldbachCircleMethodActiveExceptionalCenteringV18129
open GoldbachCircleMethodBumpDecayRadicalEnvelopeV18155
open GoldbachCircleMethodActualCharacterRadicalErrorV18157
namespace GoldbachCircleMethodActiveCharacterRadicalErrorV18158

/-- Actual adjusted window, including the same one-slot power correction. -/
noncomputable def activeFluctuationMass (Q B N : ℕ) (H b : ℝ)
    (f : ℕ → ℂ) (e : CharacterSlot Q) : ℝ :=
  ∑ t : CharacterSlot Q,
    ‖(2*(H : ℂ))⁻¹ * ∑ U ∈ centeredWindow (blockCarrier B) N H,
      ((f U*star (t.2.val (U : ZMod t.1.val))-if t.1.val=1 then 1 else 0)+
        if t=e then (powerWeight b U : ℂ) else 0)‖

theorem activeFluctuationMass_nonneg (Q B N : ℕ) (H b : ℝ)
    (f : ℕ → ℂ) (e : CharacterSlot Q) : 0 ≤ activeFluctuationMass Q B N H b f e :=
  Finset.sum_nonneg (fun _ _ => norm_nonneg _)

theorem actual_adjusted_error_le_active_mass (Q B N : ℕ) (H b : ℝ)
    (f w : ℕ → ℂ) (e : CharacterSlot Q) {K : ℝ}
    (hcoef : ∀ (r : PositiveLevel Q)
      (χ : {χ : DirichletCharacter ℂ r.val // χ.IsPrimitive}),
      ‖windowCoefficient r N w χ‖ ≤ K) :
    ‖adjustedCenteredError Q B N H b f w e‖ ≤
      K*activeFluctuationMass Q B N H b f e := by
  unfold adjustedCenteredError activeFluctuationMass
  apply (norm_sum_le _ _).trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro t _
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (hcoef t.1 t.2) (norm_nonneg _)

/-- No claim that e actually is exceptional or has a specified zero. -/
theorem actual_adjusted_error_radical_bound {G : ℝ → ℝ}
    (hc : HasCompactSupport G) (hd : ContDiff ℝ ∞ G)
    (hG : ∀ t : ℝ, 2 < t → G t = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (R : ℝ) (_hR : 2 ≤ R)
      (B N : ℕ), 0 < N → ∀ (H b : ℝ) (f : ℕ → ℂ) (e : CharacterSlot ⌊R^2⌋₊),
      ‖adjustedCenteredError ⌊R^2⌋₊ B N H b f (logWeight R G) e‖ ≤
        C*radicalMajorant R N*activeFluctuationMass ⌊R^2⌋₊ B N H b f e := by
  obtain ⟨C,hC,hbound⟩ := actual_character_coefficients_radical_bound hc hd hG
  refine ⟨C,hC,?_⟩
  intro R hR B N hN H b f e
  exact actual_adjusted_error_le_active_mass _ B N H b f (logWeight R G) e
    (fun r χ => hbound R hR r N hN χ)

theorem active_mass_le_base_plus_actual_correction (Q B N : ℕ) (H b : ℝ)
    (f : ℕ → ℂ) (e : CharacterSlot Q) :
    activeFluctuationMass Q B N H b f e ≤
      actualFluctuationMass Q N H (blockCarrier B) f +
        ‖(normalizedPowerWindow B N H b : ℝ)‖ := by
  let a : CharacterSlot Q → ℂ := fun t =>
    (2*(H : ℂ))⁻¹*∑ U ∈ centeredWindow (blockCarrier B) N H,
      (f U*star (t.2.val (U : ZMod t.1.val))-if t.1.val=1 then 1 else 0)
  have he (t : CharacterSlot Q) :
      (2*(H : ℂ))⁻¹*∑ U ∈ centeredWindow (blockCarrier B) N H,
        ((f U*star (t.2.val (U : ZMod t.1.val))-if t.1.val=1 then 1 else 0)+
          if t=e then (powerWeight b U : ℂ) else 0) =
      a t + if t=e then ((normalizedPowerWindow B N H b : ℝ) : ℂ) else 0 := by
    rw [Finset.sum_add_distrib,mul_add]
    dsimp only [a]
    congr 1
    by_cases ht : t=e
    · simp only [ht,ite_true]
      simp [normalizedPowerWindow]
    · simp only [ht,ite_false,Finset.sum_const_zero,mul_zero]
  unfold activeFluctuationMass
  simp_rw [he]
  calc
    _ ≤ ∑ t : CharacterSlot Q,
      (‖a t‖+‖if t=e then ((normalizedPowerWindow B N H b : ℝ) : ℂ) else 0‖) :=
        Finset.sum_le_sum (fun _ _ => norm_add_le _ _)
    _ = _ := by
      rw [Finset.sum_add_distrib]
      have ha : (∑ t : CharacterSlot Q, ‖a t‖) = actualFluctuationMass Q N H (blockCarrier B) f := by
        rw [Fintype.sum_sigma]
        rfl
      rw [ha]
      congr 1
      simp only [apply_ite norm, norm_zero]
      rw [Finset.sum_ite_eq']
      simp only [Finset.mem_univ,ite_true,Complex.norm_real]

end GoldbachCircleMethodActiveCharacterRadicalErrorV18158
