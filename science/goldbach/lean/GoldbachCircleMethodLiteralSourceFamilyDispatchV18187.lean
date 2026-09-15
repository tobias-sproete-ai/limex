import GoldbachCircleMethodActualCharacterFamilyInclusionV18186
import Mathlib.Algebra.Star.BigOperators

set_option autoImplicit false
open scoped BigOperators Classical
open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodFiniteWindowConvolutionV18119
open GoldbachCircleMethodLogCutoffPresieveBindingV18120
open GoldbachCircleMethodExceptionalWeightBoundaryV18128
open GoldbachCircleMethodActiveExceptionalCenteringV18129
open GoldbachCircleMethodActualCharacterRadicalErrorV18157
open GoldbachCircleMethodActiveCharacterRadicalErrorV18158
open GoldbachCircleMethodActualWindowSourceNormalizationV18185
open GoldbachCircleMethodActualCharacterFamilyInclusionV18186

namespace GoldbachCircleMethodLiteralSourceFamilyDispatchV18187

/-- Finite normalization of one literal source-family estimate. This only
transports the supplied estimate; it does not establish analytic smallness. -/
theorem finite_family_normalization_transfer {T : Type*} [Fintype T]
    (J : Finset ℕ) (N : ℕ) {H A : ℝ} (hH : 1 ≤ H) (z : T → ℂ)
    (hsource : (∑ t : T,
      ‖z t‖ / (((centeredWindow J N H).card : ℝ) + H)) ≤ A) :
    (∑ t : T, ‖(2 * (H : ℂ))⁻¹ * z t‖) ≤ 2 * A := by
  calc
    _ ≤ ∑ t : T, 2 * (‖z t‖ /
        (((centeredWindow J N H).card : ℝ) + H)) := by
      apply Finset.sum_le_sum
      intro t _
      exact complex_window_normalization_transfer J N hH (z t) le_rfl
    _ = 2 * ∑ t : T, ‖z t‖ /
        (((centeredWindow J N H).card : ℝ) + H) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ 2 * A := mul_le_mul_of_nonneg_left hsource (by norm_num)

/-- The literal base source expression gives the actual V157 base mass. -/
theorem actual_base_mass_from_literal_source (Q N : ℕ) (J : Finset ℕ)
    {H A : ℝ} (hH : 1 ≤ H) (f : ℕ → ℂ)
    (hsource : (∑ t : CharacterSlot Q,
      ‖∑ U ∈ centeredWindow J N H,
        (f U * star (t.2.val (U : ZMod t.1.val)) -
          if t.1.val = 1 then 1 else 0)‖ /
        (((centeredWindow J N H).card : ℝ) + H)) ≤ A) :
    actualFluctuationMass Q N H J f ≤ 2 * A := by
  have h := finite_family_normalization_transfer J N hH
    (fun t : CharacterSlot Q => ∑ U ∈ centeredWindow J N H,
      (f U * star (t.2.val (U : ZMod t.1.val)) -
        if t.1.val = 1 then 1 else 0)) hsource
  simpa only [actualFluctuationMass, Fintype.sum_sigma] using h

/-- The literal active source expression gives the actual V158 active mass,
with its exceptional correction retained inside the same whole norm. -/
theorem actual_active_mass_from_literal_source (Q B N : ℕ)
    {H A : ℝ} (hH : 1 ≤ H) (b : ℝ) (f : ℕ → ℂ) (e : CharacterSlot Q)
    (hsource : (∑ t : CharacterSlot Q,
      ‖∑ U ∈ centeredWindow (blockCarrier B) N H,
        ((f U * star (t.2.val (U : ZMod t.1.val)) -
          if t.1.val = 1 then 1 else 0) +
          if t = e then (powerWeight b U : ℂ) else 0)‖ /
        (((centeredWindow (blockCarrier B) N H).card : ℝ) + H)) ≤ A) :
    activeFluctuationMass Q B N H b f e ≤ 2 * A := by
  exact finite_family_normalization_transfer (blockCarrier B) N hH
    (fun t : CharacterSlot Q => ∑ U ∈ centeredWindow (blockCarrier B) N H,
      ((f U * star (t.2.val (U : ZMod t.1.val)) -
        if t.1.val = 1 then 1 else 0) +
        if t = e then (powerWeight b U : ℂ) else 0)) hsource

/-- Base source data on the larger literal family controls the smaller base
mass through the actual CharacterSlot inclusion. -/
theorem base_mass_from_larger_literal_source {Q Q' : ℕ} (hQQ' : Q ≤ Q')
    (N : ℕ) (J : Finset ℕ) {H A : ℝ} (hH : 1 ≤ H) (f : ℕ → ℂ)
    (hsource : (∑ t : CharacterSlot Q',
      ‖∑ U ∈ centeredWindow J N H,
        (f U * star (t.2.val (U : ZMod t.1.val)) -
          if t.1.val = 1 then 1 else 0)‖ /
        (((centeredWindow J N H).card : ℝ) + H)) ≤ A) :
    actualFluctuationMass Q N H J f ≤ 2 * A := by
  exact (actualFluctuationMass_mono hQQ' N H J f).trans
    (actual_base_mass_from_literal_source Q' N J hH f hsource)

/-- Active source data at the included exceptional slot controls the smaller
active mass without changing or dropping the correction. -/
theorem active_mass_from_larger_included_literal_source {Q Q' : ℕ}
    (hQQ' : Q ≤ Q') (B N : ℕ) {H A : ℝ} (hH : 1 ≤ H)
    (b : ℝ) (f : ℕ → ℂ) (e : CharacterSlot Q)
    (hsource : (∑ t : CharacterSlot Q',
      ‖∑ U ∈ centeredWindow (blockCarrier B) N H,
        ((f U * star (t.2.val (U : ZMod t.1.val)) -
          if t.1.val = 1 then 1 else 0) +
          if t = includeSlot hQQ' e then (powerWeight b U : ℂ) else 0)‖ /
        (((centeredWindow (blockCarrier B) N H).card : ℝ) + H)) ≤ A) :
    activeFluctuationMass Q B N H b f e ≤ 2 * A := by
  exact (activeMass_le_activeMass_included hQQ' B N H b f e).trans
    (actual_active_mass_from_literal_source Q' B N hH b f
      (includeSlot hQQ' e) hsource)

/-- If the larger source exception lies outside the smaller conductor range,
the smaller base mass is bounded by the larger active mass. The whole absent
indexed norm is omitted; no additive term is removed inside a retained norm. -/
theorem base_mass_from_larger_outside_active_literal_source {Q Q' : ℕ}
    (hQQ' : Q ≤ Q') (B N : ℕ) {H A : ℝ} (hH : 1 ≤ H)
    (b : ℝ) (f : ℕ → ℂ) (e : CharacterSlot Q') (he : Q < e.1.val)
    (hsource : (∑ t : CharacterSlot Q',
      ‖∑ U ∈ centeredWindow (blockCarrier B) N H,
        ((f U * star (t.2.val (U : ZMod t.1.val)) -
          if t.1.val = 1 then 1 else 0) +
          if t = e then (powerWeight b U : ℂ) else 0)‖ /
        (((centeredWindow (blockCarrier B) N H).card : ℝ) + H)) ≤ A) :
    actualFluctuationMass Q N H (blockCarrier B) f ≤ 2 * A := by
  exact (baseMass_le_activeMass_of_exception_outside hQQ' B N H b f e he).trans
    (actual_active_mass_from_literal_source Q' B N hH b f e hsource)

/-- Conjugating a finite sum whose arithmetic coefficient, principal term and
exceptional correction are real does not change its norm. -/
theorem norm_real_corrected_star_sum (I : Finset ℕ)
    (a p c : ℕ → ℝ) (z : ℕ → ℂ) :
    ‖∑ U ∈ I, ((a U : ℂ) * star (z U) - (p U : ℂ) + (c U : ℂ))‖ =
      ‖∑ U ∈ I, ((a U : ℂ) * z U - (p U : ℂ) + (c U : ℂ))‖ := by
  have heq : star (∑ U ∈ I,
      ((a U : ℂ) * star (z U) - (p U : ℂ) + (c U : ℂ))) =
      ∑ U ∈ I, ((a U : ℂ) * z U - (p U : ℂ) + (c U : ℂ)) := by
    simp only [star_sum, star_add, star_sub, star_mul,
      Complex.star_def, Complex.conj_ofReal]
    simp [mul_comm]
  calc
    _ = ‖star (∑ U ∈ I,
        ((a U : ℂ) * star (z U) - (p U : ℂ) + (c U : ℂ)))‖ :=
      (norm_star _).symm
    _ = _ := congrArg norm heq

/-- On the literal actual window, V120 blockInput is exactly real von Mangoldt. -/
theorem blockInput_eq_vonMangoldt_on_actual_window (B N U : ℕ) (H : ℝ)
    (hU : U ∈ centeredWindow (blockCarrier B) N H) :
    blockInput B U = (ArithmeticFunction.vonMangoldt U : ℂ) := by
  exact if_pos ((mem_centeredWindow (blockCarrier B) N U H).mp hU).1

end GoldbachCircleMethodLiteralSourceFamilyDispatchV18187
