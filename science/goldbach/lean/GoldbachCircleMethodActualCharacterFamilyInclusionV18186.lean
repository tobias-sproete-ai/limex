import GoldbachCircleMethodActualWindowSourceNormalizationV18185

set_option autoImplicit false
open scoped BigOperators Classical
open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodFiniteWindowConvolutionV18119
open GoldbachCircleMethodLogCutoffPresieveBindingV18120
open GoldbachCircleMethodExceptionalWeightBoundaryV18128
open GoldbachCircleMethodActiveExceptionalCenteringV18129
open GoldbachCircleMethodActualCharacterRadicalErrorV18157
open GoldbachCircleMethodActiveCharacterRadicalErrorV18158

namespace GoldbachCircleMethodActualCharacterFamilyInclusionV18186

/-- The actual CharacterSlot inclusion. The conductor and primitive character
are reused literally; only the proof of the larger conductor cutoff changes. -/
def includeSlot {Q Q' : ℕ} (hQQ' : Q ≤ Q') (t : CharacterSlot Q) :
    CharacterSlot Q' :=
  ⟨⟨t.1.val, Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp t.1.property).1,
      ((Finset.mem_Icc.mp t.1.property).2).trans hQQ'⟩⟩, t.2⟩

theorem includeSlot_injective {Q Q' : ℕ} (hQQ' : Q ≤ Q') :
    Function.Injective (includeSlot hQQ') := by
  rintro ⟨⟨r, hr⟩, chi⟩ ⟨⟨s, hs⟩, psi⟩ h
  have hrs : r = s := congrArg (fun t : CharacterSlot Q' => t.1.val) h
  subst s
  have hp : chi = psi := eq_of_heq (Sigma.mk.inj_iff.mp h).2
  cases hp
  rfl

def slotEmbedding {Q Q' : ℕ} (hQQ' : Q ≤ Q') :
    CharacterSlot Q ↪ CharacterSlot Q' :=
  ⟨includeSlot hQQ', includeSlot_injective hQQ'⟩

theorem includeSlot_conductor {Q Q' : ℕ} (hQQ' : Q ≤ Q')
    (t : CharacterSlot Q) :
    (includeSlot hQQ' t).1.val = t.1.val := rfl

/-- A slot whose conductor is above the smaller cutoff is not the image of
any smaller slot. This excludes the whole indexed norm summand only. -/
theorem includeSlot_ne_of_conductor_outside {Q Q' : ℕ}
    (hQQ' : Q ≤ Q') (e : CharacterSlot Q') (he : Q < e.1.val)
    (t : CharacterSlot Q) : includeSlot hQQ' t ≠ e := by
  intro h
  have hv : t.1.val = e.1.val :=
    congrArg (fun z : CharacterSlot Q' => z.1.val) h
  have ht := (Finset.mem_Icc.mp t.1.property).2
  omega

theorem sum_embedding_le {A B : Type*} [Fintype A] [Fintype B]
    (e : A ↪ B) (F : B → ℝ) (hF : ∀ x, 0 ≤ F x) :
    (∑ x : A, F (e x)) ≤ ∑ x : B, F x := by
  calc
    _ = ∑ y ∈ Finset.univ.map e, F y := (Finset.sum_map _ e F).symm
    _ ≤ ∑ y : B, F y := Finset.sum_le_univ_sum_of_nonneg hF

/-- Monotonicity of the literal V157 base mass under actual CharacterSlot
inclusion. -/
theorem actualFluctuationMass_mono {Q Q' : ℕ} (hQQ' : Q ≤ Q')
    (N : ℕ) (H : ℝ) (J : Finset ℕ) (f : ℕ → ℂ) :
    actualFluctuationMass Q N H J f ≤ actualFluctuationMass Q' N H J f := by
  let F : CharacterSlot Q' → ℝ := fun t =>
    ‖(2*(H : ℂ))⁻¹ * ∑ U ∈ centeredWindow J N H,
      (f U * star (t.2.val (U : ZMod t.1.val)) -
        if t.1.val = 1 then 1 else 0)‖
  have hs := sum_embedding_le (slotEmbedding hQQ') F (fun _ => norm_nonneg _)
  have hpoint (t : CharacterSlot Q) :
      F (slotEmbedding hQQ' t) =
        ‖(2*(H : ℂ))⁻¹ * ∑ U ∈ centeredWindow J N H,
          (f U * star (t.2.val (U : ZMod t.1.val)) -
            if t.1.val = 1 then 1 else 0)‖ := by
    rfl
  simp_rw [hpoint] at hs
  simpa only [F, actualFluctuationMass, Fintype.sum_sigma] using hs

/-- If the exceptional conductor is above the smaller cutoff, restriction to
the smaller carrier omits its entire nonnegative norm summand. No correction
is removed from inside any retained norm. -/
theorem baseMass_le_activeMass_of_exception_outside {Q Q' : ℕ}
    (hQQ' : Q ≤ Q') (B N : ℕ) (H b : ℝ) (f : ℕ → ℂ)
    (e : CharacterSlot Q') (he : Q < e.1.val) :
    actualFluctuationMass Q N H (blockCarrier B) f ≤
      activeFluctuationMass Q' B N H b f e := by
  let F : CharacterSlot Q' → ℝ := fun t =>
    ‖(2*(H : ℂ))⁻¹ * ∑ U ∈ centeredWindow (blockCarrier B) N H,
      ((f U * star (t.2.val (U : ZMod t.1.val)) -
        if t.1.val = 1 then 1 else 0) +
        if t = e then (powerWeight b U : ℂ) else 0)‖
  have hs := sum_embedding_le (slotEmbedding hQQ') F (fun _ => norm_nonneg _)
  have hpoint (t : CharacterSlot Q) :
      F (slotEmbedding hQQ' t) =
        ‖(2*(H : ℂ))⁻¹ * ∑ U ∈ centeredWindow (blockCarrier B) N H,
          (f U * star (t.2.val (U : ZMod t.1.val)) -
            if t.1.val = 1 then 1 else 0)‖ := by
    have hne := includeSlot_ne_of_conductor_outside hQQ' e he t
    change
      ‖(2*(H : ℂ))⁻¹ * ∑ U ∈ centeredWindow (blockCarrier B) N H,
        ((f U * star (t.2.val (U : ZMod t.1.val)) -
          if t.1.val = 1 then 1 else 0) +
          if includeSlot hQQ' t = e then (powerWeight b U : ℂ) else 0)‖ = _
    simp only [hne, if_false, add_zero]
  simp_rw [hpoint] at hs
  simpa only [F, actualFluctuationMass, activeFluctuationMass,
    Fintype.sum_sigma] using hs

/-- Active-to-active inclusion preserves the exact exceptional slot identity,
so the correction remains inside the same whole norm summand. -/
theorem activeMass_le_activeMass_included {Q Q' : ℕ}
    (hQQ' : Q ≤ Q') (B N : ℕ) (H b : ℝ) (f : ℕ → ℂ)
    (e : CharacterSlot Q) :
    activeFluctuationMass Q B N H b f e ≤
      activeFluctuationMass Q' B N H b f (includeSlot hQQ' e) := by
  let F : CharacterSlot Q' → ℝ := fun t =>
    ‖(2*(H : ℂ))⁻¹ * ∑ U ∈ centeredWindow (blockCarrier B) N H,
      ((f U * star (t.2.val (U : ZMod t.1.val)) -
        if t.1.val = 1 then 1 else 0) +
        if t = includeSlot hQQ' e then (powerWeight b U : ℂ) else 0)‖
  have hs := sum_embedding_le (slotEmbedding hQQ') F (fun _ => norm_nonneg _)
  have hpoint (t : CharacterSlot Q) :
      F (slotEmbedding hQQ' t) =
        ‖(2*(H : ℂ))⁻¹ * ∑ U ∈ centeredWindow (blockCarrier B) N H,
          ((f U * star (t.2.val (U : ZMod t.1.val)) -
            if t.1.val = 1 then 1 else 0) +
            if t = e then (powerWeight b U : ℂ) else 0)‖ := by
    change
      ‖(2*(H : ℂ))⁻¹ * ∑ U ∈ centeredWindow (blockCarrier B) N H,
        ((f U * star (t.2.val (U : ZMod t.1.val)) -
          if t.1.val = 1 then 1 else 0) +
          if includeSlot hQQ' t = includeSlot hQQ' e then
            (powerWeight b U : ℂ) else 0)‖ = _
    simp only [(includeSlot_injective hQQ').eq_iff]
  simp_rw [hpoint] at hs
  simpa only [F, activeFluctuationMass] using hs

end GoldbachCircleMethodActualCharacterFamilyInclusionV18186
