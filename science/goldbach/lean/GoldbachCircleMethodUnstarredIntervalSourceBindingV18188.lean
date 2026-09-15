import GoldbachCircleMethodLiteralSourceFamilyDispatchV18187

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
open GoldbachCircleMethodLiteralSourceFamilyDispatchV18187

namespace GoldbachCircleMethodUnstarredIntervalSourceBindingV18188

/-- The literal actual base-window norm equals the unstarred von-Mangoldt
interval norm on V185's exact clipped integer interval. -/
theorem literal_base_window_norm_eq_unstarred_interval (M N Q : ℕ)
    {H : ℝ} (hH : 0 ≤ H) (t : CharacterSlot Q) :
    ‖∑ U ∈ centeredWindow (blockCarrier M) N H,
      (blockInput M U * star (t.2.val (U : ZMod t.1.val)) -
        if t.1.val = 1 then 1 else 0)‖ =
      ‖∑ U ∈ Finset.Icc (max (M / 2 + 1) (N - ⌊H⌋₊))
          (min M (N + ⌊H⌋₊)),
        ((ArithmeticFunction.vonMangoldt U : ℂ) *
          t.2.val (U : ZMod t.1.val) -
          if t.1.val = 1 then 1 else 0)‖ := by
  let I := Finset.Icc (max (M / 2 + 1) (N - ⌊H⌋₊))
    (min M (N + ⌊H⌋₊))
  have hI : centeredWindow (blockCarrier M) N H = I :=
    block_centeredWindow_eq_Icc M N hH
  have hinput :
      (∑ U ∈ centeredWindow (blockCarrier M) N H,
        (blockInput M U * star (t.2.val (U : ZMod t.1.val)) -
          if t.1.val = 1 then 1 else 0)) =
      ∑ U ∈ I,
        ((ArithmeticFunction.vonMangoldt U : ℂ) *
          star (t.2.val (U : ZMod t.1.val)) -
          if t.1.val = 1 then 1 else 0) := by
    rw [hI]
    apply Finset.sum_congr rfl
    intro U hU
    have hUW : U ∈ centeredWindow (blockCarrier M) N H := by
      rw [hI]
      exact hU
    rw [blockInput_eq_vonMangoldt_on_actual_window M N U H hUW]
  rw [hinput]
  have h := norm_real_corrected_star_sum I
      (fun U => ArithmeticFunction.vonMangoldt U)
      (fun _ => if t.1.val = 1 then 1 else 0)
      (fun _ => 0) (fun U => t.2.val (U : ZMod t.1.val))
  by_cases hq : t.1.val = 1 <;> simp [hq, I] at h ⊢ <;> exact h

/-- The active-window identity retains the same real power correction inside
the whole norm and changes only star orientation. -/
theorem literal_active_window_norm_eq_unstarred_interval (M N Q : ℕ)
    {H : ℝ} (hH : 0 ≤ H) (b : ℝ) (e t : CharacterSlot Q) :
    ‖∑ U ∈ centeredWindow (blockCarrier M) N H,
      ((blockInput M U * star (t.2.val (U : ZMod t.1.val)) -
        if t.1.val = 1 then 1 else 0) +
        if t = e then (powerWeight b U : ℂ) else 0)‖ =
      ‖∑ U ∈ Finset.Icc (max (M / 2 + 1) (N - ⌊H⌋₊))
          (min M (N + ⌊H⌋₊)),
        (((ArithmeticFunction.vonMangoldt U : ℂ) *
          t.2.val (U : ZMod t.1.val) -
          if t.1.val = 1 then 1 else 0) +
          if t = e then (powerWeight b U : ℂ) else 0)‖ := by
  let I := Finset.Icc (max (M / 2 + 1) (N - ⌊H⌋₊))
    (min M (N + ⌊H⌋₊))
  have hI : centeredWindow (blockCarrier M) N H = I :=
    block_centeredWindow_eq_Icc M N hH
  have hinput :
      (∑ U ∈ centeredWindow (blockCarrier M) N H,
        ((blockInput M U * star (t.2.val (U : ZMod t.1.val)) -
          if t.1.val = 1 then 1 else 0) +
          if t = e then (powerWeight b U : ℂ) else 0)) =
      ∑ U ∈ I,
        (((ArithmeticFunction.vonMangoldt U : ℂ) *
          star (t.2.val (U : ZMod t.1.val)) -
          if t.1.val = 1 then 1 else 0) +
          if t = e then (powerWeight b U : ℂ) else 0) := by
    rw [hI]
    apply Finset.sum_congr rfl
    intro U hU
    have hUW : U ∈ centeredWindow (blockCarrier M) N H := by
      rw [hI]
      exact hU
    rw [blockInput_eq_vonMangoldt_on_actual_window M N U H hUW]
  rw [hinput]
  have h := norm_real_corrected_star_sum I
      (fun U => ArithmeticFunction.vonMangoldt U)
      (fun _ => if t.1.val = 1 then 1 else 0)
      (fun U => if t = e then powerWeight b U else 0)
      (fun U => t.2.val (U : ZMod t.1.val))
  by_cases hte : t = e
  · subst e
    by_cases hq : t.1.val = 1 <;> simpa [hq, I] using h
  · by_cases hq : t.1.val = 1 <;> simpa [hq, hte, I] using h

/-- An unstarred source-family estimate on the exact admissible interval at
Q' controls the smaller actual base mass. The source estimate remains a premise. -/
theorem base_mass_from_unstarred_interval_source {Q Q' : ℕ} (hQQ' : Q ≤ Q')
    (M N : ℕ) (hM : 6 ≤ M) (hN : N ∈ blockCarrier M)
    {H A : ℝ} (hH : 1 ≤ H)
    (hsource :
      (M : ℝ) / 3 ≤
          ((max (M / 2 + 1) (N - ⌊H⌋₊) - 1 : ℕ) : ℝ) →
      (Finset.Icc (max (M / 2 + 1) (N - ⌊H⌋₊))
        (min M (N + ⌊H⌋₊))).Nonempty →
      (∑ t : CharacterSlot Q',
        ‖∑ U ∈ Finset.Icc (max (M / 2 + 1) (N - ⌊H⌋₊))
            (min M (N + ⌊H⌋₊)),
          ((ArithmeticFunction.vonMangoldt U : ℂ) *
            t.2.val (U : ZMod t.1.val) -
            if t.1.val = 1 then 1 else 0)‖ /
          (((Finset.Icc (max (M / 2 + 1) (N - ⌊H⌋₊))
            (min M (N + ⌊H⌋₊))).card : ℝ) + H)) ≤ A) :
    actualFluctuationMass Q N H (blockCarrier M) (blockInput M) ≤ 2 * A := by
  have hH0 : 0 ≤ H := le_trans (by norm_num) hH
  have hleft := block_left_endpoint_admits_explicit_formula M N (H := H) hM
  have hne : (Finset.Icc (max (M / 2 + 1) (N - ⌊H⌋₊))
      (min M (N + ⌊H⌋₊))).Nonempty := by
    rw [← block_centeredWindow_eq_Icc M N hH0]
    exact centeredWindow_nonempty (blockCarrier M) N hH0 hN
  have hsrc := hsource hleft hne
  have hstar : (∑ t : CharacterSlot Q',
      ‖∑ U ∈ centeredWindow (blockCarrier M) N H,
        (blockInput M U * star (t.2.val (U : ZMod t.1.val)) -
          if t.1.val = 1 then 1 else 0)‖ /
        (((centeredWindow (blockCarrier M) N H).card : ℝ) + H)) ≤ A := by
    simp_rw [literal_base_window_norm_eq_unstarred_interval M N Q' hH0]
    have hI := congrArg Finset.card (block_centeredWindow_eq_Icc M N hH0)
    simp only [blockCarrier]
    rw [hI]
    exact hsrc
  exact base_mass_from_larger_literal_source hQQ' N (blockCarrier M)
    hH (blockInput M) hstar

/-- The matching in-range exceptional source branch controls the smaller
active mass with the exact included slot and correction. -/
theorem active_mass_from_unstarred_interval_source_included {Q Q' : ℕ}
    (hQQ' : Q ≤ Q') (M N : ℕ) (hM : 6 ≤ M) (hN : N ∈ blockCarrier M)
    {H A : ℝ} (hH : 1 ≤ H) (b : ℝ) (e : CharacterSlot Q)
    (hsource :
      (M : ℝ) / 3 ≤
          ((max (M / 2 + 1) (N - ⌊H⌋₊) - 1 : ℕ) : ℝ) →
      (Finset.Icc (max (M / 2 + 1) (N - ⌊H⌋₊))
        (min M (N + ⌊H⌋₊))).Nonempty →
      (∑ t : CharacterSlot Q',
        ‖∑ U ∈ Finset.Icc (max (M / 2 + 1) (N - ⌊H⌋₊))
            (min M (N + ⌊H⌋₊)),
          (((ArithmeticFunction.vonMangoldt U : ℂ) *
            t.2.val (U : ZMod t.1.val) -
            if t.1.val = 1 then 1 else 0) +
            if t = includeSlot hQQ' e then (powerWeight b U : ℂ) else 0)‖ /
          (((Finset.Icc (max (M / 2 + 1) (N - ⌊H⌋₊))
            (min M (N + ⌊H⌋₊))).card : ℝ) + H)) ≤ A) :
    activeFluctuationMass Q M N H b (blockInput M) e ≤ 2 * A := by
  have hH0 : 0 ≤ H := le_trans (by norm_num) hH
  have hleft := block_left_endpoint_admits_explicit_formula M N (H := H) hM
  have hne : (Finset.Icc (max (M / 2 + 1) (N - ⌊H⌋₊))
      (min M (N + ⌊H⌋₊))).Nonempty := by
    rw [← block_centeredWindow_eq_Icc M N hH0]
    exact centeredWindow_nonempty (blockCarrier M) N hH0 hN
  have hsrc := hsource hleft hne
  have hstar : (∑ t : CharacterSlot Q',
      ‖∑ U ∈ centeredWindow (blockCarrier M) N H,
        ((blockInput M U * star (t.2.val (U : ZMod t.1.val)) -
          if t.1.val = 1 then 1 else 0) +
          if t = includeSlot hQQ' e then (powerWeight b U : ℂ) else 0)‖ /
        (((centeredWindow (blockCarrier M) N H).card : ℝ) + H)) ≤ A := by
    simp_rw [literal_active_window_norm_eq_unstarred_interval M N Q' hH0 b
      (includeSlot hQQ' e)]
    have hI := congrArg Finset.card (block_centeredWindow_eq_Icc M N hH0)
    simp only [blockCarrier]
    rw [hI]
    exact hsrc
  exact active_mass_from_larger_included_literal_source hQQ' M N hH b
    (blockInput M) e hstar

/-- An exceptional source slot above Q controls the smaller uncorrected base
mass. The omitted item is the entire absent indexed norm. -/
theorem base_mass_from_unstarred_interval_source_outside {Q Q' : ℕ}
    (hQQ' : Q ≤ Q') (M N : ℕ) (hM : 6 ≤ M) (hN : N ∈ blockCarrier M)
    {H A : ℝ} (hH : 1 ≤ H) (b : ℝ) (e : CharacterSlot Q')
    (he : Q < e.1.val)
    (hsource :
      (M : ℝ) / 3 ≤
          ((max (M / 2 + 1) (N - ⌊H⌋₊) - 1 : ℕ) : ℝ) →
      (Finset.Icc (max (M / 2 + 1) (N - ⌊H⌋₊))
        (min M (N + ⌊H⌋₊))).Nonempty →
      (∑ t : CharacterSlot Q',
        ‖∑ U ∈ Finset.Icc (max (M / 2 + 1) (N - ⌊H⌋₊))
            (min M (N + ⌊H⌋₊)),
          (((ArithmeticFunction.vonMangoldt U : ℂ) *
            t.2.val (U : ZMod t.1.val) -
            if t.1.val = 1 then 1 else 0) +
            if t = e then (powerWeight b U : ℂ) else 0)‖ /
          (((Finset.Icc (max (M / 2 + 1) (N - ⌊H⌋₊))
            (min M (N + ⌊H⌋₊))).card : ℝ) + H)) ≤ A) :
    actualFluctuationMass Q N H (blockCarrier M) (blockInput M) ≤ 2 * A := by
  have hH0 : 0 ≤ H := le_trans (by norm_num) hH
  have hleft := block_left_endpoint_admits_explicit_formula M N (H := H) hM
  have hne : (Finset.Icc (max (M / 2 + 1) (N - ⌊H⌋₊))
      (min M (N + ⌊H⌋₊))).Nonempty := by
    rw [← block_centeredWindow_eq_Icc M N hH0]
    exact centeredWindow_nonempty (blockCarrier M) N hH0 hN
  have hsrc := hsource hleft hne
  have hstar : (∑ t : CharacterSlot Q',
      ‖∑ U ∈ centeredWindow (blockCarrier M) N H,
        ((blockInput M U * star (t.2.val (U : ZMod t.1.val)) -
          if t.1.val = 1 then 1 else 0) +
          if t = e then (powerWeight b U : ℂ) else 0)‖ /
        (((centeredWindow (blockCarrier M) N H).card : ℝ) + H)) ≤ A := by
    simp_rw [literal_active_window_norm_eq_unstarred_interval M N Q' hH0 b e]
    have hI := congrArg Finset.card (block_centeredWindow_eq_Icc M N hH0)
    simp only [blockCarrier]
    rw [hI]
    exact hsrc
  exact base_mass_from_larger_outside_active_literal_source hQQ' M N hH b
    (blockInput M) e he hstar

end GoldbachCircleMethodUnstarredIntervalSourceBindingV18188
