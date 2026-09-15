import GoldbachCircleMethodFiniteCompanionBindingV18118

set_option autoImplicit false
open scoped BigOperators Classical
open GoldbachCircleMethodFiniteResiduePrefixV1866
open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodFiniteCompanionBindingV18118

namespace GoldbachCircleMethodFiniteWindowConvolutionV18119

/-- Exact convolution on a finite input support. The roughness premise is
needed only where the actual input coefficient is nonzero. -/
theorem finite_support_convolution (Q N : ℕ) (S : Finset ℕ)
    (f w : ℕ → ℂ)
    (hrough : ∀ U ∈ S, f U ≠ 0 →
      ∀ q : PositiveLevel Q, IsUnit (U : ZMod q.val)) :
    (∑ U ∈ S, f U * ∑ q : PositiveLevel Q, w q.val *
      unitCharacterSum q.val ((N : ZMod q.val) - (U : ZMod q.val))) =
    ∑ r : PositiveLevel Q,
      ∑ χ : {χ : DirichletCharacter ℂ r.val // χ.IsPrimitive},
        ((r.val : ℂ)/(r.val.totient : ℂ)) * χ.val (N : ZMod r.val) *
          finiteCompanion r N w *
          (∑ U ∈ S, f U * star (χ.val (U : ZMod r.val))) := by
  calc
    _ = ∑ U ∈ S, ∑ r : PositiveLevel Q,
        ∑ χ : {χ : DirichletCharacter ℂ r.val // χ.IsPrimitive},
          ((r.val : ℂ)/(r.val.totient : ℂ)) * χ.val (N : ZMod r.val) *
            finiteCompanion r N w * (f U * star (χ.val (U : ZMod r.val))) := by
      apply Finset.sum_congr rfl
      intro U hUS
      by_cases hf : f U = 0
      · simp only [hf, zero_mul, mul_zero, Finset.sum_const_zero]
      · rw [weighted_ramanujan_companion_expansion Q N U w (hrough U hUS hf)]
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro r _
        apply Finset.sum_congr rfl
        intro χ _
        ring
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro r _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro χ _
      exact (Finset.mul_sum _ _ _).symm

/-- A centered real-width window cut from the actual discrete source carrier.
The use of real subtraction avoids truncating negative shifts. -/
noncomputable def centeredWindow (J : Finset ℕ) (N : ℕ) (H : ℝ) : Finset ℕ :=
  J.filter (fun U => |(N : ℝ) - (U : ℝ)| ≤ H)

theorem mem_centeredWindow (J : Finset ℕ) (N U : ℕ) (H : ℝ) :
    U ∈ centeredWindow J N H ↔ U ∈ J ∧ |(N : ℝ) - (U : ℝ)| ≤ H := by
  simp only [centeredWindow, Finset.mem_filter]

/-- Exact indicator-kernel convolution with its declared normalization 1/(2H).
No assertion that the number of lattice points equals 2H is made. -/
noncomputable def normalizedWindowConvolution (Q N : ℕ) (H : ℝ)
    (J : Finset ℕ) (f w : ℕ → ℂ) : ℂ :=
  (2 * (H : ℂ))⁻¹ *
    ∑ U ∈ J, if |(N : ℝ) - (U : ℝ)| ≤ H then
      f U * ∑ q : PositiveLevel Q, w q.val *
        unitCharacterSum q.val ((N : ZMod q.val) - (U : ZMod q.val))
    else 0

/-- The complete finite-window character expansion, including the unchanged
normalization and the exact intersection with J. -/
theorem normalized_window_character_expansion (Q N : ℕ) (H : ℝ)
    (J : Finset ℕ) (f w : ℕ → ℂ)
    (hrough : ∀ U ∈ centeredWindow J N H, f U ≠ 0 →
      ∀ q : PositiveLevel Q, IsUnit (U : ZMod q.val)) :
    normalizedWindowConvolution Q N H J f w =
      ∑ r : PositiveLevel Q,
        ∑ χ : {χ : DirichletCharacter ℂ r.val // χ.IsPrimitive},
          ((r.val : ℂ)/(r.val.totient : ℂ)) * χ.val (N : ZMod r.val) *
            finiteCompanion r N w *
            ((2 * (H : ℂ))⁻¹ *
              ∑ U ∈ centeredWindow J N H, f U * star (χ.val (U : ZMod r.val))) := by
  unfold normalizedWindowConvolution
  rw [← Finset.sum_filter]
  change (2 * (H : ℂ))⁻¹ *
    (∑ U ∈ centeredWindow J N H, f U * ∑ q : PositiveLevel Q, w q.val *
      unitCharacterSum q.val ((N : ZMod q.val) - (U : ZMod q.val))) = _
  rw [finite_support_convolution Q N (centeredWindow J N H) f w hrough]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro χ _
  ring

/-- The constant-input window mass is the actual cardinality divided by 2H. -/
theorem normalized_window_mass (J : Finset ℕ) (N : ℕ) (H : ℝ) :
    (2 * (H : ℂ))⁻¹ *
      (∑ U ∈ J, if |(N : ℝ) - (U : ℝ)| ≤ H then (1 : ℂ) else 0) =
        ((centeredWindow J N H).card : ℂ) / (2 * (H : ℂ)) := by
  rw [← Finset.sum_filter]
  change (2 * (H : ℂ))⁻¹ * (∑ _U ∈ centeredWindow J N H, (1 : ℂ)) = _
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
  ring

/-- A finite boundary witness forbids silently replacing lattice mass by one. -/
theorem singleton_window_mass_not_one (N : ℕ) :
    ((centeredWindow {N} N 1).card : ℂ) / (2 * ((1 : ℝ) : ℂ)) ≠ 1 := by
  have hwindow : centeredWindow {N} N 1 = {N} := by
    ext U
    simp only [mem_centeredWindow, Finset.mem_singleton]
    constructor
    · exact fun h => h.1
    · intro h
      subst U
      exact ⟨rfl, by norm_num⟩
  rw [hwindow]
  norm_num

end GoldbachCircleMethodFiniteWindowConvolutionV18119
