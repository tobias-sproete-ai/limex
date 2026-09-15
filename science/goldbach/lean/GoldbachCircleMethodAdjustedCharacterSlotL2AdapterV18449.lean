import GoldbachCircleMethodActiveCharacterRadicalErrorV18158

/-!
# Goldbach V1.8.449: exact adjusted character-slot L2 adapter

The earlier L1 majorant takes absolute values slot by slot.  This module keeps
the exact finite adjusted source attached to its actual window coefficient and
applies Cauchy--Schwarz only after the literal character-slot correlation has
been exposed.

No distribution estimate or decay is asserted.  The two finite energies are
the exact remaining interface.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodAdjustedCharacterSlotL2AdapterV18449

open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodFiniteWindowConvolutionV18119
open GoldbachCircleMethodLogCutoffPresieveBindingV18120
open GoldbachCircleMethodPrincipalWindowBoundaryV18121
open GoldbachCircleMethodExceptionalWeightBoundaryV18128
open GoldbachCircleMethodActiveExceptionalCenteringV18129

/-- The literal normalized adjusted source attached to one character slot. -/
noncomputable def adjustedSlotSource (Q B N : ℕ) (H b : ℝ)
    (f : ℕ → ℂ) (e t : CharacterSlot Q) : ℂ :=
  (2 * (H : ℂ))⁻¹ *
    ∑ U ∈ centeredWindow (blockCarrier B) N H,
      ((f U * star (t.2.val (U : ZMod t.1.val)) -
          if t.1.val = 1 then 1 else 0) +
        if t = e then (powerWeight b U : ℂ) else 0)

/-- Exact coefficient energy on the unchanged finite character-slot carrier. -/
noncomputable def adjustedCoefficientEnergy (Q N : ℕ) (w : ℕ → ℂ) : ℝ :=
  ∑ t : CharacterSlot Q, ‖windowCoefficient t.1 N w t.2‖ ^ 2

/-- Exact adjusted source energy on the same carrier. -/
noncomputable def adjustedSourceEnergy (Q B N : ℕ) (H b : ℝ)
    (f : ℕ → ℂ) (e : CharacterSlot Q) : ℝ :=
  ∑ t : CharacterSlot Q, ‖adjustedSlotSource Q B N H b f e t‖ ^ 2

/-- The finite norm-correlation retained before Cauchy--Schwarz. -/
noncomputable def adjustedNormCorrelation (Q B N : ℕ) (H b : ℝ)
    (f w : ℕ → ℂ) (e : CharacterSlot Q) : ℝ :=
  ∑ t : CharacterSlot Q,
    ‖windowCoefficient t.1 N w t.2‖ *
      ‖adjustedSlotSource Q B N H b f e t‖

/-- Triangle inequality only: the exact adjusted error is bounded by the
literal coefficient/source norm-correlation, without a uniform coefficient
majorant and without an L1 source-mass factorization. -/
theorem adjusted_centered_error_norm_le_correlation
    (Q B N : ℕ) (H b : ℝ) (f w : ℕ → ℂ) (e : CharacterSlot Q) :
    ‖adjustedCenteredError Q B N H b f w e‖ ≤
      adjustedNormCorrelation Q B N H b f w e := by
  unfold adjustedCenteredError adjustedNormCorrelation adjustedSlotSource
  calc
    _ ≤ ∑ t : CharacterSlot Q,
        ‖windowCoefficient t.1 N w t.2 *
          ((2 * (H : ℂ))⁻¹ *
            ∑ U ∈ centeredWindow (blockCarrier B) N H,
              ((f U * star (t.2.val (U : ZMod t.1.val)) -
                  if t.1.val = 1 then 1 else 0) +
                if t = e then (powerWeight b U : ℂ) else 0))‖ :=
      norm_sum_le _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro t _ht
      rw [norm_mul]

/-- Exact finite Cauchy--Schwarz adapter at one target.  This is the squared
form, so no square-root side conditions or analytic estimates are hidden. -/
theorem adjusted_centered_error_sq_le_energy_product
    (Q B N : ℕ) (H b : ℝ) (f w : ℕ → ℂ) (e : CharacterSlot Q) :
    ‖adjustedCenteredError Q B N H b f w e‖ ^ 2 ≤
      adjustedCoefficientEnergy Q N w *
        adjustedSourceEnergy Q B N H b f e := by
  have hnorm : 0 ≤ ‖adjustedCenteredError Q B N H b f w e‖ := norm_nonneg _
  have hcorr : 0 ≤ adjustedNormCorrelation Q B N H b f w e := by
    unfold adjustedNormCorrelation
    exact Finset.sum_nonneg (fun t _ht =>
      mul_nonneg (norm_nonneg _) (norm_nonneg _))
  have htriangle := adjusted_centered_error_norm_le_correlation
    Q B N H b f w e
  have hsq : ‖adjustedCenteredError Q B N H b f w e‖ ^ 2 ≤
      (adjustedNormCorrelation Q B N H b f w e) ^ 2 :=
    (sq_le_sq₀ hnorm hcorr).mpr htriangle
  apply hsq.trans
  unfold adjustedNormCorrelation adjustedCoefficientEnergy adjustedSourceEnergy
  exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun t : CharacterSlot Q => ‖windowCoefficient t.1 N w t.2‖)
    (fun t : CharacterSlot Q => ‖adjustedSlotSource Q B N H b f e t‖)

/-- A verified energy-product budget yields the corresponding linear error
budget.  The budget remains an explicit premise; this theorem does not assert
that analytic number theory supplies it. -/
theorem adjusted_centered_error_norm_le_of_energy_product_le_sq
    (Q B N : ℕ) (H b C : ℝ) (f w : ℕ → ℂ) (e : CharacterSlot Q)
    (hC : 0 ≤ C)
    (henergy : adjustedCoefficientEnergy Q N w *
      adjustedSourceEnergy Q B N H b f e ≤ C ^ 2) :
    ‖adjustedCenteredError Q B N H b f w e‖ ≤ C := by
  have hnorm : 0 ≤ ‖adjustedCenteredError Q B N H b f w e‖ := norm_nonneg _
  have hsq : ‖adjustedCenteredError Q B N H b f w e‖ ^ 2 ≤ C ^ 2 :=
    (adjusted_centered_error_sq_le_energy_product Q B N H b f w e).trans henergy
  exact (sq_le_sq₀ hnorm hC).mp hsq

end GoldbachCircleMethodAdjustedCharacterSlotL2AdapterV18449
