import GoldbachCircleMethodHybridCenteredSourceSplitV18500

/-!
# Goldbach V1.8.501: hybrid centered correlation energy

The exact V1.8.500 source split is lifted through the literal character-slot
correlation.  Cauchy--Schwarz is applied separately on the true principal and
nonprincipal supports, so the centered principal source is never replaced by
the two large pieces from which it is formed.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodHybridCenteredCorrelationEnergyV18501

open GoldbachCircleMethodActiveExceptionalCenteringV18129
open GoldbachCircleMethodAdjustedCharacterSlotL2AdapterV18449
open GoldbachCircleMethodHybridCenteredSourceSplitV18500
open GoldbachCircleMethodLogCutoffPresieveBindingV18120
open GoldbachCircleMethodPrincipalWindowBoundaryV18121
open GoldbachCircleMethodPrincipalExceptionalSourceEnergyV18480
open GoldbachCircleMethodSparseCorrectionCorrelationSplitV18482

noncomputable def centeredPrincipalCorrelation
    (Q B N : ℕ) (H : ℝ) (w : ℕ → ℂ) : ℂ :=
  ∑ t : CharacterSlot Q,
    windowCoefficient t.1 N w t.2 * centeredPrincipalSlotSource Q B N H t

noncomputable def nonprincipalPrimitiveCorrelation
    (Q B N : ℕ) (H : ℝ) (w : ℕ → ℂ) : ℂ :=
  ∑ t : CharacterSlot Q,
    windowCoefficient t.1 N w t.2 * nonprincipalPrimitiveSlotSource Q B N H t

noncomputable def centeredPrincipalCoefficientEnergy
    (Q N : ℕ) (w : ℕ → ℂ) : ℝ :=
  ∑ t : CharacterSlot Q,
    if t.1.val = 1 then ‖windowCoefficient t.1 N w t.2‖ ^ 2 else 0

noncomputable def nonprincipalCoefficientEnergy
    (Q N : ℕ) (w : ℕ → ℂ) : ℝ :=
  ∑ t : CharacterSlot Q,
    if t.1.val = 1 then 0 else ‖windowCoefficient t.1 N w t.2‖ ^ 2

noncomputable def centeredPrincipalSourceEnergy
    (Q B N : ℕ) (H : ℝ) : ℝ :=
  ∑ t : CharacterSlot Q, ‖centeredPrincipalSlotSource Q B N H t‖ ^ 2

noncomputable def nonprincipalPrimitiveSourceEnergy
    (Q B N : ℕ) (H : ℝ) : ℝ :=
  ∑ t : CharacterSlot Q, ‖nonprincipalPrimitiveSlotSource Q B N H t‖ ^ 2

/-- Exact three-channel correlation with the arithmetic principal centering
left intact. -/
theorem adjustedCenteredError_eq_hybrid_correlations
    (Q B N : ℕ) (H b : ℝ) (w : ℕ → ℂ) (e : CharacterSlot Q) :
    adjustedCenteredError Q B N H b (blockInput B) w e =
      centeredPrincipalCorrelation Q B N H w +
        nonprincipalPrimitiveCorrelation Q B N H w +
          exceptionalPowerCorrelation Q B N H b w e := by
  change (∑ t : CharacterSlot Q,
      windowCoefficient t.1 N w t.2 *
        adjustedSlotSource Q B N H b (blockInput B) e t) = _
  simp_rw [adjustedSlotSource_eq_hybrid_terms, mul_add]
  unfold centeredPrincipalCorrelation nonprincipalPrimitiveCorrelation
    exceptionalPowerCorrelation
  simp only [Finset.sum_add_distrib]

/-- Finite support-aware Cauchy--Schwarz adapter. -/
theorem supported_correlation_sq_le
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (P : ι → Prop) [DecidablePred P] (a c : ι → ℂ)
    (hc : ∀ i, ¬ P i → c i = 0) :
    ‖∑ i : ι, a i * c i‖ ^ 2 ≤
      (∑ i : ι, if P i then ‖a i‖ ^ 2 else 0) *
        ∑ i : ι, ‖c i‖ ^ 2 := by
  have hrewrite : (∑ i : ι, a i * c i) =
      ∑ i : ι, (if P i then a i else 0) * c i := by
    apply Finset.sum_congr rfl
    intro i _hi
    by_cases hPi : P i
    · simp [hPi]
    · simp [hPi, hc i hPi]
  rw [hrewrite]
  have htriangle :
      ‖∑ i : ι, (if P i then a i else 0) * c i‖ ≤
        ∑ i : ι, ‖if P i then a i else 0‖ * ‖c i‖ := by
    calc
      _ ≤ ∑ i : ι, ‖(if P i then a i else 0) * c i‖ := norm_sum_le _ _
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i _hi
        rw [norm_mul]
  have hsq := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr htriangle
  apply hsq.trans
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun i : ι => ‖if P i then a i else 0‖)
    (fun i : ι => ‖c i‖)
  apply hcs.trans_eq
  congr 1
  apply Finset.sum_congr rfl
  intro i _hi
  by_cases hPi : P i <;> simp [hPi]

theorem centeredPrincipalCorrelation_sq_le
    (Q B N : ℕ) (H : ℝ) (w : ℕ → ℂ) :
    ‖centeredPrincipalCorrelation Q B N H w‖ ^ 2 ≤
      centeredPrincipalCoefficientEnergy Q N w *
        centeredPrincipalSourceEnergy Q B N H := by
  unfold centeredPrincipalCorrelation centeredPrincipalCoefficientEnergy
    centeredPrincipalSourceEnergy
  exact supported_correlation_sq_le
    (fun t : CharacterSlot Q => t.1.val = 1)
    (fun t => windowCoefficient t.1 N w t.2)
    (fun t => centeredPrincipalSlotSource Q B N H t)
    (by intro t ht; simp [centeredPrincipalSlotSource, ht])

theorem nonprincipalPrimitiveCorrelation_sq_le
    (Q B N : ℕ) (H : ℝ) (w : ℕ → ℂ) :
    ‖nonprincipalPrimitiveCorrelation Q B N H w‖ ^ 2 ≤
      nonprincipalCoefficientEnergy Q N w *
        nonprincipalPrimitiveSourceEnergy Q B N H := by
  unfold nonprincipalPrimitiveCorrelation nonprincipalCoefficientEnergy
    nonprincipalPrimitiveSourceEnergy
  simpa only [ne_eq, ite_not] using
    (supported_correlation_sq_le
      (fun t : CharacterSlot Q => t.1.val ≠ 1)
      (fun t => windowCoefficient t.1 N w t.2)
      (fun t => nonprincipalPrimitiveSlotSource Q B N H t)
      (by
        intro t ht
        push Not at ht
        simp [nonprincipalPrimitiveSlotSource, ht]))

/-- Hybrid three-channel energy bound.  Its first factor contains the true
principal discrepancy rather than separate primitive and constant masses. -/
theorem adjustedCenteredError_sq_le_hybrid
    (Q B N : ℕ) (H b : ℝ) (w : ℕ → ℂ)
    (hH : 1 ≤ H) (hb : 0 ≤ b) (e : CharacterSlot Q) :
    ‖adjustedCenteredError Q B N H b (blockInput B) w e‖ ^ 2 ≤
      3 * (centeredPrincipalCoefficientEnergy Q N w *
            centeredPrincipalSourceEnergy Q B N H +
          nonprincipalCoefficientEnergy Q N w *
            nonprincipalPrimitiveSourceEnergy Q B N H +
          (9 / 4 : ℝ) * ‖windowCoefficient e.1 N w e.2‖ ^ 2) := by
  rw [adjustedCenteredError_eq_hybrid_correlations]
  calc
    _ ≤ 3 * (‖centeredPrincipalCorrelation Q B N H w‖ ^ 2 +
          ‖nonprincipalPrimitiveCorrelation Q B N H w‖ ^ 2 +
          ‖exceptionalPowerCorrelation Q B N H b w e‖ ^ 2) :=
      GoldbachCircleMethodAdjustedSourceThreeTermDecompositionV18479.norm_add_add_sq_le_three _ _ _
    _ ≤ _ := by
      gcongr
      · exact centeredPrincipalCorrelation_sq_le Q B N H w
      · exact nonprincipalPrimitiveCorrelation_sq_le Q B N H w
      · exact exceptionalPowerCorrelation_sq_le_single_coefficient
          Q B N H b w hH hb e

end GoldbachCircleMethodHybridCenteredCorrelationEnergyV18501
