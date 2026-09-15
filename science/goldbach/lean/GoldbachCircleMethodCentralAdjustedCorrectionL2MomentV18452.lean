import GoldbachCircleMethodAdjustedCorrectionL2CompositionV18451
import GoldbachCircleMethodCanonicalCentralAdjustedPositiveV18403

/-!
# Goldbach V1.8.452: central adjusted-correction L2 moment

The two-level finite energy bound is summed over the unchanged central target
sweep `10m, 10m+2, ..., 14m`.  A threshold exceptional set is controlled by
the resulting target moment.  This is an exact averaged interface and does not
claim the analytic energy budget required to make the exceptional set small.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodCentralAdjustedCorrectionL2MomentV18452

open GoldbachCircleMethodActiveExceptionalCenteringV18129
open GoldbachCircleMethodActiveResidualExactDecompositionV18251
open GoldbachCircleMethodAdjustedCorrectionL2CompositionV18451
open GoldbachCircleMethodCanonicalCentralAdjustedPositiveV18403
open GoldbachCircleMethodStructurallyAdmissibleActiveSlotV18258

/-- Exact squared correction mass on the canonical central sweep. -/
noncomputable def centralAdjustedCorrectionEnergy
    (m : ℕ) (rho b : ℝ)
    (e : StructurallyAdmissibleActiveSlot
      ⌊(((8 * m : ℕ) : ℝ)^rho)^2⌋₊) : ℝ :=
  ∑ i ∈ Finset.range (2 * m + 1),
    ‖canonicalAdjustedCenteredErrorCorrectionAt
      (8 * m) rho b e.val (centralTargetNat m i : ℤ)‖ ^ 2

/-- Exact sum of partner energies on the same central sweep. -/
noncomputable def centralAdjustedPartnerEnergy
    (m : ℕ) (rho b : ℝ)
    (e : StructurallyAdmissibleActiveSlot
      ⌊(((8 * m : ℕ) : ℝ)^rho)^2⌋₊) : ℝ :=
  ∑ i ∈ Finset.range (2 * m + 1),
    adjustedCorrectionPartnerEnergy
      (8 * m) (centralTargetNat m i) rho b e.val

/-- The targetwise source energy is independent of the convolution target;
therefore it factors exactly outside the central target sum. -/
theorem central_adjusted_correction_energy_le_factored_energy
    (m : ℕ) (rho b : ℝ)
    (e : StructurallyAdmissibleActiveSlot
      ⌊(((8 * m : ℕ) : ℝ)^rho)^2⌋₊) :
    centralAdjustedCorrectionEnergy m rho b e ≤
      adjustedSlotEnergyProductSourceSum (8 * m) rho b e.val *
        centralAdjustedPartnerEnergy m rho b e := by
  unfold centralAdjustedCorrectionEnergy centralAdjustedPartnerEnergy
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _hi
  apply canonical_adjusted_centered_correction_sq_le_energy_product
  simp only [centralTargetNat]
  omega

/-- Indices in the central sweep whose literal correction exceeds `T`. -/
noncomputable def centralAdjustedCorrectionBadIndices
    (m : ℕ) (rho b T : ℝ)
    (e : StructurallyAdmissibleActiveSlot
      ⌊(((8 * m : ℕ) : ℝ)^rho)^2⌋₊) : Finset ℕ :=
  (Finset.range (2 * m + 1)).filter (fun i =>
    T < ‖canonicalAdjustedCenteredErrorCorrectionAt
      (8 * m) rho b e.val (centralTargetNat m i : ℤ)‖)

/-- Finite Chebyshev bound for the central correction exceptional set. -/
theorem central_bad_card_mul_threshold_sq_le_correction_energy
    (m : ℕ) (rho b T : ℝ)
    (e : StructurallyAdmissibleActiveSlot
      ⌊(((8 * m : ℕ) : ℝ)^rho)^2⌋₊) (hT : 0 ≤ T) :
    ((centralAdjustedCorrectionBadIndices m rho b T e).card : ℝ) * T ^ 2 ≤
      centralAdjustedCorrectionEnergy m rho b e := by
  let bad := centralAdjustedCorrectionBadIndices m rho b T e
  have hsubset : bad ⊆ Finset.range (2 * m + 1) := by
    intro i hi
    exact (Finset.mem_filter.mp hi).1
  have hpoint (i : ℕ) (hi : i ∈ bad) :
      T ^ 2 ≤ ‖canonicalAdjustedCenteredErrorCorrectionAt
        (8 * m) rho b e.val (centralTargetNat m i : ℤ)‖ ^ 2 := by
    have hlt : T < ‖canonicalAdjustedCenteredErrorCorrectionAt
        (8 * m) rho b e.val (centralTargetNat m i : ℤ)‖ :=
      (Finset.mem_filter.mp hi).2
    exact (sq_le_sq₀ hT (norm_nonneg _)).mpr hlt.le
  calc
    (bad.card : ℝ) * T ^ 2 = ∑ i ∈ bad, T ^ 2 := by simp
    _ ≤ ∑ i ∈ bad,
        ‖canonicalAdjustedCenteredErrorCorrectionAt
          (8 * m) rho b e.val (centralTargetNat m i : ℤ)‖ ^ 2 := by
      exact Finset.sum_le_sum (fun i hi => hpoint i hi)
    _ ≤ ∑ i ∈ Finset.range (2 * m + 1),
        ‖canonicalAdjustedCenteredErrorCorrectionAt
          (8 * m) rho b e.val (centralTargetNat m i : ℤ)‖ ^ 2 := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
        (fun i _hi _hnot => sq_nonneg
          ‖canonicalAdjustedCenteredErrorCorrectionAt
            (8 * m) rho b e.val (centralTargetNat m i : ℤ)‖)
    _ = centralAdjustedCorrectionEnergy m rho b e := rfl

/-- Final exact central exceptional-set interface in factored energy form. -/
theorem central_bad_card_mul_threshold_sq_le_factored_energy
    (m : ℕ) (rho b T : ℝ)
    (e : StructurallyAdmissibleActiveSlot
      ⌊(((8 * m : ℕ) : ℝ)^rho)^2⌋₊) (hT : 0 ≤ T) :
    ((centralAdjustedCorrectionBadIndices m rho b T e).card : ℝ) * T ^ 2 ≤
      adjustedSlotEnergyProductSourceSum (8 * m) rho b e.val *
        centralAdjustedPartnerEnergy m rho b e :=
  (central_bad_card_mul_threshold_sq_le_correction_energy
    m rho b T e hT).trans
      (central_adjusted_correction_energy_le_factored_energy m rho b e)

end GoldbachCircleMethodCentralAdjustedCorrectionL2MomentV18452
