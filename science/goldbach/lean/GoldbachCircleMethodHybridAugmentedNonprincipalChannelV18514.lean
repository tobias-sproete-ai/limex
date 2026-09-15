import GoldbachCircleMethodHybridChannelEndToEndReductionV18513

/-!
# Goldbach V1.8.514: augmented nonprincipal channel

A structurally admissible exceptional slot has conductor greater than one.
Its coefficient atom is therefore already contained in the nonprincipal
coefficient energy.  This module absorbs the separate exceptional coefficient
term into one augmented nonprincipal budget without an extra analytic
interface.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodHybridAugmentedNonprincipalChannelV18514

open GoldbachCircleMethodActiveExceptionalCenteringV18129
open GoldbachCircleMethodCenteredPrincipalDecayInterfaceV18503
open GoldbachCircleMethodCenteredPrincipalNetExponentV18504
open GoldbachCircleMethodHybridCenteredCentralMomentV18505
open GoldbachCircleMethodHybridCenteredChannelBudgetSplitV18510
open GoldbachCircleMethodHybridCenteredCorrelationEnergyV18501
open GoldbachCircleMethodHybridPrincipalBlockExponentV18511
open GoldbachCircleMethodLogCutoffPresieveBindingV18120
open GoldbachCircleMethodPrincipalWindowBoundaryV18121
open GoldbachCircleMethodStructurallyAdmissibleActiveSlotV18258
open GoldbachCircleMethodCanonicalBumpPrincipalFloorV18220

/-- The selected admissible atom is one term of the nonprincipal coefficient
energy. -/
theorem selected_coefficient_sq_le_nonprincipalCoefficientEnergy
    (Q N : ℕ) (w : ℕ → ℂ)
    (e : StructurallyAdmissibleActiveSlot Q) :
    ‖windowCoefficient e.val.1 N w e.val.2‖ ^ 2 ≤
      nonprincipalCoefficientEnergy Q N w := by
  have he : e.val.1.val ≠ 1 := admissible_conductor_ne_one e
  unfold nonprincipalCoefficientEnergy
  have hnonneg (t : CharacterSlot Q) (_ht : t ∈ (Finset.univ : Finset (CharacterSlot Q))) :
      0 ≤ if t.1.val = 1 then 0 else ‖windowCoefficient t.1 N w t.2‖ ^ 2 := by
    split_ifs <;> positivity
  have hsingle := Finset.single_le_sum hnonneg (Finset.mem_univ e.val)
  simpa only [he, if_false] using hsingle

/-- The nonprincipal source energy augmented by the uniform exceptional-source
constant.  This budget is independent of which admissible slot is selected. -/
noncomputable def hybridAugmentedNonprincipalBlockBudget
    (B : ℕ) (rho : ℝ) : ℝ :=
  let Q := centeredPrincipalCutoff B rho
  let H := centeredPrincipalScale B rho
  let w := logWeight ((B : ℝ) ^ rho) canonicalLogBump
  ∑ n ∈ blockCarrier B,
    nonprincipalCoefficientEnergy Q n w *
      (nonprincipalPrimitiveSourceEnergy Q B n H + (9 / 4 : ℝ))

/-- The former nonprincipal and selected-exceptional budgets are jointly
bounded by the augmented channel. -/
theorem nonprincipal_add_exceptional_le_augmented
    (B : ℕ) (rho : ℝ)
    (e : StructurallyAdmissibleActiveSlot (centeredPrincipalCutoff B rho)) :
    hybridNonprincipalBlockBudget B rho +
        hybridExceptionalBlockBudget B rho e.val ≤
      hybridAugmentedNonprincipalBlockBudget B rho := by
  unfold hybridNonprincipalBlockBudget hybridExceptionalBlockBudget
    hybridAugmentedNonprincipalBlockBudget
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro n _hn
  have hselected := selected_coefficient_sq_le_nonprincipalCoefficientEnergy
    (centeredPrincipalCutoff B rho) n
    (logWeight ((B : ℝ) ^ rho) canonicalLogBump) e
  calc
    nonprincipalCoefficientEnergy (centeredPrincipalCutoff B rho) n
          (logWeight ((B : ℝ) ^ rho) canonicalLogBump) *
          nonprincipalPrimitiveSourceEnergy (centeredPrincipalCutoff B rho) B n
            (centeredPrincipalScale B rho) +
        (9 / 4 : ℝ) *
          ‖windowCoefficient e.val.1 n
            (logWeight ((B : ℝ) ^ rho) canonicalLogBump) e.val.2‖ ^ 2 ≤
      nonprincipalCoefficientEnergy (centeredPrincipalCutoff B rho) n
          (logWeight ((B : ℝ) ^ rho) canonicalLogBump) *
          nonprincipalPrimitiveSourceEnergy (centeredPrincipalCutoff B rho) B n
            (centeredPrincipalScale B rho) +
        (9 / 4 : ℝ) *
          nonprincipalCoefficientEnergy (centeredPrincipalCutoff B rho) n
            (logWeight ((B : ℝ) ^ rho) canonicalLogBump) := by
      gcongr
    _ = nonprincipalCoefficientEnergy (centeredPrincipalCutoff B rho) n
          (logWeight ((B : ℝ) ^ rho) canonicalLogBump) *
        (nonprincipalPrimitiveSourceEnergy (centeredPrincipalCutoff B rho) B n
          (centeredPrincipalScale B rho) + (9 / 4 : ℝ)) := by ring

/-- The full hybrid source is bounded by only two channels. -/
theorem hybridCenteredSourceBudget_le_principal_add_augmented
    (B : ℕ) (rho b : ℝ)
    (e : StructurallyAdmissibleActiveSlot (centeredPrincipalCutoff B rho)) :
    hybridCenteredSourceBudget B rho b e.val ≤
      hybridPrincipalBlockBudget B rho +
        hybridAugmentedNonprincipalBlockBudget B rho := by
  rw [hybridCenteredSourceBudget_eq_channel_sum B rho b e.val]
  have hrest := nonprincipal_add_exceptional_le_augmented B rho e
  linarith

/-- Open analytic target for the sole remaining nonprincipal source channel. -/
def AugmentedNonprincipalBlockEstimate
    (Ca rho s : ℝ) : Prop :=
  ∀ (B : ℕ), 3 ≤ B →
    hybridAugmentedNonprincipalBlockBudget B rho ≤ Ca * (B : ℝ) ^ s

/-- Principal discrepancy decay plus one augmented nonprincipal estimate
imply the entire source gate. -/
theorem hybridCenteredSourceBudget_le_of_two_channel_estimates
    (C Ca rho sigma s : ℝ) (hC : 0 ≤ C) (hrho : 0 < rho)
    (hprincipal : CenteredPrincipalDiscrepancyEstimate C rho sigma)
    (haugmented : AugmentedNonprincipalBlockEstimate Ca rho s)
    (hexponent : 1 + 4 * rho - 2 * sigma ≤ s)
    (B : ℕ) (hB : 3 ≤ B) (b : ℝ)
    (e : StructurallyAdmissibleActiveSlot (centeredPrincipalCutoff B rho)) :
    hybridCenteredSourceBudget B rho b e.val ≤
      (C ^ 2 + Ca) * (B : ℝ) ^ s := by
  have hbase : (1 : ℝ) ≤ B := by exact_mod_cast (show 1 ≤ B by omega)
  have hpower : (B : ℝ) ^ (1 + 4 * rho - 2 * sigma) ≤
      (B : ℝ) ^ s :=
    Real.rpow_le_rpow_of_exponent_le hbase hexponent
  have hpRaw := hybridPrincipalBlockBudget_le_net_power
    C rho sigma hC hrho hprincipal B hB
  have hp : hybridPrincipalBlockBudget B rho ≤ C ^ 2 * (B : ℝ) ^ s :=
    hpRaw.trans (mul_le_mul_of_nonneg_left hpower (sq_nonneg C))
  have ha := haugmented B hB
  calc
    hybridCenteredSourceBudget B rho b e.val ≤
        hybridPrincipalBlockBudget B rho +
          hybridAugmentedNonprincipalBlockBudget B rho :=
      hybridCenteredSourceBudget_le_principal_add_augmented B rho b e
    _ ≤ C ^ 2 * (B : ℝ) ^ s + Ca * (B : ℝ) ^ s := add_le_add hp ha
    _ = (C ^ 2 + Ca) * (B : ℝ) ^ s := by ring

end GoldbachCircleMethodHybridAugmentedNonprincipalChannelV18514
