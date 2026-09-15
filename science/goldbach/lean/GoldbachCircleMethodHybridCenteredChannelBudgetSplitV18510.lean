import GoldbachCircleMethodHybridCenteredSingleSourceGateV18509
import GoldbachCircleMethodRemovedConvolutionNormV18123

/-!
# Goldbach V1.8.510: hybrid-centered channel budget split

The single hybrid source gate is split into three named block budgets.  The
principal budget is bounded from the explicit centered-discrepancy interface;
the nonprincipal primitive and exceptional budgets remain visible and are not
silently absorbed.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodHybridCenteredChannelBudgetSplitV18510

open GoldbachCircleMethodActiveExceptionalCenteringV18129
open GoldbachCircleMethodCenteredPrincipalDecayInterfaceV18503
open GoldbachCircleMethodCenteredPrincipalNetExponentV18504
open GoldbachCircleMethodFiniteIntervalRemainderReserveV18229
open GoldbachCircleMethodHybridCenteredCentralMomentV18505
open GoldbachCircleMethodHybridCenteredCorrelationEnergyV18501
open GoldbachCircleMethodLogCutoffPresieveBindingV18120
open GoldbachCircleMethodPrincipalWindowBoundaryV18121
open GoldbachCircleMethodRemovedConvolutionNormV18123
open GoldbachCircleMethodCanonicalBumpPrincipalFloorV18220

noncomputable def hybridPrincipalBlockBudget (B : ℕ) (rho : ℝ) : ℝ :=
  let Q := centeredPrincipalCutoff B rho
  let H := centeredPrincipalScale B rho
  let w := logWeight ((B : ℝ) ^ rho) canonicalLogBump
  ∑ n ∈ blockCarrier B,
    centeredPrincipalCoefficientEnergy Q n w *
      centeredPrincipalSourceEnergy Q B n H

noncomputable def hybridNonprincipalBlockBudget (B : ℕ) (rho : ℝ) : ℝ :=
  let Q := centeredPrincipalCutoff B rho
  let H := centeredPrincipalScale B rho
  let w := logWeight ((B : ℝ) ^ rho) canonicalLogBump
  ∑ n ∈ blockCarrier B,
    nonprincipalCoefficientEnergy Q n w *
      nonprincipalPrimitiveSourceEnergy Q B n H

noncomputable def hybridExceptionalBlockBudget
    (B : ℕ) (rho : ℝ)
    (e : CharacterSlot (centeredPrincipalCutoff B rho)) : ℝ :=
  let w := logWeight ((B : ℝ) ^ rho) canonicalLogBump
  ∑ n ∈ blockCarrier B, (9 / 4 : ℝ) * ‖windowCoefficient e.1 n w e.2‖ ^ 2

/-- Exact three-way identity for the source gate. -/
theorem hybridCenteredSourceBudget_eq_channel_sum
    (B : ℕ) (rho b : ℝ)
    (e : CharacterSlot (centeredPrincipalCutoff B rho)) :
    hybridCenteredSourceBudget B rho b e =
      hybridPrincipalBlockBudget B rho +
        hybridNonprincipalBlockBudget B rho +
          hybridExceptionalBlockBudget B rho e := by
  unfold hybridCenteredSourceBudget hybridPrincipalBlockBudget
    hybridNonprincipalBlockBudget hybridExceptionalBlockBudget
    centeredPrincipalCutoff centeredPrincipalScale
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]

theorem hybridPrincipalBlockBudget_nonneg (B : ℕ) (rho : ℝ) :
    0 ≤ hybridPrincipalBlockBudget B rho := by
  unfold hybridPrincipalBlockBudget
  apply Finset.sum_nonneg
  intro n _hn
  have hc : 0 ≤ centeredPrincipalCoefficientEnergy
      (centeredPrincipalCutoff B rho) n
      (logWeight ((B : ℝ) ^ rho) canonicalLogBump) := by
    unfold centeredPrincipalCoefficientEnergy
    positivity
  have hs : 0 ≤ centeredPrincipalSourceEnergy
      (centeredPrincipalCutoff B rho) B n
      (centeredPrincipalScale B rho) := by
    unfold centeredPrincipalSourceEnergy
    positivity
  positivity

theorem hybridNonprincipalBlockBudget_nonneg (B : ℕ) (rho : ℝ) :
    0 ≤ hybridNonprincipalBlockBudget B rho := by
  unfold hybridNonprincipalBlockBudget
  apply Finset.sum_nonneg
  intro n _hn
  have hc : 0 ≤ nonprincipalCoefficientEnergy
      (centeredPrincipalCutoff B rho) n
      (logWeight ((B : ℝ) ^ rho) canonicalLogBump) := by
    unfold nonprincipalCoefficientEnergy
    positivity
  have hs : 0 ≤ nonprincipalPrimitiveSourceEnergy
      (centeredPrincipalCutoff B rho) B n
      (centeredPrincipalScale B rho) := by
    unfold nonprincipalPrimitiveSourceEnergy
    positivity
  positivity

theorem hybridExceptionalBlockBudget_nonneg
    (B : ℕ) (rho : ℝ)
    (e : CharacterSlot (centeredPrincipalCutoff B rho)) :
    0 ≤ hybridExceptionalBlockBudget B rho e := by
  unfold hybridExceptionalBlockBudget
  positivity

/-- Pointwise discrepancy decay controls the entire principal block.  The
factor `B` is the exact cost of summing over at most `B` targets; the cutoff
cost remains explicit here. -/
theorem hybridPrincipalBlockBudget_le_explicit
    (C rho sigma : ℝ) (hC : 0 ≤ C) (hrho : 0 < rho)
    (hestimate : CenteredPrincipalDiscrepancyEstimate C rho sigma)
    (B : ℕ) (hB : 3 ≤ B) :
    hybridPrincipalBlockBudget B rho ≤
      (B : ℝ) *
        ((centeredPrincipalCutoff B rho : ℝ) ^ 2 *
          (C * (B : ℝ) ^ (-sigma)) ^ 2) := by
  let Q := centeredPrincipalCutoff B rho
  let H := centeredPrincipalScale B rho
  let w := logWeight ((B : ℝ) ^ rho) canonicalLogBump
  have hQ : 1 ≤ Q := centeredPrincipalCutoff_pos B hB rho hrho
  have hconstantNonneg :
      0 ≤ (Q : ℝ) ^ 2 * (C * (B : ℝ) ^ (-sigma)) ^ 2 := by
    positivity
  unfold hybridPrincipalBlockBudget
  dsimp only [Q, H, w]
  calc
    (∑ n ∈ blockCarrier B,
        centeredPrincipalCoefficientEnergy Q n w *
          centeredPrincipalSourceEnergy Q B n H) ≤
      ∑ _n ∈ blockCarrier B,
        (Q : ℝ) ^ 2 * (C * (B : ℝ) ^ (-sigma)) ^ 2 := by
      apply Finset.sum_le_sum
      intro n hn
      apply mul_le_mul
      · exact centeredPrincipalCoefficientEnergy_le_cutoff_sq Q n hQ w
          (norm_logWeight_canonical_le_one ((B : ℝ) ^ rho))
      · exact centeredPrincipalSourceEnergy_le_of_estimate
          C rho sigma hC hestimate Q B n hQ hB hn
      · unfold centeredPrincipalSourceEnergy
        positivity
      · positivity
    _ = ((blockCarrier B).card : ℝ) *
        ((Q : ℝ) ^ 2 * (C * (B : ℝ) ^ (-sigma)) ^ 2) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (B : ℝ) *
        ((Q : ℝ) ^ 2 * (C * (B : ℝ) ^ (-sigma)) ^ 2) := by
      apply mul_le_mul_of_nonneg_right _ hconstantNonneg
      exact_mod_cast block_carrier_card_le B

end GoldbachCircleMethodHybridCenteredChannelBudgetSplitV18510
