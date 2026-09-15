import GoldbachCircleMethodAdjustedModelReserveInterfaceV18256

/-!
# Goldbach V1.8.257: arbitrary active-slot negative witness

The raw `CharacterSlot` interface contains the conductor-one principal
character.  With coefficient `b=0`, selecting that slot cancels the principal
model identically.  Hence no positive adjusted-model reserve can be uniform
over all raw slots.  A source-matched exceptional-slot predicate is mandatory.
-/

open scoped BigOperators Classical

set_option autoImplicit false

namespace GoldbachCircleMethodArbitraryActiveSlotNegativeWitnessV18257

open GoldbachCircleMethodFiniteResiduePrefixV1866
open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodFiniteCompanionBindingV18118
open GoldbachCircleMethodLogCutoffPresieveBindingV18120
open GoldbachCircleMethodPrincipalWindowBoundaryV18121
open GoldbachCircleMethodExceptionalWeightBoundaryV18128
open GoldbachCircleMethodActiveExceptionalCenteringV18129
open GoldbachCircleMethodSupportedModelErrorConvolutionV18182
open GoldbachCircleMethodSupportedResidualParsevalV18190
open GoldbachCircleMethodCanonicalBumpPrincipalFloorV18220
open GoldbachCircleMethodActualResidualExactDecompositionV18225
open GoldbachCircleMethodActiveResidualExactDecompositionV18251
open GoldbachCircleMethodAdjustedModelSecondaryTermExpansionV18255
open GoldbachCircleMethodAdjustedModelReserveInterfaceV18256

/-- The conductor-one principal character is a literal member of every raw
character family whose cutoff contains one. -/
noncomputable def principalCharacterSlot (Q : ℕ) (hQ : 1 ≤ Q) :
    CharacterSlot Q := by
  refine ⟨oneLevel hQ, ?_⟩
  change {χ : DirichletCharacter ℂ 1 // χ.IsPrimitive}
  exact ⟨1, DirichletCharacter.isPrimitive_one_level_one⟩

theorem principalSlot_windowCoefficient_eq_finiteCompanion
    (Q N : ℕ) (hQ : 1 ≤ Q) (w : ℕ → ℂ) :
    windowCoefficient (principalCharacterSlot Q hQ).1 N w
        (principalCharacterSlot Q hQ).2 =
      finiteCompanion (oneLevel hQ) N w := by
  have hchi :
      (principalCharacterSlot Q hQ).2.val
          (N : ZMod (principalCharacterSlot Q hQ).1.val) = 1 := by
    change (1 : DirichletCharacter ℂ 1) (N : ZMod 1) = 1
    exact level_one_character_value (1 : DirichletCharacter ℂ 1) N
  have hr : (principalCharacterSlot Q hQ).1 = oneLevel hQ := rfl
  unfold windowCoefficient
  rw [hchi, hr]
  simp only [oneLevel, Nat.totient_one, Nat.cast_one, div_one, one_mul]

/-- At `b=0`, the raw principal slot cancels the adjusted model exactly. -/
theorem adjustedModel_principalSlot_zero
    (Q N : ℕ) (hQ : 1 ≤ Q) (w : ℕ → ℂ) :
    adjustedModel Q N hQ 0 w (principalCharacterSlot Q hQ) = 0 := by
  unfold adjustedModel
  rw [principalSlot_windowCoefficient_eq_finiteCompanion]
  simp [powerWeight]

/-- Supported cancellation on the full natural carrier. -/
theorem supportedAdjustedModel_principalSlot_zero
    (M N : ℕ) (R : ℝ) (hR : 1 < R) (G : ℝ → ℝ) :
    supportedAdjustedModel M N R 0 G
        (principalCharacterSlot ⌊R^2⌋₊ (log_cutoff_contains_one R hR)) = 0 := by
  unfold supportedAdjustedModel
  rw [dif_pos hR]
  by_cases hN : N ∈ Finset.Ioc (M / 2) M
  · rw [if_pos hN]
    exact adjustedModel_principalSlot_zero
      ⌊R^2⌋₊ N (log_cutoff_contains_one R hR) (logWeight R G)
  · rw [if_neg hN]

/-- Therefore the complete adjusted-model self-convolution vanishes for the
raw principal slot. -/
theorem canonicalAdjustedModelAt_principalSlot_zero
    (B : ℕ) (rho : ℝ) (hR2 : 2 ≤ (B : ℝ)^rho) (k : ℤ) :
    canonicalAdjustedModelAt B rho 0
        (principalCharacterSlot ⌊((B : ℝ)^rho)^2⌋₊
          (log_cutoff_contains_one ((B : ℝ)^rho) (by linarith))) k = 0 := by
  unfold canonicalAdjustedModelAt integerPairConvolution
  have hR : 1 < (B : ℝ)^rho := by linarith
  simp_rw [supportedAdjustedModel_principalSlot_zero
    B _ ((B : ℝ)^rho) hR canonicalLogBump]
  simp

/-- Concrete impossibility of a strictly positive reserve uniformly over raw
`CharacterSlot`: the principal slot at `b=0` is a counterexample. -/
theorem not_all_raw_active_slots_have_positive_adjusted_model
    (B : ℕ) (rho : ℝ) (hR2 : 2 ≤ (B : ℝ)^rho) (k : ℤ) :
    ¬ (∀ (b : ℝ) (e : CharacterSlot ⌊((B : ℝ)^rho)^2⌋₊),
        0 < (canonicalAdjustedModelAt B rho b e k).re) := by
  intro hAll
  let e := principalCharacterSlot ⌊((B : ℝ)^rho)^2⌋₊
    (log_cutoff_contains_one ((B : ℝ)^rho) (by linarith))
  have hPos := hAll 0 e
  have hZero := canonicalAdjustedModelAt_principalSlot_zero B rho hR2 k
  rw [hZero] at hPos
  norm_num at hPos

/-- At a target with a positive principal reserve, the V1.8.256 secondary
budget is necessarily false for the raw principal slot. -/
theorem principalSlot_secondary_budget_fails_at_positive_reserve
    (M B : ℕ) (rho : ℝ) (hR2 : 2 ≤ (B : ℝ)^rho) (k : ℤ)
    (hM : 0 < M)
    (hPrincipal : (M : ℝ) / 512 < (canonicalPrincipalModelAt B rho k).re) :
    ¬ (2 * |(canonicalPrincipalSecondaryCrossAt B rho 0
          (principalCharacterSlot ⌊((B : ℝ)^rho)^2⌋₊
            (log_cutoff_contains_one ((B : ℝ)^rho) (by linarith))) k).re| +
        |(canonicalActiveSecondarySquareAt B rho 0
          (principalCharacterSlot ⌊((B : ℝ)^rho)^2⌋₊
            (log_cutoff_contains_one ((B : ℝ)^rho) (by linarith))) k).re| <
      (M : ℝ) / 1024) := by
  intro hBudget
  let e := principalCharacterSlot ⌊((B : ℝ)^rho)^2⌋₊
    (log_cutoff_contains_one ((B : ℝ)^rho) (by linarith))
  have hAdjusted := adjustedModel_re_gt_target_over_1024_of_secondary_budget
    M B rho 0 e k hPrincipal hBudget
  have hZero := canonicalAdjustedModelAt_principalSlot_zero B rho hR2 k
  rw [hZero] at hAdjusted
  simp only [Complex.zero_re] at hAdjusted
  have hMReal : 0 < (M : ℝ) := by exact_mod_cast hM
  linarith

end GoldbachCircleMethodArbitraryActiveSlotNegativeWitnessV18257
