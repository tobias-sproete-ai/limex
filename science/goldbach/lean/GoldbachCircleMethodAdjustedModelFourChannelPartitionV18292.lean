import GoldbachCircleMethodDivisorLocalizedActivePeriodicityV18291

/-!
# Goldbach V1.8.292: adjusted-model four-channel partition

The exact factor split of V1.8.290 is propagated through the actual pair
convolution.  The localized-localized contribution is isolated from the two
cross terms and the off-divisor/off-divisor term without deleting any part of
the supported adjusted model.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodAdjustedModelFourChannelPartitionV18292

open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodActiveExceptionalCenteringV18129
open GoldbachCircleMethodBlockPairCarrierV18227
open GoldbachCircleMethodSupportedAdjustedModelBindingAuditV18285
open GoldbachCircleMethodActiveConductorDivisorLocalizationV18290

/-- Localized-localized kernel. -/
noncomputable def localizedLocalizedKernel {Q : ℕ} (hQ : 1 ≤ Q)
    (e : CharacterSlot Q) (N n : ℕ) (b : ℝ) (w : ℕ → ℂ) : ℂ :=
  divisorLocalizedAdjustedFactor hQ e.1 e.2 n b w *
    divisorLocalizedAdjustedFactor hQ e.1 e.2 (N-n) b w

/-- Localized/off-divisor cross kernel. -/
noncomputable def localizedOffDivisorKernel {Q : ℕ} (hQ : 1 ≤ Q)
    (e : CharacterSlot Q) (N n : ℕ) (b : ℝ) (w : ℕ → ℂ) : ℂ :=
  divisorLocalizedAdjustedFactor hQ e.1 e.2 n b w *
    offDivisorAdjustedFactor hQ e.1 e.2 (N-n) b w

/-- Off-divisor/localized cross kernel. -/
noncomputable def offDivisorLocalizedKernel {Q : ℕ} (hQ : 1 ≤ Q)
    (e : CharacterSlot Q) (N n : ℕ) (b : ℝ) (w : ℕ → ℂ) : ℂ :=
  offDivisorAdjustedFactor hQ e.1 e.2 n b w *
    divisorLocalizedAdjustedFactor hQ e.1 e.2 (N-n) b w

/-- Off-divisor/off-divisor kernel. -/
noncomputable def offDivisorOffDivisorKernel {Q : ℕ} (hQ : 1 ≤ Q)
    (e : CharacterSlot Q) (N n : ℕ) (b : ℝ) (w : ℕ → ℂ) : ℂ :=
  offDivisorAdjustedFactor hQ e.1 e.2 n b w *
    offDivisorAdjustedFactor hQ e.1 e.2 (N-n) b w

/-- Exact pointwise four-channel expansion. -/
theorem amplitudeAdjustedPairKernel_eq_four_channels {Q : ℕ}
    (hQ : 1 ≤ Q) (e : CharacterSlot Q)
    (N n : ℕ) (b : ℝ) (w : ℕ → ℂ) :
    amplitudeAdjustedPairKernel hQ e N n b w =
      localizedLocalizedKernel hQ e N n b w +
      localizedOffDivisorKernel hQ e N n b w +
      offDivisorLocalizedKernel hQ e N n b w +
      offDivisorOffDivisorKernel hQ e N n b w := by
  unfold amplitudeAdjustedPairKernel localizedLocalizedKernel
    localizedOffDivisorKernel offDivisorLocalizedKernel
    offDivisorOffDivisorKernel
  rw [amplitudeAdjustedFactor_eq_divisorLocalized_add_offDivisor,
    amplitudeAdjustedFactor_eq_divisorLocalized_add_offDivisor]
  ring

/-- Sum of the localized-localized channel over the literal pair carrier. -/
noncomputable def localizedLocalizedPairSum {Q : ℕ} (hQ : 1 ≤ Q)
    (J : Finset ℕ) (e : CharacterSlot Q) (N : ℕ)
    (b : ℝ) (w : ℕ → ℂ) : ℂ :=
  ∑ n ∈ pairFirstCarrier J N, localizedLocalizedKernel hQ e N n b w

/-- Sum of all three channels containing at least one off-divisor factor. -/
noncomputable def offDivisorPairRemainder {Q : ℕ} (hQ : 1 ≤ Q)
    (J : Finset ℕ) (e : CharacterSlot Q) (N : ℕ)
    (b : ℝ) (w : ℕ → ℂ) : ℂ :=
  ∑ n ∈ pairFirstCarrier J N,
    (localizedOffDivisorKernel hQ e N n b w +
      offDivisorLocalizedKernel hQ e N n b w +
      offDivisorOffDivisorKernel hQ e N n b w)

/-- Exact pair-sum decomposition into the periodic candidate channel and its
full off-divisor remainder. -/
theorem amplitudeAdjustedFullPairSum_eq_localized_add_offDivisorRemainder
    {Q : ℕ} (hQ : 1 ≤ Q) (J : Finset ℕ) (e : CharacterSlot Q)
    (N : ℕ) (b : ℝ) (w : ℕ → ℂ) :
    amplitudeAdjustedFullPairSum hQ J e N b w =
      localizedLocalizedPairSum hQ J e N b w +
        offDivisorPairRemainder hQ J e N b w := by
  unfold amplitudeAdjustedFullPairSum localizedLocalizedPairSum
    offDivisorPairRemainder
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n _hn
  rw [amplitudeAdjustedPairKernel_eq_four_channels]
  ring

/-- The exact decomposition provides the sharp abstract real-part reserve:
the remainder can consume at most its norm. -/
theorem amplitudeAdjustedFullPairSum_re_ge_localized_sub_remainderNorm
    {Q : ℕ} (hQ : 1 ≤ Q) (J : Finset ℕ) (e : CharacterSlot Q)
    (N : ℕ) (b : ℝ) (w : ℕ → ℂ) :
    (localizedLocalizedPairSum hQ J e N b w).re -
        ‖offDivisorPairRemainder hQ J e N b w‖ ≤
      (amplitudeAdjustedFullPairSum hQ J e N b w).re := by
  have hsplit :=
    amplitudeAdjustedFullPairSum_eq_localized_add_offDivisorRemainder
      hQ J e N b w
  have hsplitRe := congrArg Complex.re hsplit
  simp only [Complex.add_re] at hsplitRe
  have habs := Complex.abs_re_le_norm
    (offDivisorPairRemainder hQ J e N b w)
  have hneg := neg_abs_le
    (offDivisorPairRemainder hQ J e N b w).re
  linarith

/-- Conditional positivity gate with every remaining analytic burden visible. -/
theorem amplitudeAdjustedFullPairSum_re_pos_of_localized_reserve
    {Q : ℕ} (hQ : 1 ≤ Q) (J : Finset ℕ) (e : CharacterSlot Q)
    (N : ℕ) (b : ℝ) (w : ℕ → ℂ) (reserve : ℝ)
    (hmain : reserve ≤ (localizedLocalizedPairSum hQ J e N b w).re)
    (hloss : ‖offDivisorPairRemainder hQ J e N b w‖ < reserve) :
    0 < (amplitudeAdjustedFullPairSum hQ J e N b w).re := by
  have hnet :=
    amplitudeAdjustedFullPairSum_re_ge_localized_sub_remainderNorm
      hQ J e N b w
  linarith

end GoldbachCircleMethodAdjustedModelFourChannelPartitionV18292
