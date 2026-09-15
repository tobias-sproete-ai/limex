import GoldbachCircleMethodCanonicalAdjustedModelExplicitReserveV18312

/-!
# Goldbach V1.8.313: off-divisor pair norm envelope

The three off-divisor channels are bounded by their literal pointwise norm
envelope.  This is a finite triangle-inequality reduction only.  It does not
assert cancellation, smallness, or absorbability by the localized reserve.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodOffDivisorPairNormEnvelopeV18313

open GoldbachCircleMethodActiveConductorDivisorLocalizationV18290
open GoldbachCircleMethodActiveExceptionalCenteringV18129
open GoldbachCircleMethodAdjustedModelFourChannelPartitionV18292
open GoldbachCircleMethodBlockPairCarrierV18227

/-- Literal pointwise triangle envelope for the three channels containing an
off-divisor factor. -/
noncomputable def offDivisorPairNormEnvelope {Q : ℕ} (hQ : 1 ≤ Q)
    (J : Finset ℕ) (e : CharacterSlot Q) (N : ℕ)
    (b : ℝ) (w : ℕ → ℂ) : ℝ :=
  ∑ n ∈ pairFirstCarrier J N,
    (‖divisorLocalizedAdjustedFactor hQ e.1 e.2 n b w‖ *
        ‖offDivisorAdjustedFactor hQ e.1 e.2 (N - n) b w‖ +
      ‖offDivisorAdjustedFactor hQ e.1 e.2 n b w‖ *
        ‖divisorLocalizedAdjustedFactor hQ e.1 e.2 (N - n) b w‖ +
      ‖offDivisorAdjustedFactor hQ e.1 e.2 n b w‖ *
        ‖offDivisorAdjustedFactor hQ e.1 e.2 (N - n) b w‖)

/-- The full off-divisor remainder is bounded by the literal finite envelope.
No structural cancellation is discarded silently: it is simply not claimed. -/
theorem offDivisorPairRemainder_norm_le_envelope
    {Q : ℕ} (hQ : 1 ≤ Q)
    (J : Finset ℕ) (e : CharacterSlot Q) (N : ℕ)
    (b : ℝ) (w : ℕ → ℂ) :
    ‖offDivisorPairRemainder hQ J e N b w‖ ≤
      offDivisorPairNormEnvelope hQ J e N b w := by
  unfold offDivisorPairRemainder offDivisorPairNormEnvelope
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro n _hn
  let L₁ := divisorLocalizedAdjustedFactor hQ e.1 e.2 n b w
  let O₂ := offDivisorAdjustedFactor hQ e.1 e.2 (N - n) b w
  let O₁ := offDivisorAdjustedFactor hQ e.1 e.2 n b w
  let L₂ := divisorLocalizedAdjustedFactor hQ e.1 e.2 (N - n) b w
  calc
    ‖L₁ * O₂ + O₁ * L₂ + O₁ * O₂‖ ≤
        ‖L₁ * O₂ + O₁ * L₂‖ + ‖O₁ * O₂‖ := norm_add_le _ _
    _ ≤ (‖L₁ * O₂‖ + ‖O₁ * L₂‖) + ‖O₁ * O₂‖ :=
      add_le_add (norm_add_le _ _) le_rfl
    _ = ‖L₁‖ * ‖O₂‖ + ‖O₁‖ * ‖L₂‖ + ‖O₁‖ * ‖O₂‖ := by
      simp only [norm_mul]

/-- Uniform pointwise factor bounds give the explicit cardinality envelope
`#carrier * (2*L*O + O^2)`.  The theorem deliberately exposes that a merely
coarse `O` can be too large for later absorption. -/
theorem offDivisorPairNormEnvelope_le_uniform
    {Q : ℕ} (hQ : 1 ≤ Q)
    (J : Finset ℕ) (e : CharacterSlot Q) (N : ℕ)
    (b : ℝ) (w : ℕ → ℂ) (L O : ℝ)
    (hL : 0 ≤ L) (hO : 0 ≤ O)
    (hlocalized : ∀ n ∈ pairFirstCarrier J N,
      ‖divisorLocalizedAdjustedFactor hQ e.1 e.2 n b w‖ ≤ L ∧
      ‖divisorLocalizedAdjustedFactor hQ e.1 e.2 (N - n) b w‖ ≤ L)
    (hoff : ∀ n ∈ pairFirstCarrier J N,
      ‖offDivisorAdjustedFactor hQ e.1 e.2 n b w‖ ≤ O ∧
      ‖offDivisorAdjustedFactor hQ e.1 e.2 (N - n) b w‖ ≤ O) :
    offDivisorPairNormEnvelope hQ J e N b w ≤
      ((pairFirstCarrier J N).card : ℝ) * (2 * L * O + O ^ 2) := by
  unfold offDivisorPairNormEnvelope
  calc
    _ ≤ ∑ _n ∈ pairFirstCarrier J N, (2 * L * O + O ^ 2) := by
      apply Finset.sum_le_sum
      intro n hn
      rcases hlocalized n hn with ⟨hL₁, hL₂⟩
      rcases hoff n hn with ⟨hO₁, hO₂⟩
      have h₁ :
          ‖divisorLocalizedAdjustedFactor hQ e.1 e.2 n b w‖ *
              ‖offDivisorAdjustedFactor hQ e.1 e.2 (N - n) b w‖ ≤ L * O :=
        mul_le_mul hL₁ hO₂ (norm_nonneg _) hL
      have h₂ :
          ‖offDivisorAdjustedFactor hQ e.1 e.2 n b w‖ *
              ‖divisorLocalizedAdjustedFactor hQ e.1 e.2 (N - n) b w‖ ≤ O * L :=
        mul_le_mul hO₁ hL₂ (norm_nonneg _) hO
      have h₃ :
          ‖offDivisorAdjustedFactor hQ e.1 e.2 n b w‖ *
              ‖offDivisorAdjustedFactor hQ e.1 e.2 (N - n) b w‖ ≤ O * O :=
        mul_le_mul hO₁ hO₂ (norm_nonneg _) hO
      nlinarith
    _ = _ := by
      rw [Finset.sum_const, nsmul_eq_mul]

end GoldbachCircleMethodOffDivisorPairNormEnvelopeV18313
