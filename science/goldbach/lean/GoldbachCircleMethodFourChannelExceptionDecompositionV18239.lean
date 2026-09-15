import GoldbachCircleMethodAdmittedDefectTwoErrorForcingV18238

/-!
# Goldbach V1.8.239: four-channel exception decomposition

Every hypothetical non-Goldbach target in the complete dyadic block is
embedded into an explicit union of four large-value sets: principal residual
and centered-error correction, at each of the two genuine source scales.

This is finite set bookkeeping only.  It supplies no moment estimate for any
channel and in particular does not manufacture control of the centered-error
correction.
-/

open scoped Classical

set_option autoImplicit false

namespace GoldbachCircleMethodFourChannelExceptionDecompositionV18239

open GoldbachPurePrimeAdequacyV15
open GoldbachCircleMethodResidualScaleAdmissionV18196
open GoldbachCircleMethodActualResidualLargeValueTransferV18224
open GoldbachCircleMethodActualResidualExactDecompositionV18225
open GoldbachCircleMethodTwoSourceScaleCoverV18232
open GoldbachCircleMethodTwoScaleEvenBlockDefectReserveV1833
open GoldbachCircleMethodAdmittedDefectTwoErrorForcingV18238
open GoldbachCircleMethodFiniteResiduePrefixV1866
open GoldbachCircleMethodBoundedConductorReindexV18117

/-- Hypothetical counterexamples inside the historical even dyadic block. -/
noncomputable def nonGoldbachTargets (M : ℕ) : Finset ℕ :=
  (evenTargetBlock M).filter (fun N => ¬ GoldbachAt N)

/-- Principal-residual large values, with the proof-relevant radius admission
kept explicit so the set is tied to the literal residual used in V1.8.238. -/
noncomputable def principalBadTargets
    (M B : ℕ) (rho : ℝ) (hR2 : 2 ≤ (B : ℝ)^rho) : Finset ℕ :=
  largeNormIndices (evenTargetBlock M)
    (fun N => canonicalPrincipalResidualAt B rho hR2 (N : ℤ))
    ((M : ℝ) / 2048)

/-- Centered-error-correction large values on the same target block. -/
noncomputable def correctionBadTargets
    (M B : ℕ) (rho : ℝ) : Finset ℕ :=
  largeNormIndices (evenTargetBlock M)
    (fun N => canonicalCenteredErrorCorrectionAt B rho (N : ℤ))
    ((M : ℝ) / 2048)

/-- Membership in the counterexample set exposes both the target-block
condition and the literal failure of `GoldbachAt`. -/
theorem mem_nonGoldbachTargets_iff (M N : ℕ) :
    N ∈ nonGoldbachTargets M ↔ N ∈ evenTargetBlock M ∧ ¬ GoldbachAt N := by
  simp [nonGoldbachTargets]

/-- The four named large-value sets used by the exception decomposition. -/
noncomputable def fourChannelBadUnion
    (M : ℕ) (rho : ℝ)
    (hR2Low : 2 ≤ (lowerSourceScale M : ℝ)^rho)
    (hR2High : 2 ≤ (upperSourceScale M : ℝ)^rho) : Finset ℕ :=
  ((principalBadTargets M (lowerSourceScale M) rho hR2Low ∪
      correctionBadTargets M (lowerSourceScale M) rho) ∪
    principalBadTargets M (upperSourceScale M) rho hR2High) ∪
  correctionBadTargets M (upperSourceScale M) rho

/-- Every hypothetical non-Goldbach target belongs to the explicit four-set
union.  The theorem uses the exact V1.8.238 forcing alternative and performs
no analytic estimate. -/
theorem nonGoldbachTargets_subset_fourChannelBadUnion
    {K : ℕ} [NeZero K]
    (M : ℕ) (rho : ℝ) (hM : 37 ≤ M)
    (hrho : 0 < rho) (hrhoUpper : rho ≤ (1 : ℝ) / 10000)
    (hLow : blockThreshold rho ≤ lowerSourceScale M)
    (hHigh : blockThreshold rho ≤ upperSourceScale M)
    (hKLow : ∀ q : PositiveLevel
        ⌊((lowerSourceScale M : ℝ) ^ rho) ^ 2⌋₊, q.val ∣ K)
    (hKHigh : ∀ q : PositiveLevel
        ⌊((upperSourceScale M : ℝ) ^ rho) ^ 2⌋₊, q.val ∣ K) :
    nonGoldbachTargets M ⊆
      fourChannelBadUnion M rho
        (actual_scale_admission rho hrho hrhoUpper
          (lowerSourceScale M) hLow).2.1
        (actual_scale_admission rho hrho hrhoUpper
          (upperSourceScale M) hHigh).2.1 := by
  intro N hN
  have hData := (mem_nonGoldbachTargets_iff M N).mp hN
  have hForce :=
    evenTargetBlock_not_goldbach_forces_large_error_at_covering_scale
      (K := K) M N rho hM hData.1 hrho hrhoUpper hLow hHigh
      hKLow hKHigh hData.2
  simp only [fourChannelBadUnion, Finset.mem_union]
  rcases hForce with (hLowPrincipal | hLowCorrection) |
      (hHighPrincipal | hHighCorrection)
  · exact Or.inl (Or.inl (Or.inl
      (Finset.mem_filter.mpr ⟨hData.1, hLowPrincipal⟩)))
  · exact Or.inl (Or.inl (Or.inr
      (Finset.mem_filter.mpr ⟨hData.1, hLowCorrection⟩)))
  · exact Or.inl (Or.inr
      (Finset.mem_filter.mpr ⟨hData.1, hHighPrincipal⟩))
  · exact Or.inr
      (Finset.mem_filter.mpr ⟨hData.1, hHighCorrection⟩)

/-- Finite cardinality consequence.  No channel is hidden in a combined
constant: all four counts remain separately visible. -/
theorem nonGoldbachTargets_card_le_four_channel_sum
    {K : ℕ} [NeZero K]
    (M : ℕ) (rho : ℝ) (hM : 37 ≤ M)
    (hrho : 0 < rho) (hrhoUpper : rho ≤ (1 : ℝ) / 10000)
    (hLow : blockThreshold rho ≤ lowerSourceScale M)
    (hHigh : blockThreshold rho ≤ upperSourceScale M)
    (hKLow : ∀ q : PositiveLevel
        ⌊((lowerSourceScale M : ℝ) ^ rho) ^ 2⌋₊, q.val ∣ K)
    (hKHigh : ∀ q : PositiveLevel
        ⌊((upperSourceScale M : ℝ) ^ rho) ^ 2⌋₊, q.val ∣ K) :
    (nonGoldbachTargets M).card ≤
      (principalBadTargets M (lowerSourceScale M) rho
          (actual_scale_admission rho hrho hrhoUpper
            (lowerSourceScale M) hLow).2.1).card +
      (correctionBadTargets M (lowerSourceScale M) rho).card +
      (principalBadTargets M (upperSourceScale M) rho
          (actual_scale_admission rho hrho hrhoUpper
            (upperSourceScale M) hHigh).2.1).card +
      (correctionBadTargets M (upperSourceScale M) rho).card := by
  let LP := principalBadTargets M (lowerSourceScale M) rho
    (actual_scale_admission rho hrho hrhoUpper
      (lowerSourceScale M) hLow).2.1
  let LC := correctionBadTargets M (lowerSourceScale M) rho
  let HP := principalBadTargets M (upperSourceScale M) rho
    (actual_scale_admission rho hrho hrhoUpper
      (upperSourceScale M) hHigh).2.1
  let HC := correctionBadTargets M (upperSourceScale M) rho
  have hSubset := nonGoldbachTargets_subset_fourChannelBadUnion
    (K := K) M rho hM hrho hrhoUpper hLow hHigh hKLow hKHigh
  have h0 : (nonGoldbachTargets M).card ≤ (((LP ∪ LC) ∪ HP) ∪ HC).card := by
    apply Finset.card_le_card
    simpa [fourChannelBadUnion, LP, LC, HP, HC] using hSubset
  have h1 := Finset.card_union_le LP LC
  have h2 := Finset.card_union_le (LP ∪ LC) HP
  have h3 := Finset.card_union_le ((LP ∪ LC) ∪ HP) HC
  dsimp [LP, LC, HP, HC] at h0 h1 h2 h3 ⊢
  omega

end GoldbachCircleMethodFourChannelExceptionDecompositionV18239

