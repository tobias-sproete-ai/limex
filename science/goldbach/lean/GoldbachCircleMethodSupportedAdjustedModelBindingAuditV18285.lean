import GoldbachCircleMethodDyadicMultiPeriodPositivityV18284
import GoldbachCircleMethodActiveResidualExactDecompositionV18251

/-!
# Goldbach V1.8.285: supported adjusted-model binding audit

The normalized unit-pair kernel from V1.8.271--V1.8.284 is not silently
identified with the supported adjusted model.  This module exposes the exact
principal and active amplitudes, rewrites the actual supported convolution on
its finite pair carrier, and partitions it into a unit-pair contribution and
the non-unit complement.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodSupportedAdjustedModelBindingAuditV18285

open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodFiniteCompanionBindingV18118
open GoldbachCircleMethodLogCutoffPresieveBindingV18120
open GoldbachCircleMethodPrincipalWindowBoundaryV18121
open GoldbachCircleMethodExceptionalWeightBoundaryV18128
open GoldbachCircleMethodActiveExceptionalCenteringV18129
open GoldbachCircleMethodSupportedModelErrorConvolutionV18182
open GoldbachCircleMethodActualUnitPairArithmeticV18194
open GoldbachCircleMethodActualResidualExactDecompositionV18225
open GoldbachCircleMethodBlockPairCarrierV18227
open GoldbachCircleMethodCanonicalBumpPrincipalFloorV18220
open GoldbachCircleMethodActiveResidualExactDecompositionV18251

/-- The coefficient multiplying the active character and the spatial power.
It is deliberately kept separate from the conductor-one principal amplitude. -/
noncomputable def activeRadialAmplitude {Q : ℕ} (r : PositiveLevel Q)
    (N : ℕ) (w : ℕ → ℂ) : ℂ :=
  ((r.val : ℂ) / (r.val.totient : ℂ)) * finiteCompanion r N w

/-- Amplitude-aware pointwise adjusted factor.  Setting both amplitudes to
one produces the normalized local kernel, but the actual model does not grant
that specialization. -/
noncomputable def amplitudeAdjustedFactor {Q : ℕ} (hQ : 1 ≤ Q)
    (r : PositiveLevel Q)
    (chi : {χ : DirichletCharacter ℂ r.val // χ.IsPrimitive})
    (N : ℕ) (b : ℝ) (w : ℕ → ℂ) : ℂ :=
  finiteCompanion (oneLevel hQ) N w -
    activeRadialAmplitude r N w * (powerWeight b N : ℂ) *
      chi.val (N : ZMod r.val)

/-- Exact pointwise expansion of the V1.8.129 adjusted model. -/
theorem adjustedModel_eq_amplitudeAdjustedFactor
    (Q N : ℕ) (hQ : 1 ≤ Q) (b : ℝ) (w : ℕ → ℂ)
    (e : CharacterSlot Q) :
    adjustedModel Q N hQ b w e =
      amplitudeAdjustedFactor hQ e.1 e.2 N b w := by
  unfold adjustedModel amplitudeAdjustedFactor activeRadialAmplitude
    windowCoefficient
  ring

/-- Literal amplitude-aware pair kernel at a natural target. -/
noncomputable def amplitudeAdjustedPairKernel {Q : ℕ} (hQ : 1 ≤ Q)
    (e : CharacterSlot Q) (N n : ℕ) (b : ℝ) (w : ℕ → ℂ) : ℂ :=
  amplitudeAdjustedFactor hQ e.1 e.2 n b w *
    amplitudeAdjustedFactor hQ e.1 e.2 (N - n) b w

/-- Full pair-carrier sum of the amplitude-aware adjusted kernel. -/
noncomputable def amplitudeAdjustedFullPairSum {Q : ℕ} (hQ : 1 ≤ Q)
    (J : Finset ℕ) (e : CharacterSlot Q) (N : ℕ)
    (b : ℝ) (w : ℕ → ℂ) : ℂ :=
  ∑ n ∈ pairFirstCarrier J N,
    amplitudeAdjustedPairKernel hQ e N n b w

/-- Portion of the actual amplitude-aware pair sum on unit-unit residues. -/
noncomputable def amplitudeAdjustedUnitPairSum {Q : ℕ} (hQ : 1 ≤ Q)
    (J : Finset ℕ) (e : CharacterSlot Q) (N : ℕ)
    (b : ℝ) (w : ℕ → ℂ) : ℂ :=
  ∑ n ∈ pairFirstCarrier J N,
    if (n : ZMod e.1.val) ∈ unitPairResidues e.1.val (N : ℤ) then
      amplitudeAdjustedPairKernel hQ e N n b w
    else 0

/-- Complementary contribution from pairs for which at least one residue is
not a unit.  It is retained exactly rather than discarded. -/
noncomputable def amplitudeAdjustedNonUnitPairSum {Q : ℕ} (hQ : 1 ≤ Q)
    (J : Finset ℕ) (e : CharacterSlot Q) (N : ℕ)
    (b : ℝ) (w : ℕ → ℂ) : ℂ :=
  ∑ n ∈ pairFirstCarrier J N,
    if (n : ZMod e.1.val) ∈ unitPairResidues e.1.val (N : ℤ) then 0
    else amplitudeAdjustedPairKernel hQ e N n b w

/-- Exact unit/non-unit partition of the amplitude-aware adjusted pair sum. -/
theorem amplitudeAdjustedFullPairSum_eq_unit_add_nonunit {Q : ℕ}
    (hQ : 1 ≤ Q) (J : Finset ℕ) (e : CharacterSlot Q) (N : ℕ)
    (b : ℝ) (w : ℕ → ℂ) :
    amplitudeAdjustedFullPairSum hQ J e N b w =
      amplitudeAdjustedUnitPairSum hQ J e N b w +
        amplitudeAdjustedNonUnitPairSum hQ J e N b w := by
  unfold amplitudeAdjustedFullPairSum amplitudeAdjustedUnitPairSum
    amplitudeAdjustedNonUnitPairSum
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n _hn
  by_cases hu : (n : ZMod e.1.val) ∈ unitPairResidues e.1.val (N : ℤ)
  · simp [hu]
  · simp [hu]

/-- At a natural target, the actual supported adjusted-model convolution is
exactly the full amplitude-aware pair-carrier sum. -/
theorem canonicalAdjustedModelAt_nat_eq_amplitudeAdjustedFullPairSum
    (B N : ℕ) (rho b : ℝ)
    (e : CharacterSlot ⌊((B : ℝ)^rho)^2⌋₊)
    (hR : 1 < (B : ℝ)^rho) (hBN : B ≤ N) :
    canonicalAdjustedModelAt B rho b e (N : ℤ) =
      amplitudeAdjustedFullPairSum
        (log_cutoff_contains_one ((B : ℝ)^rho) hR)
        (blockCarrier B) e N b (logWeight ((B : ℝ)^rho) canonicalLogBump) := by
  unfold canonicalAdjustedModelAt amplitudeAdjustedFullPairSum
  rw [integerPairConvolution_nat_eq_pairFirstCarrier]
  · apply Finset.sum_congr rfl
    intro n hn
    have hpair := Finset.mem_filter.mp hn
    have hnIoc : n ∈ Finset.Ioc (B / 2) B := by
      simpa only [blockCarrier] using hpair.1
    have hcIoc : N - n ∈ Finset.Ioc (B / 2) B := by
      simpa only [blockCarrier] using hpair.2
    unfold supportedAdjustedModel
    rw [dif_pos hR, if_pos hnIoc, dif_pos hR, if_pos hcIoc]
    rw [adjustedModel_eq_amplitudeAdjustedFactor,
      adjustedModel_eq_amplitudeAdjustedFactor]
    rfl
  · intro n hn
    simp only [blockCarrier, Finset.mem_Ioc] at hn
    omega

/-- Exact audit identity: the real supported adjusted-model convolution is
the sum of an amplitude-aware unit-pair part and its non-unit complement. -/
theorem canonicalAdjustedModelAt_nat_eq_unit_add_nonunit
    (B N : ℕ) (rho b : ℝ)
    (e : CharacterSlot ⌊((B : ℝ)^rho)^2⌋₊)
    (hR : 1 < (B : ℝ)^rho) (hBN : B ≤ N) :
    canonicalAdjustedModelAt B rho b e (N : ℤ) =
      amplitudeAdjustedUnitPairSum
          (log_cutoff_contains_one ((B : ℝ)^rho) hR)
          (blockCarrier B) e N b
          (logWeight ((B : ℝ)^rho) canonicalLogBump) +
        amplitudeAdjustedNonUnitPairSum
          (log_cutoff_contains_one ((B : ℝ)^rho) hR)
          (blockCarrier B) e N b
          (logWeight ((B : ℝ)^rho) canonicalLogBump) := by
  rw [canonicalAdjustedModelAt_nat_eq_amplitudeAdjustedFullPairSum
    B N rho b e hR hBN]
  exact amplitudeAdjustedFullPairSum_eq_unit_add_nonunit
    (log_cutoff_contains_one ((B : ℝ)^rho) hR)
    (blockCarrier B) e N b
    (logWeight ((B : ℝ)^rho) canonicalLogBump)

end GoldbachCircleMethodSupportedAdjustedModelBindingAuditV18285
