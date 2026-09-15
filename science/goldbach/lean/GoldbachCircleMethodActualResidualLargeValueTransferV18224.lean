import GoldbachCircleMethodCanonicalBumpResidualMomentsV18222

/-!
# Goldbach V1.8.224: actual residual large-value transfer

This module applies a finite Chebyshev/Markov counting argument to the actual
canonical-bump principal residual convolution from V1.8.222.  It controls only
the number of frequencies at which the residual norm exceeds a positive
threshold.  It does not prove that a Goldbach exception has that property.
-/

open scoped BigOperators Classical

set_option autoImplicit false

namespace GoldbachCircleMethodActualResidualLargeValueTransferV18224

open GoldbachCircleMethodLogCutoffPresieveBindingV18120
open GoldbachCircleMethodActualInputModelResidualV18138
open GoldbachCircleMethodUncorrectedSupportedErrorConvolutionV18184
open GoldbachCircleMethodSupportedModelErrorConvolutionV18182
open GoldbachCircleMethodSupportedResidualParsevalV18190
open GoldbachCircleMethodCanonicalBumpPrincipalFloorV18220
open GoldbachCircleMethodCanonicalBumpResidualMomentsV18222
open GoldbachCircleMethodRealApproximationMinorAdapterV1873

/-- Finite indices at which the norm of `F` reaches the positive mark `T`. -/
noncomputable def largeNormIndices {ι E : Type*} [DecidableEq ι]
    [SeminormedAddGroup E] (s : Finset ι) (F : ι → E) (T : ℝ) : Finset ι :=
  s.filter (fun i => T ≤ ‖F i‖)

/-- Each large-value index contributes at least `T²` to the full second
moment.  This is the finite counting core and contains no analytic premise. -/
theorem largeNorm_card_mul_threshold_sq_le_moment
    {ι E : Type*} [DecidableEq ι] [SeminormedAddGroup E]
    (s : Finset ι) (F : ι → E) (T : ℝ) (hT : 0 < T) :
    ((largeNormIndices s F T).card : ℝ) * T ^ 2 ≤
      ∑ i ∈ s, ‖F i‖ ^ 2 := by
  classical
  calc
    ((largeNormIndices s F T).card : ℝ) * T ^ 2 =
        ∑ _i ∈ largeNormIndices s F T, T ^ 2 := by simp
    _ ≤ ∑ i ∈ largeNormIndices s F T, ‖F i‖ ^ 2 := by
      exact Finset.sum_le_sum fun i hi => by
        have hiT : T ≤ ‖F i‖ := (Finset.mem_filter.mp hi).2
        nlinarith [norm_nonneg (F i)]
    _ ≤ ∑ i ∈ s, ‖F i‖ ^ 2 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.filter_subset _ _
      · intro i _ _
        exact sq_nonneg ‖F i‖

/-- Division form of the finite large-value transfer. -/
theorem largeNorm_card_le_of_moment_bound
    {ι E : Type*} [DecidableEq ι] [SeminormedAddGroup E]
    (s : Finset ι) (F : ι → E) (T momentBudget : ℝ)
    (hT : 0 < T)
    (hMoment : (∑ i ∈ s, ‖F i‖ ^ 2) ≤ momentBudget) :
    ((largeNormIndices s F T).card : ℝ) ≤ momentBudget / T ^ 2 := by
  have hT2 : 0 < T ^ 2 := sq_pos_of_pos hT
  apply (le_div_iff₀ hT2).2
  exact (largeNorm_card_mul_threshold_sq_le_moment s F T hT).trans hMoment

/-- The actual principal residual convolution already used in V1.8.222,
exposed as a named function so its large-value set cannot drift. -/
noncomputable def canonicalPrincipalResidualAt
    (B : ℕ) (rho : ℝ) (hR2 : 2 ≤ (B : ℝ)^rho) (k : ℤ) : ℂ :=
  integerPairConvolution (blockCarrier B)
    (fun N => inputPrincipalResidual B N ((B : ℝ)^rho) (by linarith)
      canonicalLogBump)
    (fun N => blockInput B N +
      supportedPrincipalModel B N ((B : ℝ)^rho) canonicalLogBump) k

/-- The V1.8.222 moment yields a cardinality bound for the literal actual
principal residual at every positive threshold.  `RealVaughanEstimate C`
and all scale restrictions remain explicit premises. -/
theorem canonical_principal_residual_largeNorm_card_bound
    (C rho : ℝ) (hC : 0 ≤ C) (hV : RealVaughanEstimate C)
    (hrho : 0 < rho) :
    ∃ Crho : ℝ, 0 ≤ Crho ∧ ∀ (B : ℕ) (_hB : 6 ≤ B),
      ∀ (hR2 : 2 ≤ (B : ℝ)^rho),
      Real.exp (Real.sqrt (Real.log (B : ℝ))) ≤ (B : ℝ)^rho →
      (B : ℝ)^rho ≤ (B : ℝ)^((1 : ℝ) / 10000) →
      ∀ T : ℝ, 0 < T →
      ((largeNormIndices (Finset.Icc (0 : ℤ) (2 * B : ℕ))
        (canonicalPrincipalResidualAt B rho hR2) T).card : ℝ) ≤
        (Crho * (B : ℝ)^3 * ((B : ℝ)^rho)^(-(5 : ℝ) / 8) *
          (Real.log (B : ℝ))^2) / T^2 := by
  obtain ⟨Crho, hCrho, hMoment⟩ :=
    canonical_principal_residual_moment_power_bound C rho hC hV hrho
  refine ⟨Crho, hCrho, ?_⟩
  intro B hB hR2 hlower hupper T hT
  apply largeNorm_card_le_of_moment_bound
    (Finset.Icc (0 : ℤ) (2 * B : ℕ))
    (canonicalPrincipalResidualAt B rho hR2) T
    (Crho * (B : ℝ)^3 * ((B : ℝ)^rho)^(-(5 : ℝ) / 8) *
      (Real.log (B : ℝ))^2) hT
  simpa only [canonicalPrincipalResidualAt] using
    hMoment B hB hR2 hlower hupper

end GoldbachCircleMethodActualResidualLargeValueTransferV18224
