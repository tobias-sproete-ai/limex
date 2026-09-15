import GoldbachCircleMethodActualQ3SignPrefixFluctuationProjectReserveV18740

/-!
# V1.8.741: q=3 project-debit absorption or negative witness

V1.8.740 reduces the actual denominator-three gate to the single explicit
inequality `actualQ3ProjectDebit < M / 14`.  Its inhabited prefix budget is a
finite absolute-mass majorant.  This append-only module tests whether global
centering alone can make that proof method nontrivial.

The result is negative.  A scaled, finite two-point source has exactly zero
total mass, while its target residue-class absolute mass and its q=3 transform
can exceed the project reserve by an arbitrary amount.  Therefore no uniform
`M / 14` absorption theorem follows from centering plus the present absolute-
mass envelope alone.

This is a negative witness for the proof class, not a lower bound for the
definitionally fixed Lambda-pair debit of V1.8.740.  That actual absorption
problem remains open and now requires genuinely signed arithmetic-progression
cancellation.  No minor-arc estimate, exceptional-set bound, or Goldbach
conclusion is asserted.  `proof_status = NO_PROOF`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

open scoped BigOperators Classical

namespace GoldbachCircleMethodActualQ3ProjectDebitAbsorptionOrNegativeWitnessV18741

open GoldbachCircleMethodActualCenteredQ3ResidueObstructionV18730
open GoldbachCircleMethodActualCenteredQ3MassRecombinationV18731
open GoldbachCircleMethodActualQ3SignPrefixFluctuationProjectReserveV18740

/-- Scalar dilation of the V1.8.731 centered two-point q=3 witness. -/
noncomputable def scaledQ3TwoPointWitness (A : Real) (s : Nat) : Complex :=
  (A : Complex) * q3TwoPointWitness s

/-- Absolute coefficient mass in one residue class modulo three.  This is the
generic analogue of the source-bound class envelope used in V1.8.740. -/
noncomputable def q3ClassAbsoluteMass
    (z : Nat → Complex) (r : ZMod 3) (k : Nat) : Real :=
  ∑ s ∈ Finset.range k, if (s : ZMod 3) = r then ‖z s‖ else 0

/-- Scaling preserves exact global centering on the complete two-point
support. -/
theorem sum_scaledQ3TwoPointWitness_eq_zero (A : Real) :
    (∑ s ∈ Finset.range 2, scaledQ3TwoPointWitness A s) = 0 := by
  unfold scaledQ3TwoPointWitness
  rw [← Finset.mul_sum, sum_q3TwoPointWitness_eq_zero]
  simp

/-- At target residue zero, the absolute-mass envelope is exactly the freely
chosen nonnegative amplitude. -/
theorem scaledQ3TwoPointWitness_classAbsoluteMass_zero_eq
    (A : Real) (hA : 0 ≤ A) :
    q3ClassAbsoluteMass (scaledQ3TwoPointWitness A) 0 2 = A := by
  norm_num [q3ClassAbsoluteMass, scaledQ3TwoPointWitness,
    q3TwoPointWitness, Finset.sum_range_succ, abs_of_nonneg hA]

/-- The corresponding q=3 transform is exactly three times the amplitude;
global centering removes only the total-mass term. -/
theorem scaledQ3TwoPointWitness_transform_zero_eq (A : Real) :
    q3EvenStepTransform (scaledQ3TwoPointWitness A) 0 2 =
      3 * (A : Complex) := by
  rw [q3EvenStepTransform_eq_three_mul_residueMass_sub_total,
    sum_scaledQ3TwoPointWitness_eq_zero]
  norm_num [q3ResidueMass, sameResidueThree, scaledQ3TwoPointWitness,
    q3TwoPointWitness, Finset.sum_range_succ]

/-- Concrete amplitude used to overrun the exact project reserve. -/
noncomputable def projectReserveBreakingAmplitude (M : Nat) : Real :=
  (M : Real) / 14 + 1

theorem projectReserveBreakingAmplitude_nonneg (M : Nat) :
    0 ≤ projectReserveBreakingAmplitude M := by
  unfold projectReserveBreakingAmplitude
  positivity

theorem projectReserve_lt_breakingAmplitude (M : Nat) :
    (M : Real) / 14 < projectReserveBreakingAmplitude M := by
  unfold projectReserveBreakingAmplitude
  linarith

/-- Amplitude that defeats the project reserve after multiplication by any
strictly positive q=3 variation scale. -/
noncomputable def variationScaledBreakingAmplitude
    (M : Nat) (σ : Real) : Real :=
  ((M : Real) / 14 + 1) / (3 * σ)

theorem variationScaledBreakingAmplitude_nonneg
    (M : Nat) {σ : Real} (hσ : 0 < σ) :
    0 ≤ variationScaledBreakingAmplitude M σ := by
  unfold variationScaledBreakingAmplitude
  positivity

theorem variationScaledWitness_classCharge_eq
    (M : Nat) {σ : Real} (hσ : 0 < σ) :
    3 * σ * q3ClassAbsoluteMass
        (scaledQ3TwoPointWitness (variationScaledBreakingAmplitude M σ)) 0 2 =
      (M : Real) / 14 + 1 := by
  rw [scaledQ3TwoPointWitness_classAbsoluteMass_zero_eq _
    (variationScaledBreakingAmplitude_nonneg M hσ)]
  unfold variationScaledBreakingAmplitude
  field_simp [ne_of_gt hσ]

/-- Formal negative witness: for every project scale there is an exactly
centered finite source whose class-absolute-mass envelope already exceeds the
entire `M / 14` reserve. -/
theorem exists_centered_source_classAbsoluteMass_gt_projectReserve (M : Nat) :
    ∃ z : Nat → Complex,
      (∑ s ∈ Finset.range 2, z s) = 0 ∧
      (M : Real) / 14 < q3ClassAbsoluteMass z 0 2 := by
  refine ⟨scaledQ3TwoPointWitness (projectReserveBreakingAmplitude M),
    sum_scaledQ3TwoPointWitness_eq_zero _, ?_⟩
  rw [scaledQ3TwoPointWitness_classAbsoluteMass_zero_eq _
    (projectReserveBreakingAmplitude_nonneg M)]
  exact projectReserve_lt_breakingAmplitude M

/-- Equivalent impossibility formulation: centering alone cannot imply a
strict class-absolute-mass bound by the project reserve for all sources. -/
theorem not_uniform_classAbsoluteMass_lt_projectReserve_from_centering
    (M : Nat) :
    ¬ ∀ z : Nat → Complex,
      (∑ s ∈ Finset.range 2, z s) = 0 →
      q3ClassAbsoluteMass z 0 2 < (M : Real) / 14 := by
  intro hUniform
  rcases exists_centered_source_classAbsoluteMass_gt_projectReserve M with
    ⟨z, hzCenter, hzLarge⟩
  have hzSmall := hUniform z hzCenter
  linarith

/-- Stronger proof-class obstruction matching the leading V1.8.740 envelope
term: for every strictly positive variation scale, centering alone permits a
source whose scaled class charge exceeds the full project reserve. -/
theorem exists_centered_source_scaledClassCharge_gt_projectReserve
    (M : Nat) {σ : Real} (hσ : 0 < σ) :
    ∃ z : Nat → Complex,
      (∑ s ∈ Finset.range 2, z s) = 0 ∧
      (M : Real) / 14 < 3 * σ * q3ClassAbsoluteMass z 0 2 := by
  refine ⟨scaledQ3TwoPointWitness (variationScaledBreakingAmplitude M σ),
    sum_scaledQ3TwoPointWitness_eq_zero _, ?_⟩
  rw [variationScaledWitness_classCharge_eq M hσ]
  linarith

/-- Consequently, even multiplication by a fixed positive variation scale
does not turn global centering into a uniform `M / 14` envelope theorem. -/
theorem not_uniform_scaledClassCharge_lt_projectReserve_from_centering
    (M : Nat) {σ : Real} (hσ : 0 < σ) :
    ¬ ∀ z : Nat → Complex,
      (∑ s ∈ Finset.range 2, z s) = 0 →
      3 * σ * q3ClassAbsoluteMass z 0 2 < (M : Real) / 14 := by
  intro hUniform
  rcases exists_centered_source_scaledClassCharge_gt_projectReserve M hσ with
    ⟨z, hzCenter, hzLarge⟩
  have hzSmall := hUniform z hzCenter
  linarith

/-- The same witness is visible in the signed q=3 channel itself: the norm of
the transform beats the reserve. -/
theorem scaledWitness_q3Transform_norm_gt_projectReserve (M : Nat) :
    (M : Real) / 14 <
      ‖q3EvenStepTransform
        (scaledQ3TwoPointWitness (projectReserveBreakingAmplitude M)) 0 2‖ := by
  let z : Complex := q3EvenStepTransform
    (scaledQ3TwoPointWitness (projectReserveBreakingAmplitude M)) 0 2
  have hzRe : z.re = 3 * projectReserveBreakingAmplitude M := by
    dsimp [z]
    rw [scaledQ3TwoPointWitness_transform_zero_eq]
    norm_num
  have hzAbs : |z.re| ≤ ‖z‖ := Complex.abs_re_le_norm z
  have hMnonneg : 0 ≤ (M : Real) := Nat.cast_nonneg M
  have hzLarge : (M : Real) / 14 < |z.re| := by
    rw [hzRe, abs_of_nonneg]
    · unfold projectReserveBreakingAmplitude
      nlinarith [hMnonneg]
    · unfold projectReserveBreakingAmplitude
      nlinarith [hMnonneg]
  exact hzLarge.trans_le hzAbs

end GoldbachCircleMethodActualQ3ProjectDebitAbsorptionOrNegativeWitnessV18741
