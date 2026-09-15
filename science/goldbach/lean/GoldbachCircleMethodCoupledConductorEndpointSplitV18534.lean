import GoldbachCircleMethodLiteralCoefficientDiagonalMajorantV18533

/-!
# Goldbach V1.8.534: coupled conductor and endpoint split

The support-preserving coefficient majorant from V1.8.533 is aggregated over
both denominator and conductor.  The resulting block envelope is decomposed
exactly into two independently auditable objects:

* a coupled reciprocal-totient kernel retaining `r*q <= Q` and coprimality;
* the pairwise-period endpoint remainder weighted by the primitive-family mass.

No bound for either aggregate is asserted here.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodCoupledConductorEndpointSplitV18534

open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodNonprincipalConductorIntervalEnergyV18520
open GoldbachCircleMethodCanonicalUniformSharpSourceCapV18532
open GoldbachCircleMethodLiteralCoefficientDiagonalMajorantV18533

/-- One reciprocal-totient diagonal kernel with the exact coupled carrier. -/
noncomputable def coupledReciprocalTotientKernel {Q : ℕ}
    (r q : PositiveLevel Q) : ℝ :=
  if r.val * q.val ≤ Q ∧ Nat.Coprime r.val q.val then
    1 / (q.val.totient : ℝ)
  else 0

/-- The aggregate diagonal arithmetic cost. -/
noncomputable def coupledConductorDiagonalKernel (Q : ℕ) : ℝ :=
  ∑ r : PositiveLevel Q,
    primitiveFamilyScale r *
      ∑ q : PositiveLevel Q, coupledReciprocalTotientKernel r q

/-- The aggregate primitive-family normalization multiplying the endpoint cost. -/
noncomputable def primitiveFamilyMass (Q : ℕ) : ℝ :=
  ∑ r : PositiveLevel Q, primitiveFamilyScale r

theorem literalCoefficientDiagonalMajorant_eq
    {Q : ℕ} (r q : PositiveLevel Q) (V : ℝ) :
    literalCoefficientDiagonalMajorant r q V =
      V ^ 2 * coupledReciprocalTotientKernel r q := by
  by_cases hactive : r.val * q.val ≤ Q ∧ Nat.Coprime r.val q.val
  · unfold literalCoefficientDiagonalMajorant coupledReciprocalTotientKernel
    rw [if_pos hactive, if_pos hactive, div_eq_mul_inv, one_div]
  · unfold literalCoefficientDiagonalMajorant coupledReciprocalTotientKernel
    rw [if_neg hactive, if_neg hactive, mul_zero]

theorem literalCoefficientDiagonalMajorant_sum_eq
    {Q : ℕ} (r : PositiveLevel Q) (V : ℝ) :
    (∑ q : PositiveLevel Q, literalCoefficientDiagonalMajorant r q V) =
      V ^ 2 * ∑ q : PositiveLevel Q, coupledReciprocalTotientKernel r q := by
  simp_rw [literalCoefficientDiagonalMajorant_eq r]
  exact (Finset.mul_sum _ _ _).symm

/-- Exact algebraic separation of the improved diagonal and the endpoint
remainder before any asymptotic estimate is applied. -/
theorem conductor_envelope_exact_split
    (Q B : ℕ) (V : ℝ) :
    (∑ r : PositiveLevel Q,
      primitiveFamilyScale r *
        (((B + 1 : ℕ) : ℝ) *
            (∑ q : PositiveLevel Q,
              literalCoefficientDiagonalMajorant r q V) +
          2 * (Q : ℝ) ^ 4 * V * V)) =
      (((B + 1 : ℕ) : ℝ) * V ^ 2) *
          coupledConductorDiagonalKernel Q +
        (2 * (Q : ℝ) ^ 4 * V * V) * primitiveFamilyMass Q := by
  unfold coupledConductorDiagonalKernel primitiveFamilyMass
  simp_rw [literalCoefficientDiagonalMajorant_sum_eq]
  calc
    _ = ∑ r : PositiveLevel Q,
        ((((B + 1 : ℕ) : ℝ) * V ^ 2) *
            (primitiveFamilyScale r *
              ∑ q : PositiveLevel Q, coupledReciprocalTotientKernel r q) +
          (2 * (Q : ℝ) ^ 4 * V * V) * primitiveFamilyScale r) := by
      apply Finset.sum_congr rfl
      intro r _hr
      ring
    _ = (∑ r : PositiveLevel Q,
          (((B + 1 : ℕ) : ℝ) * V ^ 2) *
            (primitiveFamilyScale r *
              ∑ q : PositiveLevel Q, coupledReciprocalTotientKernel r q)) +
        ∑ r : PositiveLevel Q,
          (2 * (Q : ℝ) ^ 4 * V * V) * primitiveFamilyScale r := by
      rw [Finset.sum_add_distrib]
    _ = _ := by
      rw [← Finset.mul_sum, ← Finset.mul_sum]

/-- Canonical source-normalized envelope with the diagonal and endpoint costs
made explicit as separate arithmetic gates. -/
theorem nonprincipalPrimitiveCorrelation_block_energy_le_split_envelope
    (B : ℕ) (R : ℝ) (w : ℕ → ℂ)
    (hB : 2 ≤ B) (hR : 1 < R) (hscale : R ^ 6 ≤ (B : ℝ))
    (hwReal : ∀ n : ℕ, star (w n) = w n)
    (V : ℝ) (hV : 0 ≤ V)
    (hwBound : ∀ r q : PositiveLevel ⌊R ^ 2⌋₊,
      r.val * q.val ≤ ⌊R ^ 2⌋₊ ∧ Nat.Coprime r.val q.val →
        ‖w (r.val * q.val)‖ ≤ V) :
    (∑ N ∈ GoldbachCircleMethodLogCutoffPresieveBindingV18120.blockCarrier B,
      ‖GoldbachCircleMethodHybridCenteredCorrelationEnergyV18501.nonprincipalPrimitiveCorrelation
        ⌊R ^ 2⌋₊ B N ((B : ℝ) / R ^ 4) w‖ ^ 2) ≤
      (⌊R ^ 2⌋₊ : ℝ) *
        ((9 / 4 : ℝ) * (Real.log (B : ℝ)) ^ 2) *
        (((((B + 1 : ℕ) : ℝ) * V ^ 2) *
            coupledConductorDiagonalKernel ⌊R ^ 2⌋₊) +
          ((2 * (⌊R ^ 2⌋₊ : ℝ) ^ 4 * V * V) *
            primitiveFamilyMass ⌊R ^ 2⌋₊)) := by
  have hbase :=
    nonprincipalPrimitiveCorrelation_block_energy_le_canonical_polylog_source
      B R w hB hR hscale hwReal V hV hwBound
  have hdiag : ∀ r : PositiveLevel ⌊R ^ 2⌋₊,
      (∑ q : PositiveLevel ⌊R ^ 2⌋₊,
        ‖GoldbachCircleMethodActualCompanionCompleteDiagonalV18204.literalCoefficient
          r q w‖ ^ 2 * (q.val.totient : ℝ)) ≤
        ∑ q : PositiveLevel ⌊R ^ 2⌋₊,
          literalCoefficientDiagonalMajorant r q V := by
    intro r
    exact literalCoefficient_diagonal_sum_le_majorant_sum
      r w V (fun q => hwBound r q)
  have hinner :
      (∑ r : PositiveLevel ⌊R ^ 2⌋₊,
        primitiveFamilyScale r *
          ((((B + 1 : ℕ) : ℝ) *
              (∑ q : PositiveLevel ⌊R ^ 2⌋₊,
                ‖GoldbachCircleMethodActualCompanionCompleteDiagonalV18204.literalCoefficient
                  r q w‖ ^ 2 * (q.val.totient : ℝ))) +
            2 * (⌊R ^ 2⌋₊ : ℝ) ^ 4 * V * V)) ≤
        ∑ r : PositiveLevel ⌊R ^ 2⌋₊,
          primitiveFamilyScale r *
            ((((B + 1 : ℕ) : ℝ) *
                (∑ q : PositiveLevel ⌊R ^ 2⌋₊,
                  literalCoefficientDiagonalMajorant r q V)) +
              2 * (⌊R ^ 2⌋₊ : ℝ) ^ 4 * V * V) := by
    apply Finset.sum_le_sum
    intro r _hr
    apply mul_le_mul_of_nonneg_left _ (primitiveFamilyScale_nonneg r)
    have hBcast : 0 ≤ (((B + 1 : ℕ) : ℝ)) := by positivity
    exact add_le_add
      (mul_le_mul_of_nonneg_left (hdiag r) hBcast) (le_refl _)
  have hlog : 0 ≤ Real.log (B : ℝ) := by
    apply Real.log_nonneg
    exact_mod_cast (show 1 ≤ B by omega)
  have houter :
      0 ≤ (⌊R ^ 2⌋₊ : ℝ) *
        ((9 / 4 : ℝ) * (Real.log (B : ℝ)) ^ 2) := by
    positivity
  calc
    _ ≤ (⌊R ^ 2⌋₊ : ℝ) *
        ((9 / 4 : ℝ) * (Real.log (B : ℝ)) ^ 2) *
        (∑ r : PositiveLevel ⌊R ^ 2⌋₊,
          primitiveFamilyScale r *
            ((((B + 1 : ℕ) : ℝ) *
                (∑ q : PositiveLevel ⌊R ^ 2⌋₊,
                  ‖GoldbachCircleMethodActualCompanionCompleteDiagonalV18204.literalCoefficient
                    r q w‖ ^ 2 * (q.val.totient : ℝ))) +
              2 * (⌊R ^ 2⌋₊ : ℝ) ^ 4 * V * V)) := hbase
    _ ≤ (⌊R ^ 2⌋₊ : ℝ) *
        ((9 / 4 : ℝ) * (Real.log (B : ℝ)) ^ 2) *
        (∑ r : PositiveLevel ⌊R ^ 2⌋₊,
          primitiveFamilyScale r *
            ((((B + 1 : ℕ) : ℝ) *
                (∑ q : PositiveLevel ⌊R ^ 2⌋₊,
                  literalCoefficientDiagonalMajorant r q V)) +
              2 * (⌊R ^ 2⌋₊ : ℝ) ^ 4 * V * V)) := by
      exact mul_le_mul_of_nonneg_left hinner houter
    _ = _ := by
      rw [conductor_envelope_exact_split]

end GoldbachCircleMethodCoupledConductorEndpointSplitV18534
