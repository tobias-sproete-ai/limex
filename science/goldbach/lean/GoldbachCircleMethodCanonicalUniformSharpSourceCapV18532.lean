import GoldbachCircleMethodUniformSharpSourceCapV18531
import GoldbachCircleMethodActualOutputTailBoundV18132

/-!
# Goldbach V1.8.532: canonical uniform sharp source cap

The abstract admissions `1 <= H` and `Q <= H` from V1.8.531 are discharged
at the unchanged circle-method scale `Q = floor(R^2)`, `H = B / R^4` under
the already kernel-checked window condition `R^6 <= B`.  This closes only the
source-normalization gate.  The conductor/coefficient envelope remains
explicit and unresolved.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodCanonicalUniformSharpSourceCapV18532

open GoldbachCircleMethodActualOutputTailBoundV18132
open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodNonprincipalConductorIntervalEnergyV18520
open GoldbachCircleMethodSharpNonprincipalBlockEnvelopeV18530
open GoldbachCircleMethodUniformSharpSourceCapV18531

/-- At the actual scale, the entire sharp primitive-source normalization is
polylogarithmic and has no positive power of `B`. -/
theorem canonicalUniformSharpPrimitiveSourceCap_le_nine_fourths_log_sq
    (B : ℕ) (R : ℝ) (hR : 1 < R) (hscale : R ^ 6 ≤ (B : ℝ)) :
    uniformSharpPrimitiveSourceCap ⌊R ^ 2⌋₊ B ((B : ℝ) / R ^ 4) ≤
      (9 / 4 : ℝ) * (Real.log (B : ℝ)) ^ 2 := by
  have hwindow := window_dominates_cutoff (B : ℝ) R hR hscale
  exact uniformSharpPrimitiveSourceCap_le_nine_fourths_log_sq
    ⌊R ^ 2⌋₊ B ((B : ℝ) / R ^ 4) hwindow.1 hwindow.2

/-- Canonical block envelope after eliminating the former source power loss.
No estimate of the remaining conductor/coefficient sum is inserted. -/
theorem nonprincipalPrimitiveCorrelation_block_energy_le_canonical_polylog_source
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
        ∑ r : PositiveLevel ⌊R ^ 2⌋₊,
          primitiveFamilyScale r *
            (((B + 1 : ℕ) : ℝ) *
                (∑ q : PositiveLevel ⌊R ^ 2⌋₊,
                  ‖GoldbachCircleMethodActualCompanionCompleteDiagonalV18204.literalCoefficient
                    r q w‖ ^ 2 * (q.val.totient : ℝ)) +
              2 * (⌊R ^ 2⌋₊ : ℝ) ^ 4 * V * V) := by
  have hwindow := window_dominates_cutoff (B : ℝ) R hR hscale
  exact nonprincipalPrimitiveCorrelation_block_energy_le_polylog_source_envelope
    ⌊R ^ 2⌋₊ B ((B : ℝ) / R ^ 4) w hB hwindow.1 hwindow.2
      hwReal V hV hwBound

end GoldbachCircleMethodCanonicalUniformSharpSourceCapV18532
