import GoldbachCircleMethodSharpNonprincipalBlockEnvelopeV18530

/-!
# Goldbach V1.8.531: uniform sharp source cap

Under the canonical finite-window admissions `1 <= H` and `Q <= H`, the
sharp conductor-independent source cap is at most
`(9 / 4) * log(B)^2`.  Thus the primitive raw-source channel contributes no
positive power of the block scale.  This does not control the remaining
conductor sum in the coefficient envelope.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodUniformSharpSourceCapV18531

open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodNonprincipalConductorIntervalEnergyV18520
open GoldbachCircleMethodSharpNonprincipalBlockEnvelopeV18530

theorem uniformSharpPrimitiveSourceCap_le_nine_fourths_log_sq
    (Q B : ℕ) (H : ℝ) (hH : 1 ≤ H) (hQH : (Q : ℝ) ≤ H) :
    uniformSharpPrimitiveSourceCap Q B H ≤
      (9 / 4 : ℝ) * (Real.log (B : ℝ)) ^ 2 := by
  have hHpos : 0 < H := lt_of_lt_of_le zero_lt_one hH
  have hH0 : 0 ≤ H := hHpos.le
  have hfloor : (⌊H⌋₊ : ℝ) ≤ H := Nat.floor_le hH0
  have hspan : ((2 * ⌊H⌋₊ + Q : ℕ) : ℝ) ≤ 3 * H := by
    norm_num at hfloor hQH ⊢
    linarith
  have hwindow : 2 * H + 1 ≤ 3 * H := by linarith
  have hnorm : ‖(2 * (H : ℂ))⁻¹‖ = (2 * H)⁻¹ := by
    have hnormTwo : ‖(2 : ℂ)‖ = (2 : ℝ) := by norm_num
    have hnormH : ‖(H : ℂ)‖ = H := by
      rw [Complex.norm_real, Real.norm_of_nonneg hH0]
    rw [norm_inv, norm_mul, hnormTwo, hnormH]
  unfold uniformSharpPrimitiveSourceCap
  rw [hnorm]
  calc
    (2 * H)⁻¹ ^ 2 *
        (((2 * ⌊H⌋₊ + Q : ℕ) : ℝ) *
          ((2 * H + 1) * (Real.log (B : ℝ)) ^ 2)) ≤
      (2 * H)⁻¹ ^ 2 *
        ((3 * H) * ((3 * H) * (Real.log (B : ℝ)) ^ 2)) := by
      gcongr
    _ = (9 / 4 : ℝ) * (Real.log (B : ℝ)) ^ 2 := by
      field_simp
      ring

/-- The sharp block envelope with its entire source normalization replaced by
the explicit polylogarithmic cap.  The surviving conductor/coefficient sum is
the next and only analytic scale gate in this branch. -/
theorem nonprincipalPrimitiveCorrelation_block_energy_le_polylog_source_envelope
    (Q B : ℕ) (H : ℝ) (w : ℕ → ℂ)
    (hB : 2 ≤ B) (hH : 1 ≤ H) (hQH : (Q : ℝ) ≤ H)
    (hwReal : ∀ n : ℕ, star (w n) = w n)
    (V : ℝ) (hV : 0 ≤ V)
    (hwBound : ∀ r q : PositiveLevel Q,
      r.val * q.val ≤ Q ∧ Nat.Coprime r.val q.val →
        ‖w (r.val * q.val)‖ ≤ V) :
    (∑ N ∈ GoldbachCircleMethodLogCutoffPresieveBindingV18120.blockCarrier B,
      ‖GoldbachCircleMethodHybridCenteredCorrelationEnergyV18501.nonprincipalPrimitiveCorrelation
        Q B N H w‖ ^ 2) ≤
      (Q : ℝ) * ((9 / 4 : ℝ) * (Real.log (B : ℝ)) ^ 2) *
        ∑ r : PositiveLevel Q,
          primitiveFamilyScale r *
            (((B + 1 : ℕ) : ℝ) *
                (∑ q : PositiveLevel Q,
                  ‖GoldbachCircleMethodActualCompanionCompleteDiagonalV18204.literalCoefficient
                    r q w‖ ^ 2 * (q.val.totient : ℝ)) +
              2 * (Q : ℝ) ^ 4 * V * V) := by
  have hH0 : 0 ≤ H := by linarith
  let E : PositiveLevel Q → ℝ := fun r =>
    primitiveFamilyScale r *
      (((B + 1 : ℕ) : ℝ) *
          (∑ q : PositiveLevel Q,
            ‖GoldbachCircleMethodActualCompanionCompleteDiagonalV18204.literalCoefficient
              r q w‖ ^ 2 * (q.val.totient : ℝ)) +
        2 * (Q : ℝ) ^ 4 * V * V)
  have hbase :=
    nonprincipalPrimitiveCorrelation_block_energy_le_uniform_sharp_envelope
      Q B H w hB hH0 hwReal V hV hwBound
  have hsum : 0 ≤ ∑ r : PositiveLevel Q, E r := by
    exact Finset.sum_nonneg (fun r _hr => by
      unfold E
      exact mul_nonneg (primitiveFamilyScale_nonneg r) (by positivity))
  have hcap := uniformSharpPrimitiveSourceCap_le_nine_fourths_log_sq
    Q B H hH hQH
  have hscaled :
      (Q : ℝ) * uniformSharpPrimitiveSourceCap Q B H *
          (∑ r : PositiveLevel Q, E r) ≤
        (Q : ℝ) * ((9 / 4 : ℝ) * (Real.log (B : ℝ)) ^ 2) *
          (∑ r : PositiveLevel Q, E r) := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hcap (Nat.cast_nonneg Q)) hsum
  exact hbase.trans (by simpa only [E] using hscaled)

end GoldbachCircleMethodUniformSharpSourceCapV18531
