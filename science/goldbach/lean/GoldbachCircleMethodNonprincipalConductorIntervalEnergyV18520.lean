import GoldbachCircleMethodCompanionIntervalEnergyBoundV18496
import GoldbachCircleMethodRemovedCharacterWindowNormV18124

/-!
# Goldbach V1.8.520: primitive-family interval energy at one conductor

This module replaces the global character-cardinality estimate from V1.8.519
by the exact finite-companion interval energy already checked in V1.8.496.
The conclusion is conductor-local.  It neither sums over conductors nor claims
the sublinear source estimate required by the hybrid closure gate.
-/

set_option autoImplicit false

open scoped BigOperators Classical ComplexConjugate

namespace GoldbachCircleMethodNonprincipalConductorIntervalEnergyV18520

open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodFiniteCompanionBindingV18118
open GoldbachCircleMethodLogCutoffPresieveBindingV18120
open GoldbachCircleMethodPrincipalWindowBoundaryV18121
open GoldbachCircleMethodRemovedCharacterWindowNormV18124
open GoldbachCircleMethodActualCompanionCompleteDiagonalV18204
open GoldbachCircleMethodCompanionIntervalEnergyBoundV18496

/-- The exact scalar left after summing the squared normalization factor over
at most `phi(r)` primitive characters. -/
noncomputable def primitiveFamilyScale {Q : ℕ} (r : PositiveLevel Q) : ℝ :=
  (r.val.totient : ℝ) *
    (((r.val : ℝ) / (r.val.totient : ℝ)) ^ 2)

theorem primitiveFamilyScale_nonneg {Q : ℕ} (r : PositiveLevel Q) :
    0 ≤ primitiveFamilyScale r := by
  unfold primitiveFamilyScale
  positivity

/-- One character coefficient is controlled by the exact companion at the
same conductor; no global `Q^3` coefficient bound is used. -/
theorem windowCoefficient_sq_le_companion_sq
    {Q : ℕ} (r : PositiveLevel Q) (N : ℕ) (w : ℕ → ℂ)
    (χ : {χ : DirichletCharacter ℂ r.val // χ.IsPrimitive}) :
    ‖windowCoefficient r N w χ‖ ^ 2 ≤
      (((r.val : ℝ) / (r.val.totient : ℝ)) ^ 2) *
        ‖finiteCompanion r N w‖ ^ 2 := by
  have hphi : 0 < (r.val.totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne r.val))
  have hscale : 0 ≤ (r.val : ℝ) / (r.val.totient : ℝ) := by positivity
  have hnorm :
      ‖windowCoefficient r N w χ‖ ≤
        ((r.val : ℝ) / (r.val.totient : ℝ)) *
          ‖finiteCompanion r N w‖ := by
    unfold windowCoefficient
    rw [norm_mul, norm_mul, norm_div, Complex.norm_natCast,
      Complex.norm_natCast]
    have hχ := χ.val.norm_le_one (N : ZMod r.val)
    simpa only [mul_assoc, one_mul] using
      (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hχ
          (norm_nonneg (finiteCompanion r N w))) hscale)
  calc
    ‖windowCoefficient r N w χ‖ ^ 2 ≤
        (((r.val : ℝ) / (r.val.totient : ℝ)) *
          ‖finiteCompanion r N w‖) ^ 2 := by
      exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hnorm
    _ = _ := by ring

/-- Summing over the primitive family costs the exact finite scalar
`phi(r) * (r/phi(r))^2`, rather than the global slot-cardinality bound. -/
theorem primitive_windowCoefficient_energy_le
    {Q : ℕ} (r : PositiveLevel Q) (N : ℕ) (w : ℕ → ℂ) :
    (∑ χ : {χ : DirichletCharacter ℂ r.val // χ.IsPrimitive},
      ‖windowCoefficient r N w χ‖ ^ 2) ≤
      primitiveFamilyScale r * ‖finiteCompanion r N w‖ ^ 2 := by
  have hcard :
      Fintype.card {χ : DirichletCharacter ℂ r.val // χ.IsPrimitive} ≤
        r.val.totient := by
    calc
      _ ≤ Fintype.card (DirichletCharacter ℂ r.val) :=
        Fintype.card_subtype_le _
      _ = r.val.totient := by
        rw [← Nat.card_eq_fintype_card]
        exact DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity
          ℂ r.val
  calc
    (∑ χ : {χ : DirichletCharacter ℂ r.val // χ.IsPrimitive},
      ‖windowCoefficient r N w χ‖ ^ 2) ≤
        ∑ _χ : {χ : DirichletCharacter ℂ r.val // χ.IsPrimitive},
          (((r.val : ℝ) / (r.val.totient : ℝ)) ^ 2) *
            ‖finiteCompanion r N w‖ ^ 2 := by
      exact Finset.sum_le_sum
        (fun χ _hχ => windowCoefficient_sq_le_companion_sq r N w χ)
    _ = (Fintype.card
          {χ : DirichletCharacter ℂ r.val // χ.IsPrimitive} : ℝ) *
          ((((r.val : ℝ) / (r.val.totient : ℝ)) ^ 2) *
            ‖finiteCompanion r N w‖ ^ 2) := by
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
    _ ≤ (r.val.totient : ℝ) *
          ((((r.val : ℝ) / (r.val.totient : ℝ)) ^ 2) *
            ‖finiteCompanion r N w‖ ^ 2) := by
      exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hcard) (by positivity)
    _ = primitiveFamilyScale r * ‖finiteCompanion r N w‖ ^ 2 := by
      unfold primitiveFamilyScale
      ring

/-- The primitive-family coefficient energy on the central block is bounded
by the V1.8.496 incomplete-companion interval estimate at the same conductor.
This is the sharp modular replacement for V1.8.519's global `Q^4` pointwise
count; aggregation over `r > 1` remains a separate gate. -/
theorem primitive_windowCoefficient_block_energy_le
    {Q : ℕ} (r : PositiveLevel Q) (B : ℕ) (w : ℕ → ℂ)
    (hwReal : ∀ n : ℕ, star (w n) = w n)
    (V : ℝ) (hV : 0 ≤ V)
    (hwBound : ∀ q : PositiveLevel Q,
      r.val * q.val ≤ Q ∧ Nat.Coprime r.val q.val →
        ‖w (r.val * q.val)‖ ≤ V) :
    (∑ n ∈ blockCarrier B,
      ∑ χ : {χ : DirichletCharacter ℂ r.val // χ.IsPrimitive},
        ‖windowCoefficient r n w χ‖ ^ 2) ≤
      primitiveFamilyScale r *
        (((B + 1 : ℕ) : ℝ) * (∑ q : PositiveLevel Q,
          ‖literalCoefficient r q w‖ ^ 2 * (q.val.totient : ℝ)) +
            2 * (Q : ℝ) ^ 4 * V * V) := by
  have hsubset : blockCarrier B ⊆ Finset.range (B + 1) := by
    intro n hn
    exact Finset.mem_range.mpr (by
      have hnB : n ≤ B := (Finset.mem_Ioc.mp hn).2
      omega)
  calc
    (∑ n ∈ blockCarrier B,
      ∑ χ : {χ : DirichletCharacter ℂ r.val // χ.IsPrimitive},
        ‖windowCoefficient r n w χ‖ ^ 2) ≤
        ∑ n ∈ blockCarrier B,
          primitiveFamilyScale r * ‖finiteCompanion r n w‖ ^ 2 := by
      exact Finset.sum_le_sum
        (fun n _hn => primitive_windowCoefficient_energy_le r n w)
    _ = primitiveFamilyScale r *
          (∑ n ∈ blockCarrier B, ‖finiteCompanion r n w‖ ^ 2) := by
      rw [Finset.mul_sum]
    _ ≤ primitiveFamilyScale r *
          (∑ n ∈ Finset.range (B + 1),
            ‖finiteCompanion r n w‖ ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ (primitiveFamilyScale_nonneg r)
      exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
        (fun n _hn _hnot => sq_nonneg ‖finiteCompanion r n w‖)
    _ = primitiveFamilyScale r *
          (∑ i ∈ Finset.range (B + 1),
            ‖finiteCompanion r (0 + i) w‖ ^ 2) := by simp
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (primitiveFamilyScale_nonneg r)
      exact finiteCompanion_interval_energy_le
        r w hwReal 0 (B + 1) V hV hwBound

end GoldbachCircleMethodNonprincipalConductorIntervalEnergyV18520
