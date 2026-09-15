import GoldbachCircleMethodPrincipalActivePairwisePeriodV18316
import GoldbachCircleMethodActualTwistSelfConvolutionV18211

/-!
# Goldbach V1.8.317: active/active pairwise-period adapter

Two literal active terms at a fixed primitive conductor are completed only on
`lcm(r*l,r*k)`.  The exact diagonal projection and the finite incomplete-period
cost remain separate.  No global common LCM is introduced.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodActiveActivePairwisePeriodV18317

open GoldbachCircleMethodActualCompanionCompleteDiagonalV18204
open GoldbachCircleMethodActualTwistSelfConvolutionV18211
open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodFiniteResiduePrefixV1866
open GoldbachCircleMethodPairwisePeriodRemainderBoundV18206
open GoldbachCircleMethodPrincipalActivePairwisePeriodV18316
open GoldbachCircleMethodPrimitiveTwistedRamanujanSupportV18208

/-- Exact normalized active/active projection for one denominator pair. -/
noncomputable def activeActivePairMean {Q : ℕ}
    (r l k : PositiveLevel Q)
    (chi : {χ : DirichletCharacter ℂ r.val // χ.IsPrimitive})
    (v w : ℕ → ℂ) (N : ℕ) : ℂ :=
  if l.val = k.val then
    ((r.val : ℂ) / (r.val.totient : ℂ) ^ 2) *
      literalCoefficient r l v * literalCoefficient r k w * chi.val (-1) *
      unitCharacterSum r.val (N : ZMod r.val) *
      unitCharacterSum l.val (N : ZMod l.val)
  else 0

/-- One active/active pair is centered on its exact Fourier projection and
completed only on `lcm(r*l,r*k)`.  Both literal weights survive. -/
theorem active_active_pair_interval_norm_le {Q : ℕ}
    (r l k : PositiveLevel Q)
    (_hadm_l : r.val * l.val ≤ Q) (_hadm_k : r.val * k.val ≤ Q)
    (hcop_l : Nat.Coprime r.val l.val) (hcop_k : Nat.Coprime r.val k.val)
    (chi : {χ : DirichletCharacter ℂ r.val // χ.IsPrimitive})
    (hInv : chi.val⁻¹ = chi.val)
    (v w : ℕ → ℂ) (N A T : ℕ) (hend : A + T ≤ N + 1)
    (V W : ℝ) (hV : 0 ≤ V) (hW : 0 ≤ W)
    (hv : ‖v (r.val * l.val)‖ ≤ V)
    (hw : ‖w (r.val * k.val)‖ ≤ W) :
    ‖(∑ i ∈ Finset.range T,
        activeTwistedLiteralTerm r l chi v
            ((N - (A + i) : ℕ) : ZMod (r.val * l.val)) *
          activeTwistedLiteralTerm r k chi w
            ((A + i : ℕ) : ZMod (r.val * k.val))) -
      (T : ℂ) * activeActivePairMean r l k chi v w N‖ ≤
      2 * (Nat.lcm (r.val * l.val) (r.val * k.val) : ℝ) *
        ((r.val : ℝ) * V) * ((r.val : ℝ) * W) := by
  let K := Nat.lcm (r.val * l.val) (r.val * k.val)
  let _ : NeZero K :=
    ⟨Nat.lcm_ne_zero
      (Nat.mul_ne_zero (NeZero.ne r.val) (NeZero.ne l.val))
      (Nat.mul_ne_zero (NeZero.ne r.val) (NeZero.ne k.val))⟩
  have hrlK : r.val * l.val ∣ K := Nat.dvd_lcm_left _ _
  have hrkK : r.val * k.val ∣ K := Nat.dvd_lcm_right _ _
  let g : ZMod K → ℂ := fun x =>
    activeTwistedLiteralTerm r l chi v
        (ZMod.castHom hrlK (ZMod (r.val * l.val)) ((N : ZMod K) - x)) *
      activeTwistedLiteralTerm r k chi w
        (ZMod.castHom hrkK (ZMod (r.val * k.val)) x)
  let d : ℂ := activeActivePairMean r l k chi v w N
  have hg : ∀ x, ‖g x‖ ≤ ((r.val : ℝ) * V) * ((r.val : ℝ) * W) := by
    intro x
    unfold g
    rw [norm_mul]
    exact mul_le_mul
      (activeTwistedLiteralTerm_norm_le r l chi v V hV hv _)
      (activeTwistedLiteralTerm_norm_le r k chi w W hW hw _)
      (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) hV)
  have hmean : (∑ x : ZMod K, g x) = (K : ℂ) * d := by
    unfold g d activeActivePairMean activeTwistedLiteralTerm
    rw [show (∑ x : ZMod K,
        (((r.val : ℂ) / (r.val.totient : ℂ)) *
          literalCoefficient r l v *
          twistedRamanujan r.val l.val chi.val
            (ZMod.castHom hrlK (ZMod (r.val * l.val)) ((N : ZMod K) - x))) *
        (((r.val : ℂ) / (r.val.totient : ℂ)) *
          literalCoefficient r k w *
          twistedRamanujan r.val k.val chi.val
            (ZMod.castHom hrkK (ZMod (r.val * k.val)) x))) =
        ((((r.val : ℂ) / (r.val.totient : ℂ)) ^ 2) *
          literalCoefficient r l v * literalCoefficient r k w) *
        (∑ x : ZMod K,
          twistedRamanujan r.val l.val chi.val
              (ZMod.castHom hrlK (ZMod (r.val * l.val)) ((N : ZMod K) - x)) *
            twistedRamanujan r.val k.val chi.val
              (ZMod.castHom hrkK (ZMod (r.val * k.val)) x)) by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro x _hx
          ring]
    rw [twistedRamanujan_complete_matrix r.val l.val hrlK hrkK
      hcop_l hcop_k chi.val chi.property hInv (N : ZMod K)]
    by_cases heq : l.val = k.val
    · rw [if_pos heq, if_pos heq]
      have hrne : (r.val : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne r.val
      have hphine : (r.val.totient : ℂ) ≠ 0 := by
        exact_mod_cast NeZero.ne r.val.totient
      simp only [map_natCast]
      field_simp [hrne, hphine]
    · rw [if_neg heq, if_neg heq]
      ring
  have hdev := interval_deviation_norm_le g d A T
    (((r.val : ℝ) * V) * ((r.val : ℝ) * W)) hg hmean
  have hread :
      (∑ i ∈ Finset.range T, g ((A + i : ℕ) : ZMod K)) =
        ∑ i ∈ Finset.range T,
          activeTwistedLiteralTerm r l chi v
              ((N - (A + i) : ℕ) : ZMod (r.val * l.val)) *
            activeTwistedLiteralTerm r k chi w
              ((A + i : ℕ) : ZMod (r.val * k.val)) := by
    apply Finset.sum_congr rfl
    intro i hi
    have hiN : A + i ≤ N := by
      have := Finset.mem_range.mp hi
      omega
    simp only [g, map_sub, map_natCast, Nat.cast_sub hiN]
  rw [hread] at hdev
  change ‖_ - (T : ℂ) * activeActivePairMean r l k chi v w N‖ ≤ _ at hdev
  have hmod : ((T % K : ℕ) : ℝ) ≤ (K : ℝ) := by
    exact_mod_cast (Nat.mod_lt T (Nat.pos_of_ne_zero (NeZero.ne K))).le
  exact hdev.trans (by
    dsimp only [K]
    have henv : 0 ≤ ((r.val : ℝ) * V) * ((r.val : ℝ) * W) := by positivity
    nlinarith)

end GoldbachCircleMethodActiveActivePairwisePeriodV18317
