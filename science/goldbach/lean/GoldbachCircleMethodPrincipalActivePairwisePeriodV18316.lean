import GoldbachCircleMethodCanonicalAdjustedModelL2ReserveV18315
import GoldbachCircleMethodActualTwistedCompleteProjectionV18209

/-!
# Goldbach V1.8.316: principal/active pairwise-period adapter

This module begins the direct pairwise-period route around the enormous common
LCM.  A single principal Ramanujan denominator `q` and a single admitted
primitive-character/Ramanujan denominator pair `(r,l)` are completed only on
`lcm(q,r*l)`.  The exact projection and the incomplete-interval cost remain
visible.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodPrincipalActivePairwisePeriodV18316

open GoldbachCircleMethodActualCompanionCompleteDiagonalV18204
open GoldbachCircleMethodActualPrincipalTwistCrossDiagonalV18210
open GoldbachCircleMethodActualTwistedCompleteProjectionV18209
open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodFiniteResiduePrefixV1866
open GoldbachCircleMethodPairwisePeriodRemainderBoundV18206
open GoldbachCircleMethodPrincipalWindowBoundaryV18121
open GoldbachCircleMethodPrimitiveTwistedRamanujanSupportV18208

/-- One literal active-window denominator term, including the conductor scale
and the actual primitive twist. -/
noncomputable def activeTwistedLiteralTerm {Q : ℕ}
    (r l : PositiveLevel Q)
    (chi : {χ : DirichletCharacter ℂ r.val // χ.IsPrimitive})
    (w : ℕ → ℂ) (x : ZMod (r.val * l.val)) : ℂ :=
  ((r.val : ℂ) / (r.val.totient : ℂ)) *
    literalCoefficient r l w * twistedRamanujan r.val l.val chi.val x

/-- The active literal term costs at most one factor `r` beyond the supplied
weight bound.  No cancellation is used. -/
theorem activeTwistedLiteralTerm_norm_le {Q : ℕ}
    (r l : PositiveLevel Q)
    (chi : {χ : DirichletCharacter ℂ r.val // χ.IsPrimitive})
    (w : ℕ → ℂ) (W : ℝ) (hW : 0 ≤ W)
    (hw : ‖w (r.val * l.val)‖ ≤ W)
    (x : ZMod (r.val * l.val)) :
    ‖activeTwistedLiteralTerm r l chi w x‖ ≤ (r.val : ℝ) * W := by
  have ht :
      ‖literalCoefficient r l w *
          twistedRamanujan r.val l.val chi.val x‖ ≤ W := by
    unfold twistedRamanujan
    rw [show literalCoefficient r l w *
        (chi.val (ZMod.castHom (Nat.dvd_mul_right r.val l.val) (ZMod r.val) x) *
          unitCharacterSum l.val
            (ZMod.castHom (Nat.dvd_mul_left l.val r.val) (ZMod l.val) x)) =
        chi.val (ZMod.castHom (Nat.dvd_mul_right r.val l.val) (ZMod r.val) x) *
          (literalCoefficient r l w *
            unitCharacterSum l.val
              (ZMod.castHom (Nat.dvd_mul_left l.val r.val) (ZMod l.val) x)) by ring,
      norm_mul]
    exact (mul_le_mul (chi.val.norm_le_one _)
      (literal_term_norm_le r l w W hW hw _) (norm_nonneg _) zero_le_one).trans_eq
        (one_mul W)
  have hrpos : 0 < r.val := Nat.pos_of_ne_zero (NeZero.ne r.val)
  have hphi : (1 : ℝ) ≤ r.val.totient := by
    exact_mod_cast Nat.totient_pos.mpr hrpos
  have hscale : ‖(r.val : ℂ) / (r.val.totient : ℂ)‖ ≤ (r.val : ℝ) := by
    rw [norm_div, Complex.norm_natCast, Complex.norm_natCast]
    exact div_le_self (Nat.cast_nonneg r.val) hphi
  unfold activeTwistedLiteralTerm
  rw [show ((r.val : ℂ) / (r.val.totient : ℂ)) *
      literalCoefficient r l w * twistedRamanujan r.val l.val chi.val x =
      ((r.val : ℂ) / (r.val.totient : ℂ)) *
        (literalCoefficient r l w * twistedRamanujan r.val l.val chi.val x) by ring,
    norm_mul]
  exact mul_le_mul hscale ht (norm_nonneg _) (Nat.cast_nonneg _)

/-- One principal/active pair is centered on its exact Fourier projection and
completed only on `lcm(q,r*l)`. -/
theorem principal_active_pair_interval_norm_le {Q : ℕ}
    (hQ : 1 ≤ Q)
    (r l q : PositiveLevel Q)
    (_hadm : r.val * l.val ≤ Q)
    (hcop : Nat.Coprime r.val l.val)
    (chi : {χ : DirichletCharacter ℂ r.val // χ.IsPrimitive})
    (v w : ℕ → ℂ) (N A T : ℕ) (hend : A + T ≤ N + 1)
    (V W : ℝ) (hV : 0 ≤ V) (hW : 0 ≤ W)
    (hv : ‖v q.val‖ ≤ V) (hw : ‖w (r.val * l.val)‖ ≤ W) :
    ‖(∑ i ∈ Finset.range T,
        (literalCoefficient (oneLevel hQ) q v *
          unitCharacterSum q.val ((N - (A + i) : ℕ) : ZMod q.val)) *
        activeTwistedLiteralTerm r l chi w
          ((A + i : ℕ) : ZMod (r.val * l.val))) -
      (T : ℂ) *
        (if q.val = r.val * l.val then
          literalCoefficient (oneLevel hQ) q v *
            ((r.val : ℂ) / (r.val.totient : ℂ)) *
            literalCoefficient r l w *
            twistedRamanujan r.val l.val chi.val
              ((N : ℕ) : ZMod (r.val * l.val))
        else 0)‖ ≤
      2 * (Nat.lcm q.val (r.val * l.val) : ℝ) * V *
        ((r.val : ℝ) * W) := by
  let K := Nat.lcm q.val (r.val * l.val)
  let _ : NeZero K :=
    ⟨Nat.lcm_ne_zero (NeZero.ne q.val)
      (Nat.mul_ne_zero (NeZero.ne r.val) (NeZero.ne l.val))⟩
  have hqK : q.val ∣ K := Nat.dvd_lcm_left _ _
  have hrlK : r.val * l.val ∣ K := Nat.dvd_lcm_right _ _
  let g : ZMod K → ℂ := fun x =>
    (literalCoefficient (oneLevel hQ) q v *
      unitCharacterSum q.val
        (ZMod.castHom hqK (ZMod q.val) ((N : ZMod K) - x))) *
    activeTwistedLiteralTerm r l chi w
      (ZMod.castHom hrlK (ZMod (r.val * l.val)) x)
  let d : ℂ :=
    if q.val = r.val * l.val then
      literalCoefficient (oneLevel hQ) q v *
        ((r.val : ℂ) / (r.val.totient : ℂ)) *
        literalCoefficient r l w *
        twistedRamanujan r.val l.val chi.val
          (ZMod.castHom hrlK (ZMod (r.val * l.val)) (N : ZMod K))
    else 0
  have hg : ∀ x, ‖g x‖ ≤ V * ((r.val : ℝ) * W) := by
    intro x
    unfold g
    rw [norm_mul]
    exact mul_le_mul
      (literal_term_norm_le (oneLevel hQ) q v V hV
        (by simpa [oneLevel] using hv) _)
      (activeTwistedLiteralTerm_norm_le r l chi w W hW hw _)
      (norm_nonneg _) hV
  have hmean : (∑ x : ZMod K, g x) = (K : ℂ) * d := by
    unfold g d activeTwistedLiteralTerm
    rw [show (∑ x : ZMod K,
        (literalCoefficient (oneLevel hQ) q v *
          unitCharacterSum q.val
            (ZMod.castHom hqK (ZMod q.val) ((N : ZMod K) - x))) *
        (((r.val : ℂ) / (r.val.totient : ℂ)) *
          literalCoefficient r l w *
          twistedRamanujan r.val l.val chi.val
            (ZMod.castHom hrlK (ZMod (r.val * l.val)) x))) =
        (literalCoefficient (oneLevel hQ) q v *
          ((r.val : ℂ) / (r.val.totient : ℂ)) *
          literalCoefficient r l w) *
        (∑ x : ZMod K,
          unitCharacterSum q.val
            (ZMod.castHom hqK (ZMod q.val) ((N : ZMod K) - x)) *
          twistedRamanujan r.val l.val chi.val
            (ZMod.castHom hrlK (ZMod (r.val * l.val)) x)) by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro x _hx
          ring]
    rw [twisted_ramanujan_complete_matrix r.val l.val hqK hrlK
      hcop chi.val chi.property (N : ZMod K)]
    by_cases heq : q.val = r.val * l.val
    · rw [if_pos heq, if_pos heq]
      ring
    · rw [if_neg heq, if_neg heq]
      ring
  have hdev := interval_deviation_norm_le g d A T
    (V * ((r.val : ℝ) * W)) hg hmean
  have hread :
      (∑ i ∈ Finset.range T, g ((A + i : ℕ) : ZMod K)) =
        ∑ i ∈ Finset.range T,
          (literalCoefficient (oneLevel hQ) q v *
            unitCharacterSum q.val ((N - (A + i) : ℕ) : ZMod q.val)) *
          activeTwistedLiteralTerm r l chi w
            ((A + i : ℕ) : ZMod (r.val * l.val)) := by
    apply Finset.sum_congr rfl
    intro i hi
    have hiN : A + i ≤ N := by
      have := Finset.mem_range.mp hi
      omega
    simp only [g, map_sub, map_natCast, Nat.cast_sub hiN]
  rw [hread] at hdev
  have hdread : d =
      if q.val = r.val * l.val then
        literalCoefficient (oneLevel hQ) q v *
          ((r.val : ℂ) / (r.val.totient : ℂ)) *
          literalCoefficient r l w *
          twistedRamanujan r.val l.val chi.val
            ((N : ℕ) : ZMod (r.val * l.val))
      else 0 := by
    unfold d
    split_ifs
    · congr 1
      simp only [map_natCast]
    · rfl
  rw [hdread] at hdev
  have hmod : ((T % K : ℕ) : ℝ) ≤ (K : ℝ) := by
    exact_mod_cast (Nat.mod_lt T (Nat.pos_of_ne_zero (NeZero.ne K))).le
  exact hdev.trans (by
    dsimp only [K]
    have hVW : 0 ≤ V * ((r.val : ℝ) * W) := by positivity
    nlinarith)

end GoldbachCircleMethodPrincipalActivePairwisePeriodV18316
