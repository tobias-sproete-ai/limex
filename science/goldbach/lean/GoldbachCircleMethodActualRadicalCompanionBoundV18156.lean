import GoldbachCircleMethodBumpDecayRadicalEnvelopeV18155

set_option autoImplicit false
open scoped BigOperators Classical ContDiff
open MeasureTheory
open GoldbachCircleMethodBumpFourierRepresentationV18143
open GoldbachCircleMethodLogCutoffPresieveBindingV18120
open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodFiniteCompanionBindingV18118
open GoldbachCircleMethodLocalEulerRadicalBoundsV18149
open GoldbachCircleMethodActualCompanionRadicalIntegralV18154
open GoldbachCircleMethodBumpDecayRadicalEnvelopeV18155
namespace GoldbachCircleMethodActualRadicalCompanionBoundV18156

theorem logarithmic_constant_absorption {R : ℝ} (hR : 2 ≤ R) :
    1+Real.log R ≤ (1+1/Real.log 2)*Real.log R := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl : Real.log 2 ≤ Real.log R := Real.log_le_log (by norm_num) hR
  have hb : (1 : ℝ) ≤ Real.log R/Real.log 2 := (le_div_iff₀ hl2).mpr (by simpa using hl)
  calc
    _ ≤ Real.log R/Real.log 2+Real.log R := by linarith
    _ = _ := by ring

noncomputable def bumpEnvelopeConstant (B : ℝ) : ℝ :=
  Real.exp 1*(1+1/Real.log 2)*B

theorem bumpEnvelopeConstant_nonneg {B : ℝ} (hB : 0 ≤ B) :
    0 ≤ bumpEnvelopeConstant B := by
  unfold bumpEnvelopeConstant
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  positivity

/-- Explicit admissible constant, depending only on the fixed bump. -/
theorem actual_radical_companion_bound_given_decay {G : ℝ → ℝ}
    (hc : HasCompactSupport G) (hd : ContDiff ℝ ∞ G)
    (hG : ∀ t : ℝ, 2 < t → G t = 0) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ ξ : ℝ, ‖bumpFourierWeight G ξ‖ ≤ B/(1+|ξ|)^10)
    {R : ℝ} (hR : 2 ≤ R) (r : PositiveLevel ⌊R^2⌋₊)
    {N : ℕ} (hN : 0 < N) (hcop : r.val.Coprime N) :
    ((r.val : ℝ)/(r.val.totient : ℝ))*‖finiteCompanion r N (logWeight R G)‖ ≤
      bumpEnvelopeConstant B*radicalMajorant R N := by
  have hR1 : 1 < R := lt_of_lt_of_le (by norm_num) hR
  let I : ℝ := ∫ ξ : ℝ, tenthDecay ξ*radicalEnvelope R ξ N
  have hI : 0 ≤ I := integral_nonneg
    (fun ξ => mul_nonneg (tenthDecay_nonneg ξ) (radicalEnvelope_nonneg hR1 ξ N))
  have hK : 0 ≤ (Real.exp 1*(1+Real.log R))*(N.divisors.card : ℝ) := by
    have hl := Real.log_pos hR1
    positivity
  have hb := actual_companion_radical_integral_bound hc hd hG hR1 r hN hcop
  have hi := actual_weighted_integral_le_decay hc hd hR1 N hB
  calc
    _ ≤ ((Real.exp 1*(1+Real.log R))*(N.divisors.card : ℝ))*(B*I) :=
      hb.trans (mul_le_mul_of_nonneg_left hi hK)
    _ ≤ ((Real.exp 1*((1+1/Real.log 2)*Real.log R))*(N.divisors.card : ℝ))*(B*I) := by
      apply mul_le_mul_of_nonneg_right _ (mul_nonneg hB0 hI)
      apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
      exact mul_le_mul_of_nonneg_left (logarithmic_constant_absorption hR) (Real.exp_pos _).le
    _ = _ := by unfold bumpEnvelopeConstant radicalMajorant; dsimp [I]; ring

/-- Uniform in R,r,N. The constant is constructed from the actual bump,
not supplied as an unproved analytic premise. -/
theorem actual_radical_companion_bound {G : ℝ → ℝ}
    (hc : HasCompactSupport G) (hd : ContDiff ℝ ∞ G)
    (hG : ∀ t : ℝ, 2 < t → G t = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (R : ℝ) (_hR : 2 ≤ R)
      (r : PositiveLevel ⌊R^2⌋₊) (N : ℕ), 0 < N →
      r.val.Coprime N →
      ((r.val : ℝ)/(r.val.totient : ℝ))*‖finiteCompanion r N (logWeight R G)‖ ≤
        C*radicalMajorant R N := by
  obtain ⟨B,hB0,hB⟩ := actual_bump_decay_tenth hc hd
  refine ⟨bumpEnvelopeConstant B,bumpEnvelopeConstant_nonneg hB0,?_⟩
  intro R hR r N hN hcop
  exact actual_radical_companion_bound_given_decay hc hd hG hB0 hB hR r hN hcop

/-- The coprime indicator removes precisely the excluded cases; it does
not assert their unmasked companion is small or zero. -/
theorem actual_coprime_indicator_radical_bound {G : ℝ → ℝ}
    (hc : HasCompactSupport G) (hd : ContDiff ℝ ∞ G)
    (hG : ∀ t : ℝ, 2 < t → G t = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (R : ℝ) (_hR : 2 ≤ R)
      (r : PositiveLevel ⌊R^2⌋₊) (N : ℕ), 0 < N →
      (if r.val.Coprime N then
        ((r.val : ℝ)/(r.val.totient : ℝ))*‖finiteCompanion r N (logWeight R G)‖ else 0) ≤
        C*radicalMajorant R N := by
  obtain ⟨C,hC,hbound⟩ := actual_radical_companion_bound hc hd hG
  refine ⟨C,hC,?_⟩
  intro R hR r N hN
  by_cases hcop : r.val.Coprime N
  · rw [if_pos hcop]
    exact hbound R hR r N hN hcop
  · rw [if_neg hcop]
    exact mul_nonneg hC (radicalMajorant_nonneg (lt_of_lt_of_le (by norm_num) hR) N)

end GoldbachCircleMethodActualRadicalCompanionBoundV18156
