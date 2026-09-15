import GoldbachCircleMethodActualHalfScaleCorrelationV18177
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.MeasureTheory.Integral.Bochner.Basic

set_option autoImplicit false
open scoped BigOperators Classical ArithmeticFunction
open MeasureTheory
open ArithmeticFunction
open GoldbachCircleMethodLocalEulerRadicalBoundsV18149
open GoldbachCircleMethodBumpDecayRadicalEnvelopeV18155
open GoldbachCircleMethodRadicalArithmeticClassV18159
namespace GoldbachCircleMethodDirectLambdaRadicalDominationV18178

/-- The fixed positive mass of the existing tenth-decay weight. -/
noncomputable def tenthDecayMass : ℝ := ∫ ξ : ℝ, tenthDecay ξ

/-- Positivity uses continuity, nonnegativity, integrability and the nonzero value at zero;
no numerical evaluation of the integral is used. -/
theorem tenthDecayMass_pos : 0 < tenthDecayMass := by
  unfold tenthDecayMass
  apply integral_pos_of_integrable_nonneg_nonzero (x := 0)
  · unfold tenthDecay
    exact continuous_const.div (by fun_prop) (fun ξ => by positivity)
  · exact tenthDecay_integrable
  · exact fun ξ => tenthDecay_nonneg ξ
  · norm_num [tenthDecay]

/-- On a prime power below `X`, the actual local radical factor uniformly dominates
the logarithmic ratio `log p / log X`. -/
theorem radicalLocal_ge_log_ratio {X : ℕ} (hX : 2 ≤ X)
    {R : ℝ} (hR : 1 < R) (hRX : R ≤ (X : ℝ)) (ξ : ℝ)
    {p : ℕ} (hp : p.Prime) (hpX : p ≤ X) :
    Real.log (p : ℝ) / Real.log (X : ℝ) ≤ radicalLocal R ξ p := by
  have hlogp : 0 ≤ Real.log (p : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hp.one_le)
  have hlogX : 0 < Real.log (X : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have hlogR : 0 < Real.log R := Real.log_pos hR
  have hlogpX : Real.log (p : ℝ) ≤ Real.log (X : ℝ) :=
    Real.log_le_log (by exact_mod_cast hp.pos) (by exact_mod_cast hpX)
  have hlogRX : Real.log R ≤ Real.log (X : ℝ) :=
    Real.log_le_log (lt_trans zero_lt_one hR) hRX
  have hratio0 : 0 ≤ Real.log (p : ℝ) / Real.log R :=
    div_nonneg hlogp hlogR.le
  have hfactor : 1 ≤ 10 * (1 + |ξ|) := by
    nlinarith [abs_nonneg ξ]
  unfold radicalLocal
  apply le_min
  · exact (div_le_one hlogX).2 hlogpX
  · calc
      Real.log (p : ℝ) / Real.log (X : ℝ) ≤
          Real.log (p : ℝ) / Real.log R :=
        div_le_div_of_nonneg_left hlogp hlogR hlogRX
      _ ≤ 10 * (1 + |ξ|) * Real.log (p : ℝ) / Real.log R := by
        have hm := mul_le_mul_of_nonneg_right hfactor hratio0
        field_simp [ne_of_gt hlogR] at hm ⊢
        nlinarith

/-- The existing integral majorant has an explicit lower bound on every positive
prime power.  This is not a lower-bound sieve statement. -/
theorem radicalMajorant_prime_power_lower_bound {X : ℕ} (hX : 2 ≤ X)
    {R : ℝ} (hR : 1 < R) (hRX : R ≤ (X : ℝ))
    {p k : ℕ} (hp : p.Prime) (hk : 0 < k) (hpowX : p ^ k ≤ X) :
    2 * Real.log R * (Real.log (p : ℝ) / Real.log (X : ℝ)) * tenthDecayMass ≤
      radicalMajorant R (p ^ k) := by
  have hpX : p ≤ X := (Nat.le_pow hk).trans hpowX
  have hratio0 : 0 ≤ Real.log (p : ℝ) / Real.log (X : ℝ) := by positivity
  have hJ0 : 0 ≤ tenthDecayMass := tenthDecayMass_pos.le
  have hi : (Real.log (p : ℝ) / Real.log (X : ℝ)) * tenthDecayMass ≤
      ∫ ξ : ℝ, tenthDecay ξ * radicalEnvelope R ξ (p ^ k) := by
    unfold tenthDecayMass
    rw [← integral_const_mul]
    apply integral_mono
      (tenthDecay_integrable.const_mul (Real.log (p : ℝ) / Real.log (X : ℝ)))
      (weighted_tenth_radical_integrable hR (p ^ k))
    intro ξ
    simpa only [radicalEnvelope_prime_power R ξ hp hk, mul_comm] using
      mul_le_mul_of_nonneg_left
        (radicalLocal_ge_log_ratio hX hR hRX ξ hp hpX) (tenthDecay_nonneg ξ)
  have hk2 : (2 : ℝ) ≤ (k + 1 : ℕ) := by exact_mod_cast (show 2 ≤ k + 1 by omega)
  have hbase0 : 0 ≤ Real.log R *
      ((Real.log (p : ℝ) / Real.log (X : ℝ)) * tenthDecayMass) :=
    mul_nonneg (Real.log_pos hR).le (mul_nonneg hratio0 hJ0)
  calc
    2 * Real.log R * (Real.log (p : ℝ) / Real.log (X : ℝ)) * tenthDecayMass =
        2 * (Real.log R *
          ((Real.log (p : ℝ) / Real.log (X : ℝ)) * tenthDecayMass)) := by ring
    _ ≤ ((k + 1 : ℕ) : ℝ) * (Real.log R *
          ((Real.log (p : ℝ) / Real.log (X : ℝ)) * tenthDecayMass)) :=
      mul_le_mul_of_nonneg_right hk2 hbase0
    _ ≤ ((k + 1 : ℕ) : ℝ) * (Real.log R *
          (∫ ξ : ℝ, tenthDecay ξ * radicalEnvelope R ξ (p ^ k))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hi (Real.log_pos hR).le) (Nat.cast_nonneg _)
    _ = ((k + 1 : ℕ) : ℝ) * Real.log R *
          (∫ ξ : ℝ, tenthDecay ξ * radicalEnvelope R ξ (p ^ k)) := by ring
    _ = radicalMajorant R (p ^ k) := by
      unfold radicalMajorant
      rw [card_divisors_prime_power hp]

/-- Direct domination of the genuine von-Mangoldt weight by the existing radical
majorant.  The constant is explicit in the unevaluated positive mass. -/
theorem vonMangoldt_le_radicalMajorant {X n : ℕ} (hX : 2 ≤ X)
    {R : ℝ} (hR : 1 < R) (hRX : R ≤ (X : ℝ)) (hnX : n ≤ X) :
    Λ n ≤ Real.log (X : ℝ) /
        (2 * Real.log R * tenthDecayMass) * radicalMajorant R n := by
  have hlogX : 0 < Real.log (X : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have hden : 0 < 2 * Real.log R * tenthDecayMass :=
    mul_pos (mul_pos (by norm_num) (Real.log_pos hR)) tenthDecayMass_pos
  have hcoef : 0 ≤ Real.log (X : ℝ) /
      (2 * Real.log R * tenthDecayMass) := div_nonneg hlogX.le hden.le
  by_cases hn : IsPrimePow n
  · obtain ⟨p,k,hp,hk,rfl⟩ := (isPrimePow_nat_iff _).1 hn
    rw [vonMangoldt_apply_pow hk.ne',vonMangoldt_apply_prime hp]
    have hlower := radicalMajorant_prime_power_lower_bound hX hR hRX hp hk hnX
    calc
      Real.log (p : ℝ) =
          (Real.log (X : ℝ) / (2 * Real.log R * tenthDecayMass)) *
            (2 * Real.log R * (Real.log (p : ℝ) / Real.log (X : ℝ)) *
              tenthDecayMass) := by
        field_simp [ne_of_gt hlogX, ne_of_gt (Real.log_pos hR), ne_of_gt tenthDecayMass_pos]
      _ ≤ (Real.log (X : ℝ) / (2 * Real.log R * tenthDecayMass)) *
          radicalMajorant R (p ^ k) := mul_le_mul_of_nonneg_left hlower hcoef
  · rw [(vonMangoldt_eq_zero_iff).2 hn]
    exact mul_nonneg hcoef (radicalMajorant_nonneg hR n)

/-- Finite companion transfer.  Natural subtraction outside the companion range
causes no gap because `m - n ≤ m ≤ X`, including the zero case. -/
theorem finite_lambda_companion_le_radical {X m : ℕ} (hX : 2 ≤ X)
    (hmX : m ≤ X) {R : ℝ} (hR : 1 < R) (hRX : R ≤ (X : ℝ))
    (I : Finset ℕ) :
    (∑ n ∈ I, radicalMajorant R n * Λ (m - n)) ≤
      (Real.log (X : ℝ) / (2 * Real.log R * tenthDecayMass)) *
        (∑ n ∈ I, radicalMajorant R n * radicalMajorant R (m - n)) := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n hn
  calc
    radicalMajorant R n * Λ (m - n) ≤
        radicalMajorant R n *
          (Real.log (X : ℝ) / (2 * Real.log R * tenthDecayMass) *
            radicalMajorant R (m - n)) :=
      mul_le_mul_of_nonneg_left
        (vonMangoldt_le_radicalMajorant hX hR hRX ((Nat.sub_le m n).trans hmX))
        (radicalMajorant_nonneg hR n)
    _ = Real.log (X : ℝ) / (2 * Real.log R * tenthDecayMass) *
        (radicalMajorant R n * radicalMajorant R (m - n)) := by ring

end GoldbachCircleMethodDirectLambdaRadicalDominationV18178
