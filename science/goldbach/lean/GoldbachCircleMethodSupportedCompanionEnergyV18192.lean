import GoldbachCircleMethodDivisorSubpowerExistenceV18191

/-! Actual supported companion energy; V191 divisor existence is instantiated.
Native source candidate: accepted status requires actual run and independent review.
-/
set_option autoImplicit false
open scoped BigOperators Classical ContDiff
open MeasureTheory
open GoldbachCircleMethodFiniteCompanionBindingV18118
open GoldbachCircleMethodLogCutoffPresieveBindingV18120
open GoldbachCircleMethodLocalEulerRadicalBoundsV18149
open GoldbachCircleMethodActualCompanionRadicalIntegralV18154
open GoldbachCircleMethodPrincipalWindowBoundaryV18121
open GoldbachCircleMethodBumpDecayRadicalEnvelopeV18155
open GoldbachCircleMethodSupportedModelErrorConvolutionV18182
open GoldbachCircleMethodUncorrectedSupportedErrorConvolutionV18184
open GoldbachCircleMethodSupportedResidualParsevalV18190
open GoldbachCircleMethodActiveExceptionalCenteringV18129
open GoldbachCircleMethodDivisorSubpowerExistenceV18191

namespace GoldbachCircleMethodSupportedCompanionEnergyV18192

theorem radicalMajorant_le_divisor_mass {R : ℝ} (hR : 1 < R) (n : ℕ) :
    radicalMajorant R n ≤
      (n.divisors.card : ℝ) * Real.log R * (∫ ξ : ℝ, tenthDecay ξ) := by
  unfold radicalMajorant
  apply mul_le_mul_of_nonneg_left _
    (mul_nonneg (Nat.cast_nonneg _) (Real.log_pos hR).le)
  apply integral_mono (weighted_tenth_radical_integrable hR n) tenthDecay_integrable
  intro ξ
  exact mul_le_of_le_one_right (tenthDecay_nonneg ξ)
    (radicalEnvelope_le_one hR ξ n)

/-- This helper derives energy from a pointwise arithmetic divisor bound and
the actual radical envelope, not from a requested energy bound as premise. -/
theorem finite_energy_from_divisor_bound
    (B : ℕ) (hB : 2 ≤ B) (R eps K CB : ℝ)
    (hR : 2 ≤ R) (hRB : R ≤ (B : ℝ))
    (heps : 0 < eps) (hK : 1 ≤ K) (hCB : 0 ≤ CB)
    (hdiv : ∀ n : ℕ, 0 < n → (n.divisors.card : ℝ) ≤ K*(n : ℝ)^eps)
    (model : ℕ → ℂ)
    (hmodel : ∀ n ∈ blockCarrier B, ‖model n‖ ≤ CB*radicalMajorant R n) :
    (∑ n ∈ blockCarrier B, ‖blockInput B n + model n‖^2) ≤
      (B : ℝ) *
        ((1+CB*(∫ ξ : ℝ, tenthDecay ξ)*K)*(B : ℝ)^eps*Real.log (B : ℝ))^2 := by
  have hBr : (2 : ℝ) ≤ B := by exact_mod_cast hB
  have hR1 : 1 < R := by linarith
  have hlogB : 0 ≤ Real.log (B : ℝ) := Real.log_nonneg (by linarith)
  have hlogR : 0 ≤ Real.log R := (Real.log_pos hR1).le
  have hlogRB : Real.log R ≤ Real.log (B : ℝ) :=
    Real.log_le_log (by linarith) hRB
  have hI : 0 ≤ ∫ ξ : ℝ, tenthDecay ξ :=
    integral_nonneg tenthDecay_nonneg
  have hpow : 1 ≤ (B : ℝ)^eps :=
    Real.one_le_rpow (by linarith) heps.le
  have hKn : 0 ≤ K := by linarith
  let A := (1+CB*(∫ ξ : ℝ, tenthDecay ξ)*K)*(B : ℝ)^eps*Real.log (B : ℝ)
  have hp (n : ℕ) (hn : n ∈ blockCarrier B) :
      ‖blockInput B n + model n‖ ≤ A := by
    have hn' : B/2 < n ∧ n ≤ B := by
      simpa only [blockCarrier, Finset.mem_Ioc] using hn
    have hnp : 0 < n := by omega
    have hnr : (0 : ℝ) < n := by exact_mod_cast hnp
    have hnB : (n : ℝ) ≤ B := by exact_mod_cast hn'.2
    have htau : (n.divisors.card : ℝ) ≤ K*(B : ℝ)^eps :=
      (hdiv n hnp).trans
        (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow hnr.le hnB heps.le) hKn)
    have hr := radicalMajorant_le_divisor_mass hR1 n
    have hr' : radicalMajorant R n ≤
        K*(B : ℝ)^eps*Real.log (B : ℝ)*(∫ ξ : ℝ, tenthDecay ξ) := by
      apply hr.trans
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul htau hlogRB hlogR (by positivity)) hI
    have ha : ‖blockInput B n‖ ≤ Real.log (B : ℝ) :=
      (blockInput_norm_le_vonMangoldt B n).trans
        (ArithmeticFunction.vonMangoldt_le_log.trans
          (Real.log_le_log hnr hnB))
    have hm := (hmodel n hn).trans (mul_le_mul_of_nonneg_left hr' hCB)
    calc
      _ ≤ ‖blockInput B n‖ + ‖model n‖ := norm_add_le _ _
      _ ≤ Real.log (B : ℝ) +
        CB*(K*(B : ℝ)^eps*Real.log (B : ℝ)*(∫ ξ : ℝ, tenthDecay ξ)) :=
          add_le_add ha hm
      _ ≤ A := by
        dsimp [A]
        nlinarith [mul_le_mul_of_nonneg_right hpow hlogB]
  have hcard : (blockCarrier B).card ≤ B := by
    simp only [blockCarrier, Nat.card_Ioc]
    exact Nat.sub_le _ _
  calc
    _ ≤ ∑ _n ∈ blockCarrier B, A^2 := by
      apply Finset.sum_le_sum
      intro n hn
      exact pow_le_pow_left₀ (norm_nonneg _) (hp n hn) 2
    _ = ((blockCarrier B).card : ℝ)*A^2 := by simp
    _ ≤ (B : ℝ)*A^2 :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (sq_nonneg A)
    _ = _ := rfl

/-- Actual principal branch; the model constant is chosen before eps, and
the divisor constant is then uniform in every block and cutoff. -/
theorem actual_supported_principal_energy_bound {G : ℝ → ℝ}
    (hc : HasCompactSupport G) (hd : ContDiff ℝ ∞ G)
    (hG : ∀ t : ℝ, 2 < t → G t = 0) :
    ∃ CB : ℝ, 0 ≤ CB ∧ ∀ eps : ℝ, 0 < eps →
      ∃ K : ℝ, 1 ≤ K ∧ ∀ (B : ℕ), 2 ≤ B → ∀ R : ℝ,
        2 ≤ R → R ≤ (B : ℝ) →
        (∑ n ∈ blockCarrier B,
          ‖blockInput B n + supportedPrincipalModel B n R G‖^2) ≤
          (B : ℝ) *
            ((1+CB*(∫ ξ : ℝ, tenthDecay ξ)*K)*(B : ℝ)^eps*Real.log (B : ℝ))^2 := by
  obtain ⟨CB,hCB,hmodel⟩ := supported_principalModel_radical_bound hc hd hG
  refine ⟨CB,hCB,?_⟩
  intro eps heps
  obtain ⟨K,hK,hdiv⟩ := exists_divisors_card_le_const_mul_rpow heps
  refine ⟨K,hK,?_⟩
  intro B hB R hR hRB
  exact finite_energy_from_divisor_bound B hB R eps K CB hR hRB heps hK hCB hdiv
    (fun n => supportedPrincipalModel B n R G) (fun n _hn => hmodel R hR B n)

/-- Separate actual active branch, with the same b and character slot in
every summand. This is an energy bound, not an active Fourier residual bound. -/
theorem actual_supported_adjusted_energy_bound {G : ℝ → ℝ}
    (hc : HasCompactSupport G) (hd : ContDiff ℝ ∞ G)
    (hG : ∀ t : ℝ, 2 < t → G t = 0) :
    ∃ CB : ℝ, 0 ≤ CB ∧ ∀ eps : ℝ, 0 < eps →
      ∃ K : ℝ, 1 ≤ K ∧ ∀ (B : ℕ), 2 ≤ B → ∀ R : ℝ,
        2 ≤ R → R ≤ (B : ℝ) → ∀ b : ℝ, 0 ≤ b →
        ∀ e : CharacterSlot ⌊R^2⌋₊,
        (∑ n ∈ blockCarrier B,
          ‖blockInput B n + supportedAdjustedModel B n R b G e‖^2) ≤
          (B : ℝ) *
            ((1+CB*(∫ ξ : ℝ, tenthDecay ξ)*K)*(B : ℝ)^eps*Real.log (B : ℝ))^2 := by
  obtain ⟨CB,hCB,hmodel⟩ := supported_adjustedModel_radical_bound hc hd hG
  refine ⟨CB,hCB,?_⟩
  intro eps heps
  obtain ⟨K,hK,hdiv⟩ := exists_divisors_card_le_const_mul_rpow heps
  refine ⟨K,hK,?_⟩
  intro B hB R hR hRB b hb e
  exact finite_energy_from_divisor_bound B hB R eps K CB hR hRB heps hK hCB hdiv
    (fun n => supportedAdjustedModel B n R b G e)
    (fun n _hn => hmodel R hR B n b hb e)

end GoldbachCircleMethodSupportedCompanionEnergyV18192
