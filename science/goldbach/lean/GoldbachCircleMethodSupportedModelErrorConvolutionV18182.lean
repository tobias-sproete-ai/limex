import GoldbachCircleMethodEventualScaleActualErrorLambdaV18181

set_option autoImplicit false
open scoped BigOperators Classical ArithmeticFunction ContDiff
open GoldbachCircleMethodFiniteCompanionBindingV18118
open GoldbachCircleMethodLogCutoffPresieveBindingV18120
open GoldbachCircleMethodPrincipalWindowBoundaryV18121
open GoldbachCircleMethodExceptionalWeightBoundaryV18128
open GoldbachCircleMethodActiveExceptionalCenteringV18129
open GoldbachCircleMethodBumpDecayRadicalEnvelopeV18155
open GoldbachCircleMethodActualCharacterRadicalErrorV18157
open GoldbachCircleMethodActiveCharacterRadicalErrorV18158
open GoldbachCircleMethodRadicalCorrelationTransferV18161
open GoldbachCircleMethodBadPrimeProductComparisonV18165
open GoldbachCircleMethodMertensUniformConstantsV18168
open GoldbachCircleMethodBadPrimeUniformFrequencyV18169
open GoldbachCircleMethodGlobalSieveFiniteFactorV18173
open GoldbachCircleMethodMertensProductFromHarmonicV18174
open GoldbachCircleMethodDisjointPrimeFactorCompositionV18171
open GoldbachCircleMethodActualHalfScaleCorrelationV18177
open GoldbachCircleMethodDirectLambdaRadicalDominationV18178
open GoldbachCircleMethodFixedRhoPolynomialLossV18180
open GoldbachCircleMethodEventualScaleActualErrorLambdaV18181
namespace GoldbachCircleMethodSupportedModelErrorConvolutionV18182

/-- The actual V129 adjusted model with its original half-window support. -/
noncomputable def supportedAdjustedModel (M N : ℕ) (R b : ℝ)
    (G : ℝ → ℝ) (e : CharacterSlot ⌊R^2⌋₊) : ℂ :=
  if hR : 1 < R then
    if N ∈ Finset.Ioc (M / 2) M then
      adjustedModel ⌊R^2⌋₊ N (log_cutoff_contains_one R hR) b (logWeight R G) e
    else 0
  else 0

/-- The actual V129 adjusted centered error with the same support and the
literal local scale `H=M/R^4`. -/
noncomputable def supportedAdjustedError (M N : ℕ) (R : ℝ) (b : ℝ)
    (G : ℝ → ℝ) (e : CharacterSlot ⌊R^2⌋₊) : ℂ :=
  if N ∈ Finset.Ioc (M / 2) M then
    adjustedCenteredError ⌊R^2⌋₊ M N ((M : ℝ) / R^4) b
      (blockInput M) (logWeight R G) e
  else 0

theorem blockInput_norm_le_vonMangoldt (M n : ℕ) :
    ‖blockInput M n‖ ≤ Λ n := by
  unfold blockInput
  by_cases hn : n ∈ blockCarrier M
  · rw [if_pos hn]
    simpa only [Complex.norm_real,
      Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg] using
        (le_refl (Λ n))
  · rw [if_neg hn,norm_zero]
    exact ArithmeticFunction.vonMangoldt_nonneg

/-- The supported actual adjusted model has a radical-majorant constant fixed
by `G` before any scale, exponent or character slot is chosen. -/
theorem supported_adjustedModel_radical_bound {G : ℝ → ℝ}
    (hc : HasCompactSupport G) (hd : ContDiff ℝ ∞ G)
    (hG : ∀ t : ℝ, 2 < t → G t = 0) :
    ∃ CB : ℝ, 0 ≤ CB ∧ ∀ (R : ℝ), 2 ≤ R →
      ∀ (M N : ℕ) (b : ℝ), 0 ≤ b → ∀ (e : CharacterSlot ⌊R^2⌋₊),
      ‖supportedAdjustedModel M N R b G e‖ ≤ CB * radicalMajorant R N := by
  obtain ⟨C,hC,hcoef⟩ := actual_character_coefficients_radical_bound hc hd hG
  refine ⟨2*C,by positivity,?_⟩
  intro R hR M N b hb e
  have hR1 : 1 < R := lt_of_lt_of_le (by norm_num) hR
  unfold supportedAdjustedModel
  rw [dif_pos hR1]
  by_cases hn : N ∈ Finset.Ioc (M / 2) M
  · rw [if_pos hn]
    have hN : 0 < N := by
      simp only [Finset.mem_Ioc] at hn
      omega
    let hQ : 1 ≤ ⌊R^2⌋₊ := log_cutoff_contains_one R hR1
    let chiOne : {χ : DirichletCharacter ℂ (oneLevel hQ).val // χ.IsPrimitive} := by
      change {χ : DirichletCharacter ℂ 1 // χ.IsPrimitive}
      exact ⟨1,DirichletCharacter.isPrimitive_one_level_one⟩
    have hp0 := hcoef R hR (oneLevel hQ) N hN chiOne
    have hchi : chiOne.val (N : ZMod (oneLevel hQ).val) = 1 := by
      change (1 : DirichletCharacter ℂ 1) (N : ZMod 1) = 1
      exact level_one_character_value 1 N
    have hprincipal : windowCoefficient (oneLevel hQ) N (logWeight R G) chiOne =
        finiteCompanion (oneLevel hQ) N (logWeight R G) := by
      unfold windowCoefficient
      rw [hchi]
      simp only [oneLevel,Nat.totient_one,Nat.cast_one,div_one,one_mul]
    have hp : ‖finiteCompanion (oneLevel hQ) N (logWeight R G)‖ ≤
        C * radicalMajorant R N := by
      rw [hprincipal] at hp0
      exact hp0
    have he := hcoef R hR e.1 N hN e.2
    have hrad : 0 ≤ radicalMajorant R N := radicalMajorant_nonneg hR1 N
    have hpower := power_weight_abs_le_one M N b hb hn
    have hsecond :
        ‖windowCoefficient e.1 N (logWeight R G) e.2 * (powerWeight b N : ℂ)‖ ≤
          C * radicalMajorant R N := by
      rw [norm_mul,Complex.norm_real]
      calc
        ‖windowCoefficient e.1 N (logWeight R G) e.2‖ * |powerWeight b N| ≤
            (C * radicalMajorant R N) * 1 :=
          mul_le_mul he hpower (abs_nonneg _) (mul_nonneg hC hrad)
        _ = C * radicalMajorant R N := mul_one _
    unfold adjustedModel
    calc
      _ ≤ ‖finiteCompanion (oneLevel hQ) N (logWeight R G)‖ +
          ‖windowCoefficient e.1 N (logWeight R G) e.2 * (powerWeight b N : ℂ)‖ :=
        norm_sub_le _ _
      _ ≤ C * radicalMajorant R N + C * radicalMajorant R N := add_le_add hp hsecond
      _ = (2*C) * radicalMajorant R N := by ring
  · rw [if_neg hn,norm_zero]
    exact mul_nonneg (by positivity) (radicalMajorant_nonneg hR1 N)

/-- The V177 radical-radical companion at the genuine fixed power scale. -/
theorem actual_half_scale_HH_power_bound
    (D c CH : ℝ) (hD : 0 ≤ D) (hCH : 0 ≤ CH)
    (hweighted : ∀ (X : ℕ), 2 ≤ X → ∀ t : ℝ, 2 ≤ t → t ≤ (X : ℝ) →
      |prefixLogMoment X t - Real.log t| ≤ D)
    (hharmonic : ∀ (X : ℕ), 2 ≤ X → ∀ t : ℝ, 2 ≤ t → t ≤ (X : ℝ) →
      |prefixHarmonicMoment X t - Real.log (Real.log t) - c| ≤ D / Real.log t)
    {M m : ℕ} (hM : 16 ≤ M) (hmlower : 5 * M ≤ 4 * m)
    (hmupper : 4 * m ≤ 7 * M)
    {rho : ℝ} (hrho : 0 < rho) (hrho1 : rho ≤ 1)
    (hsource : ∀ ξ η : ℝ,
      arithmeticCorrelation ((M : ℝ)^rho) ξ η (Finset.Ioc (M / 2) M) m ≤
        CH * ((M : ℝ) / 2) * finiteSieveProduct m (M / 2) *
          goodBadProduct ((M : ℝ)^rho) ξ η m (M / 2)) :
    (∑ n ∈ Finset.Ioc (M / 2) M,
      radicalMajorant ((M : ℝ)^rho) n * radicalMajorant ((M : ℝ)^rho) (m - n)) ≤
      128 * CH * (mertensProductConstant D c)^2 *
        (oneFrequencyConstant D c)^2 *
        (∫ ξ : ℝ, secondMomentDecay ξ)^2 * (M : ℝ) *
        arithmeticFactor m / rho^2 := by
  have hs := fixedRho_scale_admission hM hrho hrho1
  have hbase := actual_half_scale_correlation_bound D c CH hD hCH hweighted hharmonic
    hM hmlower hmupper hs.1 hs.2 hsource
  rw [fixedRho_log_ratio hM hrho] at hbase
  calc
    _ ≤ 128 * CH * (mertensProductConstant D c)^2 *
        (oneFrequencyConstant D c)^2 *
        (∫ ξ : ℝ, secondMomentDecay ξ)^2 * (M : ℝ) *
        arithmeticFactor m * (1 / rho)^2 := hbase
    _ = 128 * CH * (mertensProductConstant D c)^2 *
        (oneFrequencyConstant D c)^2 *
        (∫ ξ : ℝ, secondMomentDecay ξ)^2 * (M : ℝ) *
        arithmeticFactor m / rho^2 := by
      field_simp [hrho.ne']

/-- Literal finite `E*(a+B)` norm majorant.  Both constants are fixed by `G`
before `rho`; the actual mass estimate and all source inputs remain hypotheses. -/
theorem eventual_supported_actual_error_model_lambda_bound {G : ℝ → ℝ}
    (hc : HasCompactSupport G) (hd : ContDiff ℝ ∞ G)
    (hG : ∀ t : ℝ, 2 < t → G t = 0) :
    ∃ CE : ℝ, 0 ≤ CE ∧ ∃ CB : ℝ, 0 ≤ CB ∧
      ∀ (D c CH : ℝ) (_hD : 0 ≤ D) (_hCH : 0 ≤ CH)
        (_hweighted : ∀ (X : ℕ), 2 ≤ X → ∀ t : ℝ, 2 ≤ t → t ≤ (X : ℝ) →
          |prefixLogMoment X t - Real.log t| ≤ D)
        (_hharmonic : ∀ (X : ℕ), 2 ≤ X → ∀ t : ℝ, 2 ≤ t → t ≤ (X : ℝ) →
          |prefixHarmonicMoment X t - Real.log (Real.log t) - c| ≤ D / Real.log t)
        (rho : ℝ) (_hrho : 0 < rho) (_hrho1 : rho ≤ 1),
      ∃ M₀ : ℕ, ∀ {M m : ℕ} (b eta : ℝ)
        (e : CharacterSlot ⌊((M : ℝ)^rho)^2⌋₊),
        M₀ ≤ M → 5 * M ≤ 4 * m → 4 * m ≤ 7 * M → 0 ≤ b → 0 ≤ eta →
        (∀ ξ η : ℝ,
          arithmeticCorrelation ((M : ℝ)^rho) ξ η (Finset.Ioc (M / 2) M) m ≤
            CH * ((M : ℝ) / 2) * finiteSieveProduct m (M / 2) *
              goodBadProduct ((M : ℝ)^rho) ξ η m (M / 2)) →
        (∀ n ∈ Finset.Ioc (M / 2) M,
          activeFluctuationMass ⌊((M : ℝ)^rho)^2⌋₊ M n
            ((M : ℝ) / ((M : ℝ)^rho)^4) b (blockInput M) e ≤ eta) →
        (∑ n ∈ Finset.Ioc (M / 2) M,
          ‖supportedAdjustedError M n ((M : ℝ)^rho) b G e‖ *
            (‖blockInput M (m - n)‖ +
              ‖supportedAdjustedModel M (m - n) ((M : ℝ)^rho) b G e‖)) ≤
          CE * eta *
            ((128 * CH * (mertensProductConstant D c)^2 *
                (oneFrequencyConstant D c)^2 *
                (∫ ξ : ℝ, secondMomentDecay ξ)^2 / tenthDecayMass) *
              (M : ℝ) * arithmeticFactor m / rho^3 +
             CB * (128 * CH * (mertensProductConstant D c)^2 *
                (oneFrequencyConstant D c)^2 *
                (∫ ξ : ℝ, secondMomentDecay ξ)^2) *
              (M : ℝ) * arithmeticFactor m / rho^2) := by
  obtain ⟨CE,hCE,herror⟩ := actual_adjusted_error_radical_bound hc hd hG
  obtain ⟨CB,hCB,hmodel⟩ := supported_adjustedModel_radical_bound hc hd hG
  refine ⟨CE,hCE,CB,hCB,?_⟩
  intro D c CH hD hCH hweighted hharmonic rho hrho hrho1
  obtain ⟨M₀,hscale⟩ := fixedRho_eventual_scale_two hrho
  refine ⟨M₀,?_⟩
  intro M m b eta e hM₀ hmlower hmupper hb heta hsource hmass
  have hs := hscale M hM₀
  have hR1 := (fixedRho_scale_admission hs.1 hrho hrho1).1
  have hLambda := actual_half_scale_lambda_power_bound D c CH hD hCH hweighted hharmonic
    hs.1 hmlower hmupper hrho hrho1 hsource
  have hHH := actual_half_scale_HH_power_bound D c CH hD hCH hweighted hharmonic
    hs.1 hmlower hmupper hrho hrho1 hsource
  have hpoint (n : ℕ) (hn : n ∈ Finset.Ioc (M / 2) M) :
      ‖supportedAdjustedError M n ((M : ℝ)^rho) b G e‖ *
          (‖blockInput M (m - n)‖ +
            ‖supportedAdjustedModel M (m - n) ((M : ℝ)^rho) b G e‖) ≤
        (CE * eta) * radicalMajorant ((M : ℝ)^rho) n *
          (Λ (m - n) + CB * radicalMajorant ((M : ℝ)^rho) (m - n)) := by
    have hnpos : 0 < n := by
      simp only [Finset.mem_Ioc] at hn
      omega
    have herr0 := herror ((M : ℝ)^rho) hs.2 M n hnpos
      ((M : ℝ) / ((M : ℝ)^rho)^4) b (blockInput M) e
    have hrad : 0 ≤ radicalMajorant ((M : ℝ)^rho) n :=
      radicalMajorant_nonneg hR1 n
    have herr : ‖supportedAdjustedError M n ((M : ℝ)^rho) b G e‖ ≤
        (CE * eta) * radicalMajorant ((M : ℝ)^rho) n := by
      rw [supportedAdjustedError,if_pos hn]
      calc
        _ ≤ CE * radicalMajorant ((M : ℝ)^rho) n *
            activeFluctuationMass ⌊((M : ℝ)^rho)^2⌋₊ M n
              ((M : ℝ) / ((M : ℝ)^rho)^4) b (blockInput M) e := herr0
        _ ≤ CE * radicalMajorant ((M : ℝ)^rho) n * eta :=
          mul_le_mul_of_nonneg_left (hmass n hn) (mul_nonneg hCE hrad)
        _ = (CE * eta) * radicalMajorant ((M : ℝ)^rho) n := by ring
    have hcomp : ‖blockInput M (m - n)‖ +
        ‖supportedAdjustedModel M (m - n) ((M : ℝ)^rho) b G e‖ ≤
          Λ (m - n) + CB * radicalMajorant ((M : ℝ)^rho) (m - n) :=
      add_le_add (blockInput_norm_le_vonMangoldt M (m - n))
        (hmodel ((M : ℝ)^rho) hs.2 M (m - n) b hb e)
    exact mul_le_mul herr hcomp (by positivity) (by positivity)
  calc
    _ ≤ ∑ n ∈ Finset.Ioc (M / 2) M,
        (CE * eta) * radicalMajorant ((M : ℝ)^rho) n *
          (Λ (m - n) + CB * radicalMajorant ((M : ℝ)^rho) (m - n)) :=
      Finset.sum_le_sum (fun n hn => hpoint n hn)
    _ = CE * eta *
        ((∑ n ∈ Finset.Ioc (M / 2) M,
            radicalMajorant ((M : ℝ)^rho) n * Λ (m - n)) +
          CB * (∑ n ∈ Finset.Ioc (M / 2) M,
            radicalMajorant ((M : ℝ)^rho) n *
              radicalMajorant ((M : ℝ)^rho) (m - n))) := by
      simp only [mul_add,Finset.sum_add_distrib,Finset.mul_sum]
      apply congrArg₂ (· + ·)
      · apply Finset.sum_congr rfl
        intro n hn
        ring
      · apply Finset.sum_congr rfl
        intro n hn
        ring
    _ ≤ CE * eta *
        (((128 * CH * (mertensProductConstant D c)^2 *
              (oneFrequencyConstant D c)^2 *
              (∫ ξ : ℝ, secondMomentDecay ξ)^2 / tenthDecayMass) *
            (M : ℝ) * arithmeticFactor m / rho^3) +
          CB * (128 * CH * (mertensProductConstant D c)^2 *
              (oneFrequencyConstant D c)^2 *
              (∫ ξ : ℝ, secondMomentDecay ξ)^2 * (M : ℝ) *
            arithmeticFactor m / rho^2)) := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg hCE heta)
      exact add_le_add hLambda (mul_le_mul_of_nonneg_left hHH hCB)
    _ = CE * eta *
        ((128 * CH * (mertensProductConstant D c)^2 *
            (oneFrequencyConstant D c)^2 *
            (∫ ξ : ℝ, secondMomentDecay ξ)^2 / tenthDecayMass) *
          (M : ℝ) * arithmeticFactor m / rho^3 +
         CB * (128 * CH * (mertensProductConstant D c)^2 *
            (oneFrequencyConstant D c)^2 *
            (∫ ξ : ℝ, secondMomentDecay ξ)^2) *
          (M : ℝ) * arithmeticFactor m / rho^2) := by ring

end GoldbachCircleMethodSupportedModelErrorConvolutionV18182
