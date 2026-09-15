import GoldbachCircleMethodBumpFourierRepresentationV18143

set_option autoImplicit false
open scoped BigOperators Classical ContDiff
open MeasureTheory
open GoldbachCircleMethodCompanionAbsoluteConvergenceV18141
open GoldbachCircleMethodCompanionIntegralInterchangeV18142
open GoldbachCircleMethodBumpFourierRepresentationV18143
open GoldbachCircleMethodLogCutoffPresieveBindingV18120
open GoldbachCircleMethodFullSquarefreeCarrierV1846
open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodFiniteCompanionBindingV18118
open GoldbachCircleMethodCompanionDivisorReindexV18140

namespace GoldbachCircleMethodLogWeightMellinBindingV18144

/-- The logarithmic argument of the pre-existing weight, not a new
cutoff or a changed complex-power convention. Positive n is essential. -/
theorem reciprocal_power_log_phase (R : ℝ) {n : ℕ} (hn : 0 < n) (ξ : ℝ) :
    1/((n : ℂ)^radicalExponent R ξ) =
      (Real.exp (-(Real.log (n : ℝ)/Real.log R)) : ℂ) *
        Complex.exp (-Complex.I*(ξ : ℂ)*
          ((Real.log (n : ℝ)/Real.log R : ℝ) : ℂ)) := by
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [Complex.cpow_def_of_ne_zero hnC,one_div,← Complex.exp_neg,
    ← Complex.natCast_log,Complex.ofReal_exp,← Complex.exp_add]
  congr 1
  unfold radicalExponent
  push_cast
  ring

/-- Pointwise Mellin-line representation of the exact V120 logWeight.
No singular n=0 term and no artificial replacement of G are admitted. -/
theorem logWeight_mellin_representation {G : ℝ → ℝ}
    (hc : HasCompactSupport G) (hd : ContDiff ℝ ∞ G)
    (R : ℝ) {n : ℕ} (hn : 0 < n) :
    logWeight R G n =
      ∫ ξ : ℝ, bumpFourierWeight G ξ/((n : ℂ)^radicalExponent R ξ) := by
  let t : ℝ := Real.log (n : ℝ)/Real.log R
  have he (ξ : ℝ) :
      bumpFourierWeight G ξ/((n : ℂ)^radicalExponent R ξ) =
      (Real.exp (-t) : ℂ) * (bumpFourierWeight G ξ *
        Complex.exp (-Complex.I*(ξ : ℂ)*(t : ℂ))) := by
    rw [div_eq_mul_one_div,reciprocal_power_log_phase R hn ξ]
    dsimp [t]
    ring
  simp_rw [he]
  rw [integral_const_mul,bumpFourierWeight_inversion hc hd]
  dsimp [weightedBump,logWeight,t]
  rw [← mul_assoc,← Complex.ofReal_mul,← Real.exp_add]
  simp

/-- Actual compactly supported complementary summand. -/
noncomputable def smoothedComplementTerm (k m : ℕ) (R : ℝ)
    (G : ℝ → ℝ) (n : ℕ) : ℂ :=
  if Squarefree n ∧ Nat.Coprime k n then
    logWeight R G (m*n)/(n.totient : ℂ) else 0

theorem complementary_mellin_integral {G : ℝ → ℝ}
    (hc : HasCompactSupport G) (hd : ContDiff ℝ ∞ G)
    (R : ℝ) (k : ℕ) {m : ℕ} (hm : 0 < m) (n : ℕ) :
    (∫ ξ : ℝ, (bumpFourierWeight G ξ/((m : ℂ)^radicalExponent R ξ)) *
      complementaryDirichletTerm k (radicalExponent R ξ) n) =
      smoothedComplementTerm k m R G n := by
  by_cases hn : Squarefree n ∧ Nat.Coprime k n
  · have hnpos : 0 < n := hn.1.ne_zero.bot_lt
    simp_rw [complementaryDirichletTerm,if_pos hn]
    have he (ξ : ℝ) :
        (bumpFourierWeight G ξ/((m : ℂ)^radicalExponent R ξ)) *
          (1/((n.totient : ℂ)*(n : ℂ)^radicalExponent R ξ)) =
        (1/(n.totient : ℂ)) *
          (bumpFourierWeight G ξ/((m*n : ℕ) : ℂ)^radicalExponent R ξ) := by
      rw [Nat.cast_mul,Complex.natCast_mul_natCast_cpow]
      ring
    simp_rw [he]
    rw [integral_const_mul,← logWeight_mellin_representation hc hd R (mul_pos hm hnpos)]
    simp only [smoothedComplementTerm,if_pos hn]
    ring
  · simp only [complementaryDirichletTerm,smoothedComplementTerm,if_neg hn,
      mul_zero,integral_zero]

/-- Genuine HasSum after discharging each Mellin integral. -/
theorem smoothedComplement_hasSum_integral {G : ℝ → ℝ}
    (hc : HasCompactSupport G) (hd : ContDiff ℝ ∞ G)
    {R : ℝ} (hR : 1 < R) (k : ℕ) {m : ℕ} (hm : 0 < m) :
    HasSum (smoothedComplementTerm k m R G)
      (∫ ξ : ℝ, (bumpFourierWeight G ξ/((m : ℂ)^radicalExponent R ξ)) *
        (∑' n, complementaryDirichletTerm k (radicalExponent R ξ) n)) := by
  have hs := actual_bump_prefactored_interchange hc hd hR k hm
  simpa only [complementary_mellin_integral hc hd R k hm] using hs

theorem smoothedComplement_zero_above_cutoff {G : ℝ → ℝ}
    (hG : ∀ t : ℝ, 2 < t → G t = 0) {R : ℝ} (hR : 1 < R)
    (k : ℕ) {m : ℕ} (hm : 0 < m) {n : ℕ} (hn : ⌊R^2⌋₊/m < n) :
    smoothedComplementTerm k m R G n = 0 := by
  by_cases hp : Squarefree n ∧ Nat.Coprime k n
  · have hmn : ⌊R^2⌋₊ < m*n := by
      simpa only [Nat.mul_comm] using (Nat.div_lt_iff_lt_mul hm).mp hn
    rw [smoothedComplementTerm,if_pos hp,
      logWeight_zero_above_cutoff R hR G hG (m*n)
        (mul_pos hm hp.1.ne_zero.bot_lt) hmn,zero_div]
  · simp only [smoothedComplementTerm,if_neg hp]

/-- Exact finite cutoff-to-integral bridge. The finite carrier and
coprimality condition match V140, with no rectangular relaxation. -/
theorem finite_complement_mellin_integral {G : ℝ → ℝ}
    (hc : HasCompactSupport G) (hd : ContDiff ℝ ∞ G)
    (hG : ∀ t : ℝ, 2 < t → G t = 0) {R : ℝ} (hR : 1 < R)
    (k : ℕ) {m : ℕ} (hm : 0 < m) :
    (∑ n ∈ (fullSquarefreePrefix (⌊R^2⌋₊/m)).filter (fun n => Nat.Coprime k n),
      logWeight R G (m*n)/(n.totient : ℂ)) =
      ∫ ξ : ℝ, (bumpFourierWeight G ξ/((m : ℂ)^radicalExponent R ξ)) *
        (∑' n, complementaryDirichletTerm k (radicalExponent R ξ) n) := by
  let S := (fullSquarefreePrefix (⌊R^2⌋₊/m)).filter (fun n => Nat.Coprime k n)
  have hfinite : HasSum (smoothedComplementTerm k m R G)
      (∑ n ∈ S, smoothedComplementTerm k m R G n) := by
    apply hasSum_sum_of_ne_finset_zero
    intro n hn
    by_cases hp : Squarefree n ∧ Nat.Coprime k n
    · have hcut : ⌊R^2⌋₊/m < n := by
        by_contra h
        exact hn (Finset.mem_filter.mpr
          ⟨mem_fullSquarefreePrefix.mpr ⟨Nat.le_of_not_gt h,hp.1⟩,hp.2⟩)
      exact smoothedComplement_zero_above_cutoff hG hR k hm hcut
    · simp only [smoothedComplementTerm,if_neg hp]
  have he : (∑ n ∈ S, smoothedComplementTerm k m R G n) =
      ∑ n ∈ S, logWeight R G (m*n)/(n.totient : ℂ) := by
    apply Finset.sum_congr rfl
    intro n hn
    have hp := Finset.mem_filter.mp hn
    simp only [smoothedComplementTerm,
      if_pos (show Squarefree n ∧ Nat.Coprime k n from
        ⟨(mem_fullSquarefreePrefix.mp hp.1).2,hp.2⟩)]
  rw [← he]
  exact hfinite.unique (smoothedComplement_hasSum_integral hc hd hR k hm)

/-- The actual finite companion from V118, with V120's precise log
weight and V140's coupled divisor carrier, represented by justified
complementary-series integrals. -/
theorem actual_finite_companion_mellin {G : ℝ → ℝ}
    (hc : HasCompactSupport G) (hd : ContDiff ℝ ∞ G)
    (hG : ∀ t : ℝ, 2 < t → G t = 0) {R : ℝ} (hR : 1 < R)
    (r : PositiveLevel ⌊R^2⌋₊) (N : ℕ) :
    finiteCompanion r N (logWeight R G) =
      ∑ d ∈ (fullSquarefreePrefix (⌊R^2⌋₊/r.val)).filter
          (fun d => d ∣ N ∧ Nat.Coprime r.val d),
        (((ArithmeticFunction.moebius d : ℤ) : ℂ)*(d : ℂ)/(d.totient : ℂ)) *
          ∫ ξ : ℝ, (bumpFourierWeight G ξ/
              (((r.val*d : ℕ) : ℂ)^radicalExponent R ξ)) *
            (∑' n, complementaryDirichletTerm (r.val*d) (radicalExponent R ξ) n) := by
  rw [finite_companion_factored_divisor_sum]
  apply Finset.sum_congr rfl
  intro d hdmem
  have hdpos : 0 < d :=
    (mem_fullSquarefreePrefix.mp (Finset.mem_filter.mp hdmem).1).2.ne_zero.bot_lt
  have hrpos : 0 < r.val := (Finset.mem_Icc.mp r.property).1
  rw [finite_complement_mellin_integral hc hd hG hR (r.val*d) (mul_pos hrpos hdpos)]

end GoldbachCircleMethodLogWeightMellinBindingV18144
