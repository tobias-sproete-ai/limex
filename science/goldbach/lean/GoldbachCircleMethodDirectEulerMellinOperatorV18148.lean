import GoldbachCircleMethodFullRamanujanDirichletV18147

set_option autoImplicit false
open scoped BigOperators Classical ContDiff
open MeasureTheory
open GoldbachCircleMethodFiniteResiduePrefixV1866
open GoldbachCircleMethodCompanionAbsoluteConvergenceV18141
open GoldbachCircleMethodCompanionIntegralInterchangeV18142
open GoldbachCircleMethodBumpFourierRepresentationV18143
open GoldbachCircleMethodLogWeightMellinBindingV18144
open GoldbachCircleMethodLogCutoffPresieveBindingV18120
open GoldbachCircleMethodFullRamanujanDirichletV18147
open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodFiniteCompanionBindingV18118

namespace GoldbachCircleMethodDirectEulerMellinOperatorV18148

theorem full_term_power_factor (r N : ℕ) (s : ℂ) (q : ℕ) :
    fullRamanujanDirichletTerm r N s q =
      fullRamanujanDirichletTerm r N 0 q/((q : ℂ)^s) := by
  by_cases hq : q = 0
  · subst q
    simp only [full_term_zero,zero_div]
  · simp only [fullRamanujanDirichletTerm,dif_neg hq,Complex.cpow_zero,div_one]
    split_ifs <;> simp only [zero_div]

theorem continuous_full_vertical_term (R : ℝ) (r N q : ℕ) :
    Continuous (fun ξ : ℝ => fullRamanujanDirichletTerm r N (radicalExponent R ξ) q) := by
  by_cases hq : q = 0
  · subst q
    simp only [full_term_zero]
    exact continuous_const
  · have he : (fun ξ : ℝ => fullRamanujanDirichletTerm r N (radicalExponent R ξ) q) =
        (fun ξ : ℝ => fullRamanujanDirichletTerm r N 0 q / ((q : ℂ)^radicalExponent R ξ)) :=
      funext (fun ξ => full_term_power_factor r N (radicalExponent R ξ) q)
    rw [he]
    have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hq
    exact continuous_const.div
      ((continuous_radicalExponent R).const_cpow (Or.inl hqC))
      (fun _ => Complex.cpow_ne_zero_iff.mpr (Or.inl hqC))

theorem full_vertical_norm_bound {R : ℝ} (r : ℕ)
    {N : ℕ} (hN : 0 < N) (q : ℕ) (ξ : ℝ) :
    ‖fullRamanujanDirichletTerm r N (radicalExponent R ξ) q‖ ≤
      divisorMass N*divisorMajorant (1/Real.log R) q := by
  simpa only [radicalExponent_re] using full_term_norm_le r hN (radicalExponent R ξ) q

theorem full_vertical_weighted_hasSum_integral {R : ℝ} (hR : 1 < R)
    (r : ℕ) {N : ℕ} (hN : 0 < N) (ψ : ℝ → ℂ) (hψ : Integrable ψ) :
    HasSum (fun q : ℕ => ∫ ξ : ℝ, ψ ξ *
        fullRamanujanDirichletTerm r N (radicalExponent R ξ) q)
      (∫ ξ : ℝ, ψ ξ*(∑' q, fullRamanujanDirichletTerm r N (radicalExponent R ξ) q)) := by
  let D : ℕ → ℝ := fun q => divisorMass N*divisorMajorant (1/Real.log R) q
  have hD : Summable D :=
    (summable_divisorMajorant (one_div_pos.mpr (Real.log_pos hR))).mul_left (divisorMass N)
  apply hasSum_integral_of_dominated_convergence (fun q ξ => ‖ψ ξ‖*D q)
  · intro q
    exact hψ.aestronglyMeasurable.mul (continuous_full_vertical_term R r N q).aestronglyMeasurable
  · intro q
    exact Filter.Eventually.of_forall (fun ξ => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (full_vertical_norm_bound r hN q ξ) (norm_nonneg _))
  · exact Filter.Eventually.of_forall (fun ξ => hD.mul_left ‖ψ ξ‖)
  · have he : (fun ξ => ∑' q, ‖ψ ξ‖*D q) =
        (fun ξ => ‖ψ ξ‖*(∑' q,D q)) := funext (fun ξ => hD.tsum_mul_left _)
    rw [he]
    exact hψ.norm.mul_const _
  · exact Filter.Eventually.of_forall (fun ξ =>
      (full_term_norm_summable r hN (radicalExponent_re_pos hR ξ)).of_norm.hasSum.mul_left (ψ ξ))

noncomputable def fullSmoothedTerm (r N : ℕ) (R : ℝ) (G : ℝ → ℝ) (q : ℕ) : ℂ :=
  fullRamanujanDirichletTerm r N 0 q*logWeight R G (r*q)

theorem full_smoothed_zero (r N : ℕ) (R : ℝ) (G : ℝ → ℝ) :
    fullSmoothedTerm r N R G 0 = 0 := by
  simp only [fullSmoothedTerm,full_term_zero,zero_mul]

theorem full_term_mellin_integral {G : ℝ → ℝ}
    (hc : HasCompactSupport G) (hd : ContDiff ℝ ∞ G)
    (R : ℝ) {r : ℕ} (hr : 0 < r) (N q : ℕ) :
    (∫ ξ : ℝ, (bumpFourierWeight G ξ/((r : ℂ)^radicalExponent R ξ)) *
      fullRamanujanDirichletTerm r N (radicalExponent R ξ) q) =
      fullSmoothedTerm r N R G q := by
  by_cases hq : q = 0
  · subst q
    simp only [full_term_zero,mul_zero,integral_zero,full_smoothed_zero]
  · have hqpos : 0 < q := Nat.pos_of_ne_zero hq
    have he (ξ : ℝ) :
        (bumpFourierWeight G ξ/((r : ℂ)^radicalExponent R ξ)) *
          fullRamanujanDirichletTerm r N (radicalExponent R ξ) q =
        fullRamanujanDirichletTerm r N 0 q *
          (bumpFourierWeight G ξ/(((r*q : ℕ) : ℂ)^radicalExponent R ξ)) := by
      rw [full_term_power_factor,Nat.cast_mul,Complex.natCast_mul_natCast_cpow]
      ring
    simp_rw [he]
    rw [integral_const_mul,← logWeight_mellin_representation hc hd R (mul_pos hr hqpos)]
    rfl

theorem full_smoothed_hasSum_integral {G : ℝ → ℝ}
    (hc : HasCompactSupport G) (hd : ContDiff ℝ ∞ G)
    {R : ℝ} (hR : 1 < R) {r : ℕ} (hr : 0 < r) {N : ℕ} (hN : 0 < N) :
    HasSum (fullSmoothedTerm r N R G)
      (∫ ξ : ℝ, (bumpFourierWeight G ξ/((r : ℂ)^radicalExponent R ξ)) *
        (∑' q, fullRamanujanDirichletTerm r N (radicalExponent R ξ) q)) := by
  have hs := full_vertical_weighted_hasSum_integral hR r hN _
    (integrable_weighted_vertical_power hR hr _ (bumpFourierWeight_integrable hc hd))
  simpa only [full_term_mellin_integral hc hd R hr N] using hs

/-- Actual cutoff, not a limiting tail estimate. -/
theorem full_smoothed_zero_above_product_cutoff {G : ℝ → ℝ}
    (hG : ∀ t : ℝ, 2 < t → G t = 0) {R : ℝ} (hR : 1 < R)
    (r N q : ℕ) (hcut : ⌊R^2⌋₊ < r*q) :
    fullSmoothedTerm r N R G q = 0 := by
  unfold fullSmoothedTerm
  rw [logWeight_zero_above_cutoff R hR G hG (r*q)
    (lt_of_le_of_lt (Nat.zero_le _) hcut) hcut, mul_zero]

theorem full_smoothed_finite_hasSum {G : ℝ → ℝ}
    (hG : ∀ t : ℝ, 2 < t → G t = 0) {R : ℝ} (hR : 1 < R)
    {r : ℕ} (hr : 0 < r) (N : ℕ) :
    HasSum (fullSmoothedTerm r N R G)
      (∑ q ∈ Finset.Icc 1 ⌊R^2⌋₊, fullSmoothedTerm r N R G q) := by
  apply hasSum_sum_of_ne_finset_zero
  intro q hq
  by_cases hq0 : q = 0
  · subst q
    exact full_smoothed_zero r N R G
  · have hcut : ⌊R^2⌋₊ < q := by
      by_contra h
      exact hq (Finset.mem_Icc.mpr ⟨Nat.pos_of_ne_zero hq0, Nat.le_of_not_gt h⟩)
    exact full_smoothed_zero_above_product_cutoff hG hR r N q
      (hcut.trans_le (Nat.le_mul_of_pos_left q hr))

/-- Same V118 operator and same r*q cutoff; no newly defined surrogate. -/
theorem actual_companion_eq_full_smoothed {G : ℝ → ℝ}
    (hG : ∀ t : ℝ, 2 < t → G t = 0) {R : ℝ} (hR : 1 < R)
    (r : PositiveLevel ⌊R^2⌋₊) (N : ℕ) :
    finiteCompanion r N (logWeight R G) =
      ∑ q ∈ Finset.Icc 1 ⌊R^2⌋₊, fullSmoothedTerm r.val N R G q := by
  unfold finiteCompanion
  rw [Finset.sum_subtype (Finset.Icc 1 ⌊R^2⌋₊) (by intro q; rfl)
    (fullSmoothedTerm r.val N R G)]
  apply Finset.sum_congr rfl
  intro q _
  by_cases hcut : r.val*q.val ≤ ⌊R^2⌋₊
  · unfold fullSmoothedTerm
    rw [full_term_original_coefficient]
    simp only [Complex.cpow_zero,div_one,hcut,true_and]
    split_ifs <;> simp only [zero_mul]
  · rw [if_neg (fun h => hcut h.1),
      full_smoothed_zero_above_product_cutoff hG hR r.val N q.val (Nat.lt_of_not_ge hcut)]

theorem actual_companion_direct_mellin {G : ℝ → ℝ}
    (hc : HasCompactSupport G) (hd : ContDiff ℝ ∞ G)
    (hG : ∀ t : ℝ, 2 < t → G t = 0) {R : ℝ} (hR : 1 < R)
    (r : PositiveLevel ⌊R^2⌋₊) {N : ℕ} (hN : 0 < N) :
    finiteCompanion r N (logWeight R G) =
      ∫ ξ : ℝ, (bumpFourierWeight G ξ/((r.val : ℂ)^radicalExponent R ξ)) *
        (∑' q, fullRamanujanDirichletTerm r.val N (radicalExponent R ξ) q) := by
  rw [actual_companion_eq_full_smoothed hG hR]
  exact (full_smoothed_finite_hasSum hG hR (Finset.mem_Icc.mp r.property).1 N).unique
    (full_smoothed_hasSum_integral hc hd hR (Finset.mem_Icc.mp r.property).1 hN)

/-- The original finite companion equals the convergent three-branch Euler
integral. Prime divisors of N and the conductor exclusion remain explicit. -/
theorem actual_companion_direct_euler_mellin {G : ℝ → ℝ}
    (hc : HasCompactSupport G) (hd : ContDiff ℝ ∞ G)
    (hG : ∀ t : ℝ, 2 < t → G t = 0) {R : ℝ} (hR : 1 < R)
    (r : PositiveLevel ⌊R^2⌋₊) {N : ℕ} (hN : 0 < N) :
    finiteCompanion r N (logWeight R G) =
      ∫ ξ : ℝ, (bumpFourierWeight G ξ/((r.val : ℂ)^radicalExponent R ξ)) *
        (∏' p : Nat.Primes,
          fullRamanujanLocalFactor r.val N (radicalExponent R ξ) p.val) := by
  rw [actual_companion_direct_mellin hc hd hG hR r hN]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun ξ => by
    exact congrArg (fun z : ℂ =>
      (bumpFourierWeight G ξ/((r.val : ℂ)^radicalExponent R ξ))*z)
      (full_ramanujan_euler_hasProd r.val hN (radicalExponent_re_pos hR ξ)).tprod_eq.symm)

theorem continuous_full_vertical_sum {R : ℝ} (hR : 1 < R)
    (r : ℕ) {N : ℕ} (hN : 0 < N) :
    Continuous (fun ξ : ℝ => ∑' q, fullRamanujanDirichletTerm r N (radicalExponent R ξ) q) :=
  continuous_tsum (continuous_full_vertical_term R r N)
    ((summable_divisorMajorant (one_div_pos.mpr (Real.log_pos hR))).mul_left (divisorMass N))
    (fun q ξ => full_vertical_norm_bound r hN q ξ)

/-- Explicit integrability rules out relying on a totalized undefined integral. -/
theorem actual_full_euler_integrand_integrable {G : ℝ → ℝ}
    (hc : HasCompactSupport G) (hd : ContDiff ℝ ∞ G)
    {R : ℝ} (hR : 1 < R) {r : ℕ} (hr : 0 < r) {N : ℕ} (hN : 0 < N) :
    Integrable (fun ξ : ℝ => (bumpFourierWeight G ξ/((r : ℂ)^radicalExponent R ξ)) *
      (∏' p : Nat.Primes, fullRamanujanLocalFactor r N (radicalExponent R ξ) p.val)) := by
  have hw := integrable_weighted_vertical_power hR hr _ (bumpFourierWeight_integrable hc hd)
  let D : ℕ → ℝ := fun q => divisorMass N*divisorMajorant (1/Real.log R) q
  have hD : Summable D :=
    (summable_divisorMajorant (one_div_pos.mpr (Real.log_pos hR))).mul_left (divisorMass N)
  have hi : Integrable (fun ξ : ℝ =>
      (bumpFourierWeight G ξ/((r : ℂ)^radicalExponent R ξ)) *
        (∑' q, fullRamanujanDirichletTerm r N (radicalExponent R ξ) q)) := by
    apply (hw.norm.mul_const (∑' q,D q)).mono'
    · exact hw.aestronglyMeasurable.mul
        (continuous_full_vertical_sum hR r hN).aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun ξ => by
      rw [norm_mul]
      have hs := full_term_norm_summable r hN (radicalExponent_re_pos hR ξ)
      have hb := (norm_tsum_le_tsum_norm hs).trans
        (hs.tsum_le_tsum (fun q => full_vertical_norm_bound r hN q ξ) hD)
      exact mul_le_mul_of_nonneg_left hb (norm_nonneg _))
  apply hi.congr
  exact Filter.Eventually.of_forall (fun ξ =>
    congrArg (fun z : ℂ => (bumpFourierWeight G ξ/((r : ℂ)^radicalExponent R ξ))*z)
      (full_ramanujan_euler_hasProd r hN (radicalExponent_re_pos hR ξ)).tprod_eq.symm)

end GoldbachCircleMethodDirectEulerMellinOperatorV18148
