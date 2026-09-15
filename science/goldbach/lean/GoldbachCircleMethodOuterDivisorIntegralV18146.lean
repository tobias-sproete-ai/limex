import GoldbachCircleMethodComplementaryEulerProductV18145
import Mathlib.Analysis.Normed.Group.FunctionSeries

set_option autoImplicit false
open scoped BigOperators Classical ContDiff
open MeasureTheory
open GoldbachCircleMethodCompanionAbsoluteConvergenceV18141
open GoldbachCircleMethodCompanionIntegralInterchangeV18142
open GoldbachCircleMethodBumpFourierRepresentationV18143
open GoldbachCircleMethodLogWeightMellinBindingV18144
open GoldbachCircleMethodLogCutoffPresieveBindingV18120
open GoldbachCircleMethodFullSquarefreeCarrierV1846
open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodFiniteCompanionBindingV18118

namespace GoldbachCircleMethodOuterDivisorIntegralV18146

theorem continuous_complementary_vertical_sum {R : ℝ} (hR : 1 < R) (k : ℕ) :
    Continuous (fun ξ : ℝ => ∑' n, complementaryDirichletTerm k (radicalExponent R ξ) n) :=
  continuous_tsum (continuous_complementary_vertical_term R k)
    (summable_divisorMajorant (one_div_pos.mpr (Real.log_pos hR)))
    (fun n ξ => (radical_line_absolute_domination hR k ξ).2.1 n)

noncomputable def companionIntegrand (G : ℝ → ℝ) (R : ℝ) (m : ℕ) (ξ : ℝ) : ℂ :=
  (bumpFourierWeight G ξ/((m : ℂ)^radicalExponent R ξ)) *
    (∑' n, complementaryDirichletTerm m (radicalExponent R ξ) n)

theorem companionIntegrand_integrable {G : ℝ → ℝ}
    (hc : HasCompactSupport G) (hd : ContDiff ℝ ∞ G)
    {R : ℝ} (hR : 1 < R) {m : ℕ} (hm : 0 < m) :
    Integrable (companionIntegrand G R m) := by
  have hw := integrable_weighted_vertical_power hR hm _
    (bumpFourierWeight_integrable hc hd)
  have hf := continuous_complementary_vertical_sum hR m
  apply (hw.norm.mul_const (∑' n, divisorMajorant (1/Real.log R) n)).mono'
  · exact hw.aestronglyMeasurable.mul hf.aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun ξ => by
    dsimp [companionIntegrand]
    rw [norm_mul]
    have hb := complementaryDirichletSeries_norm_le m (radicalExponent_re_pos hR ξ)
    rw [radicalExponent_re] at hb
    exact mul_le_mul_of_nonneg_left hb (norm_nonneg _))

/-- Added outer-divisor terms vanish by G's exact cutoff AFTER
integration. Their Dirichlet-series integrands need not vanish. -/
theorem companion_integral_zero_above_cutoff {G : ℝ → ℝ}
    (hc : HasCompactSupport G) (hd : ContDiff ℝ ∞ G)
    (hG : ∀ t : ℝ, 2 < t → G t = 0) {R : ℝ} (hR : 1 < R)
    {m : ℕ} (hm : ⌊R^2⌋₊ < m) :
    (∫ ξ : ℝ, companionIntegrand G R m ξ) = 0 := by
  have hmpos : 0 < m := Nat.zero_le _ |>.trans_lt hm
  unfold companionIntegrand
  rw [← finite_complement_mellin_integral hc hd hG hR m hmpos]
  have hdiv : ⌊R^2⌋₊/m = 0 := Nat.div_eq_of_lt hm
  have hempty : fullSquarefreePrefix 0 = ∅ := by
    ext n
    simp only [mem_fullSquarefreePrefix,Finset.notMem_empty,iff_false]
    rintro ⟨hn,hs⟩
    exact hs.ne_zero (Nat.eq_zero_of_le_zero hn)
  rw [hdiv,hempty,Finset.filter_empty,Finset.sum_empty]

def fullDivisorCarrier (r N : ℕ) : Finset ℕ :=
  N.divisors.filter (fun d => Squarefree d ∧ Nat.Coprime r d)

/-- Exact extension to all squarefree divisors of positive N.
Extra terms are zero integrals, not pointwise zero integrands. -/
theorem actual_companion_full_divisor_integrals {G : ℝ → ℝ}
    (hc : HasCompactSupport G) (hd : ContDiff ℝ ∞ G)
    (hG : ∀ t : ℝ, 2 < t → G t = 0) {R : ℝ} (hR : 1 < R)
    (r : PositiveLevel ⌊R^2⌋₊) {N : ℕ} (hN : 0 < N) :
    finiteCompanion r N (logWeight R G) =
      ∑ d ∈ fullDivisorCarrier r.val N,
        (((ArithmeticFunction.moebius d : ℤ) : ℂ)*(d : ℂ)/(d.totient : ℂ)) *
          ∫ ξ : ℝ, companionIntegrand G R (r.val*d) ξ := by
  rw [actual_finite_companion_mellin hc hd hG hR r N]
  apply Finset.sum_subset
  · intro d hdmem
    have hh := Finset.mem_filter.mp hdmem
    exact Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨hh.2.1,hN.ne'⟩,
      (mem_fullSquarefreePrefix.mp hh.1).2,hh.2.2⟩
  · intro d hdmem hnot
    have hh := Finset.mem_filter.mp hdmem
    have hrpos : 0 < r.val := (Finset.mem_Icc.mp r.property).1
    have hcut : ⌊R^2⌋₊/r.val < d := by
      by_contra h
      exact hnot (Finset.mem_filter.mpr
        ⟨mem_fullSquarefreePrefix.mpr ⟨Nat.le_of_not_gt h,hh.2.1⟩,
          Nat.dvd_of_mem_divisors hh.1,hh.2.2⟩)
    have hprod : ⌊R^2⌋₊ < r.val*d := by
      simpa only [Nat.mul_comm] using (Nat.div_lt_iff_lt_mul hrpos).mp hcut
    change (((ArithmeticFunction.moebius d : ℤ) : ℂ)*(d : ℂ)/(d.totient : ℂ)) *
      (∫ ξ : ℝ, companionIntegrand G R (r.val*d) ξ) = 0
    rw [companion_integral_zero_above_cutoff hc hd hG hR hprod,mul_zero]

/-- Finite outer sum is moved under the integral only after actual
integrability of every term has been proved. -/
theorem actual_companion_full_divisor_integral {G : ℝ → ℝ}
    (hc : HasCompactSupport G) (hd : ContDiff ℝ ∞ G)
    (hG : ∀ t : ℝ, 2 < t → G t = 0) {R : ℝ} (hR : 1 < R)
    (r : PositiveLevel ⌊R^2⌋₊) {N : ℕ} (hN : 0 < N) :
    finiteCompanion r N (logWeight R G) =
      ∫ ξ : ℝ, ∑ d ∈ fullDivisorCarrier r.val N,
        (((ArithmeticFunction.moebius d : ℤ) : ℂ)*(d : ℂ)/(d.totient : ℂ)) *
          companionIntegrand G R (r.val*d) ξ := by
  rw [actual_companion_full_divisor_integrals hc hd hG hR r hN]
  have hi (d : ℕ) (hdmem : d ∈ fullDivisorCarrier r.val N) :
      Integrable (fun ξ : ℝ =>
        (((ArithmeticFunction.moebius d : ℤ) : ℂ)*(d : ℂ)/(d.totient : ℂ)) *
          companionIntegrand G R (r.val*d) ξ) := by
    have hrpos : 0 < r.val := (Finset.mem_Icc.mp r.property).1
    have hdpos : 0 < d :=
      (Finset.mem_filter.mp hdmem).2.1.ne_zero.bot_lt
    exact (companionIntegrand_integrable hc hd hR (mul_pos hrpos hdpos)).const_mul _
  rw [integral_finsetSum _ hi]
  apply Finset.sum_congr rfl
  intro d _
  rw [integral_const_mul]

/-- Fixed outer-divisor bracket. This is computed from the actual
coefficient series, not an assumed analytic factorization. -/
noncomputable def fullDivisorBracket (r N : ℕ) (s : ℂ) : ℂ :=
  ∑ d ∈ fullDivisorCarrier r N,
    (((ArithmeticFunction.moebius d : ℤ) : ℂ)*(d : ℂ)/
      ((d.totient : ℂ)*(d : ℂ)^s)) *
      (∑' n, complementaryDirichletTerm (r*d) s n)

theorem actual_companion_factored_integral {G : ℝ → ℝ}
    (hc : HasCompactSupport G) (hd : ContDiff ℝ ∞ G)
    (hG : ∀ t : ℝ, 2 < t → G t = 0) {R : ℝ} (hR : 1 < R)
    (r : PositiveLevel ⌊R^2⌋₊) {N : ℕ} (hN : 0 < N) :
    finiteCompanion r N (logWeight R G) =
      ∫ ξ : ℝ, (bumpFourierWeight G ξ/((r.val : ℂ)^radicalExponent R ξ)) *
        fullDivisorBracket r.val N (radicalExponent R ξ) := by
  rw [actual_companion_full_divisor_integral hc hd hG hR r hN]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun ξ => by
    dsimp only
    unfold fullDivisorBracket
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d _
    unfold companionIntegrand
    rw [Nat.cast_mul,Complex.natCast_mul_natCast_cpow]
    ring)

end GoldbachCircleMethodOuterDivisorIntegralV18146
