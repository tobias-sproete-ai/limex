import GoldbachCircleMethodFullEulerRadicalAssemblyV18153

set_option autoImplicit false
open scoped BigOperators Classical ContDiff
open MeasureTheory
open GoldbachCircleMethodCompanionAbsoluteConvergenceV18141
open GoldbachCircleMethodBumpFourierRepresentationV18143
open GoldbachCircleMethodLogCutoffPresieveBindingV18120
open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodFiniteCompanionBindingV18118
open GoldbachCircleMethodFullRamanujanDirichletV18147
open GoldbachCircleMethodDirectEulerMellinOperatorV18148
open GoldbachCircleMethodLocalEulerRadicalBoundsV18149
open GoldbachCircleMethodConductorProductCompensationV18152
open GoldbachCircleMethodFullEulerRadicalAssemblyV18153
namespace GoldbachCircleMethodActualCompanionRadicalIntegralV18154

theorem radicalEnvelope_nonneg {R : ℝ} (hR : 1 < R) (ξ : ℝ) (N : ℕ) :
    0 ≤ radicalEnvelope R ξ N :=
  Finset.prod_nonneg (fun _ hp => radicalLocal_nonneg hR ξ (Nat.prime_of_mem_primeFactors hp))

theorem radicalEnvelope_le_one {R : ℝ} (hR : 1 < R) (ξ : ℝ) (N : ℕ) :
    radicalEnvelope R ξ N ≤ 1 := by
  apply Finset.prod_le_one
  · intro p hp
    exact radicalLocal_nonneg hR ξ (Nat.prime_of_mem_primeFactors hp)
  · intro p _
    exact min_le_left _ _

theorem continuous_radicalEnvelope (R : ℝ) (N : ℕ) :
    Continuous (fun ξ : ℝ => radicalEnvelope R ξ N) := by
  unfold radicalEnvelope radicalLocal
  fun_prop

theorem integrable_weighted_radical {R : ℝ} (hR : 1 < R) (N : ℕ)
    {ψ : ℝ → ℂ} (hψ : Integrable ψ) :
    Integrable (fun ξ => ‖ψ ξ‖*radicalEnvelope R ξ N) := by
  apply hψ.norm.mono'
  · exact hψ.norm.aestronglyMeasurable.mul (continuous_radicalEnvelope R N).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun ξ => by
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (norm_nonneg _) (radicalEnvelope_nonneg hR ξ N))]
    exact mul_le_of_le_one_right (norm_nonneg _) (radicalEnvelope_le_one hR ξ N))

theorem full_series_integrand_integrable {G : ℝ → ℝ}
    (hc : HasCompactSupport G) (hd : ContDiff ℝ ∞ G)
    {R : ℝ} (hR : 1 < R) {r N : ℕ} (hr : 0 < r) (hN : 0 < N) :
    Integrable (fun ξ : ℝ => (bumpFourierWeight G ξ/((r : ℂ)^radicalExponent R ξ)) *
      (∑' q, fullRamanujanDirichletTerm r N (radicalExponent R ξ) q)) := by
  apply (actual_full_euler_integrand_integrable hc hd hR hr hN).congr
  exact Filter.Eventually.of_forall (fun ξ =>
    congrArg (fun z : ℂ => (bumpFourierWeight G ξ/((r : ℂ)^radicalExponent R ξ))*z)
      (full_ramanujan_euler_hasProd r hN (radicalExponent_re_pos hR ξ)).tprod_eq)

theorem conductor_integrand_radical_bound {R : ℝ} (hR : 1 < R)
    (ξ : ℝ) (ψ : ℂ) {r N : ℕ} (hr : 0 < r) (hN : 0 < N) (hcop : r.Coprime N) :
    ((r : ℝ)/(r.totient : ℝ)) *
      ‖(ψ/((r : ℂ)^radicalExponent R ξ)) *
        (∑' q, fullRamanujanDirichletTerm r N (radicalExponent R ξ) q)‖ ≤
      ((Real.exp 1*(1+Real.log R))*(N.divisors.card : ℝ)) *
        (‖ψ‖*radicalEnvelope R ξ N) := by
  have hb := mul_le_mul_of_nonneg_left (conductor_compensated_radical_line_bound hR ξ hr hN hcop)
    (norm_nonneg ψ)
  rw [norm_mul,norm_div,Complex.norm_natCast_cpow_of_re_ne_zero r
    (radicalExponent_re_pos hR ξ).ne',radicalExponent_re]
  unfold conductorWeight at hb
  convert hb using 1 <;> first | rfl | ring

/-- Bound for the original finite companion, with the same logarithmic weight
and r*q cutoff. This is not a newly introduced surrogate. -/
theorem actual_companion_radical_integral_bound {G : ℝ → ℝ}
    (hc : HasCompactSupport G) (hd : ContDiff ℝ ∞ G)
    (hG : ∀ t : ℝ, 2 < t → G t = 0) {R : ℝ} (hR : 1 < R)
    (r : PositiveLevel ⌊R^2⌋₊) {N : ℕ} (hN : 0 < N)
    (hcop : r.val.Coprime N) :
    ((r.val : ℝ)/(r.val.totient : ℝ))*‖finiteCompanion r N (logWeight R G)‖ ≤
      ((Real.exp 1*(1+Real.log R))*(N.divisors.card : ℝ)) *
        (∫ ξ : ℝ, ‖bumpFourierWeight G ξ‖*radicalEnvelope R ξ N) := by
  have hr := (Finset.mem_Icc.mp r.property).1
  let F : ℝ → ℂ := fun ξ => (bumpFourierWeight G ξ/((r.val : ℂ)^radicalExponent R ξ)) *
    (∑' q, fullRamanujanDirichletTerm r.val N (radicalExponent R ξ) q)
  let K : ℝ := (Real.exp 1*(1+Real.log R))*(N.divisors.card : ℝ)
  let C : ℝ := (r.val : ℝ)/(r.val.totient : ℝ)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hi : Integrable F := full_series_integrand_integrable hc hd hR hr hN
  have he := actual_companion_direct_mellin hc hd hG hR r hN
  change finiteCompanion r N (logWeight R G) = ∫ ξ : ℝ, F ξ at he
  rw [he]
  change C*‖∫ ξ, F ξ‖ ≤ K*(∫ ξ : ℝ, ‖bumpFourierWeight G ξ‖*radicalEnvelope R ξ N)
  calc
    _ ≤ C*(∫ ξ, ‖F ξ‖) := mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm F) hC
    _ = ∫ ξ, C*‖F ξ‖ := (integral_const_mul C _).symm
    _ ≤ ∫ ξ : ℝ, K*(‖bumpFourierWeight G ξ‖*radicalEnvelope R ξ N) := by
      apply integral_mono (hi.norm.const_mul C)
        ((integrable_weighted_radical hR N (bumpFourierWeight_integrable hc hd)).const_mul K)
      intro ξ
      exact conductor_integrand_radical_bound hR ξ _ hr hN hcop
    _ = _ := integral_const_mul K _

end GoldbachCircleMethodActualCompanionRadicalIntegralV18154
