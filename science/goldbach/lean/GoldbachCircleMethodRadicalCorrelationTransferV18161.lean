import GoldbachCircleMethodRadicalConvolutionIntegralV18160

set_option autoImplicit false
open scoped BigOperators Classical
open MeasureTheory
open GoldbachCircleMethodBumpDecayRadicalEnvelopeV18155
open GoldbachCircleMethodRadicalArithmeticClassV18159
open GoldbachCircleMethodRadicalConvolutionIntegralV18160
namespace GoldbachCircleMethodRadicalCorrelationTransferV18161

noncomputable def secondMomentDecay (ξ : ℝ) : ℝ :=
  tenthDecay ξ * (1+|ξ|)^2

theorem secondMomentDecay_nonneg (ξ : ℝ) : 0 ≤ secondMomentDecay ξ :=
  mul_nonneg (tenthDecay_nonneg ξ) (sq_nonneg _)

theorem secondMomentDecay_integrable : Integrable secondMomentDecay := by
  have hi := integrable_one_add_norm (E := ℝ) (μ := (volume : Measure ℝ))
    (r := (8 : ℝ)) (by norm_num)
  apply hi.congr
  exact Filter.Eventually.of_forall (fun ξ => by
    simp only [secondMomentDecay,tenthDecay,Real.norm_eq_abs,
      Real.rpow_neg (by positivity : 0 ≤ 1+|ξ|)]
    norm_num
    field_simp
    )

noncomputable def arithmeticCorrelation (R ξ η : ℝ) (I : Finset ℕ) (m : ℕ) : ℝ :=
  ∑ n ∈ I, divisorRadicalWeight R ξ n * divisorRadicalWeight R η (m-n)

theorem kernel_sum_eq_correlation (R ξ η : ℝ) (I : Finset ℕ) (m : ℕ) :
    (∑ n ∈ I, kernelWeight R n ξ * kernelWeight R (m-n) η) =
      (tenthDecay ξ*tenthDecay η)*arithmeticCorrelation R ξ η I m := by
  unfold arithmeticCorrelation
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  unfold kernelWeight
  ring

/-- Conditional analytic interface: the correlation bound is an explicit
hypothesis, not a library axiom or a claimed Henriot instantiation. -/
theorem correlation_bound_transfers {R : ℝ} (hR : 1 < R)
    (I : Finset ℕ) (m : ℕ) {K : ℝ}
    (hK : ∀ ξ η : ℝ, arithmeticCorrelation R ξ η I m ≤
      K*(1+|ξ|)^2*(1+|η|)^2) :
    (∑ n ∈ I, radicalMajorant R n * radicalMajorant R (m-n)) ≤
      (Real.log R)^2*K*(∫ ξ : ℝ, secondMomentDecay ξ)^2 := by
  let A : ℝ → ℝ → ℝ := fun ξ η =>
    ∑ n ∈ I, kernelWeight R n ξ * kernelWeight R (m-n) η
  have hinner (ξ : ℝ) : Integrable (A ξ) :=
    integrable_finsetSum I (fun n _ => pair_inner_integrable hR n (m-n) ξ)
  have houter : Integrable (fun ξ : ℝ => ∫ η : ℝ, A ξ η) := by
    have he (ξ : ℝ) : (∫ η : ℝ, A ξ η) =
        ∑ n ∈ I, ∫ η : ℝ, kernelWeight R n ξ * kernelWeight R (m-n) η :=
      integral_finsetSum I (fun n _ => pair_inner_integrable hR n (m-n) ξ)
    simp_rw [he]
    exact integrable_finsetSum I (fun n _ => pair_outer_integrable hR n (m-n))
  have point (ξ η : ℝ) : A ξ η ≤ K*secondMomentDecay ξ*secondMomentDecay η := by
    dsimp [A]
    rw [kernel_sum_eq_correlation]
    have hb := mul_le_mul_of_nonneg_left (hK ξ η)
      (mul_nonneg (tenthDecay_nonneg ξ) (tenthDecay_nonneg η))
    convert hb using 1 <;> first | rfl | (unfold secondMomentDecay; ring)
  have innerle (ξ : ℝ) : (∫ η : ℝ, A ξ η) ≤
      K*secondMomentDecay ξ*(∫ η : ℝ, secondMomentDecay η) := by
    rw [← integral_const_mul]
    exact integral_mono (hinner ξ)
      (secondMomentDecay_integrable.const_mul _) (point ξ)
  have outerle : (∫ ξ : ℝ, ∫ η : ℝ, A ξ η) ≤
      K*(∫ ξ : ℝ, secondMomentDecay ξ)^2 := by
    calc
      _ ≤ ∫ ξ : ℝ, K*secondMomentDecay ξ*(∫ η : ℝ, secondMomentDecay η) :=
        integral_mono houter ((secondMomentDecay_integrable.const_mul K).mul_const _) innerle
      _ = _ := by rw [integral_mul_const,integral_const_mul]; ring
  rw [finite_convolution_integral hR I m]
  have hb := mul_le_mul_of_nonneg_left outerle (sq_nonneg (Real.log R))
  convert hb using 1 <;> first | rfl | ring

end GoldbachCircleMethodRadicalCorrelationTransferV18161
