import GoldbachCircleMethodRadicalArithmeticClassV18159

set_option autoImplicit false
open scoped BigOperators Classical
open MeasureTheory
open GoldbachCircleMethodLocalEulerRadicalBoundsV18149
open GoldbachCircleMethodBumpDecayRadicalEnvelopeV18155
open GoldbachCircleMethodRadicalArithmeticClassV18159
namespace GoldbachCircleMethodRadicalConvolutionIntegralV18160

noncomputable def kernelWeight (R : ℝ) (n : ℕ) (ξ : ℝ) : ℝ :=
  tenthDecay ξ * divisorRadicalWeight R ξ n

theorem kernelWeight_nonneg {R : ℝ} (hR : 1 < R) (n : ℕ) (ξ : ℝ) :
    0 ≤ kernelWeight R n ξ :=
  mul_nonneg (tenthDecay_nonneg ξ) (divisorRadicalWeight_nonneg hR ξ n)

theorem kernelWeight_integrable {R : ℝ} (hR : 1 < R) (n : ℕ) :
    Integrable (kernelWeight R n) := by
  have hi := (weighted_tenth_radical_integrable hR n).const_mul (n.divisors.card : ℝ)
  convert hi using 1
  funext ξ
  unfold kernelWeight divisorRadicalWeight
  ring

theorem majorant_eq_integral (R : ℝ) (n : ℕ) :
    radicalMajorant R n = Real.log R * (∫ ξ : ℝ, kernelWeight R n ξ) := by
  have he : kernelWeight R n = fun ξ => (n.divisors.card : ℝ) *
      (tenthDecay ξ * radicalEnvelope R ξ n) := by
    funext ξ
    unfold kernelWeight divisorRadicalWeight
    ring
  rw [he,integral_const_mul]
  unfold radicalMajorant
  ring

theorem pair_inner_integrable {R : ℝ} (hR : 1 < R) (n m : ℕ) (ξ : ℝ) :
    Integrable (fun η : ℝ => kernelWeight R n ξ * kernelWeight R m η) :=
  (kernelWeight_integrable hR m).const_mul _

theorem pair_outer_integrable {R : ℝ} (hR : 1 < R) (n m : ℕ) :
    Integrable (fun ξ : ℝ => ∫ η : ℝ, kernelWeight R n ξ * kernelWeight R m η) := by
  simp_rw [integral_const_mul]
  exact (kernelWeight_integrable hR n).mul_const _

theorem majorant_product_integral (R : ℝ) (n m : ℕ) :
    radicalMajorant R n * radicalMajorant R m =
      (Real.log R)^2 * (∫ ξ : ℝ, ∫ η : ℝ,
        kernelWeight R n ξ * kernelWeight R m η) := by
  rw [majorant_eq_integral,majorant_eq_integral]
  simp_rw [integral_const_mul]
  rw [integral_mul_const]
  ring

/-- Exact finite sum transfer. No short-interval or correlation estimate
is asserted; application must supply its actual finite carrier. -/
theorem finite_convolution_integral {R : ℝ} (hR : 1 < R)
    (I : Finset ℕ) (m : ℕ) :
    (∑ n ∈ I, radicalMajorant R n * radicalMajorant R (m-n)) =
      (Real.log R)^2 * (∫ ξ : ℝ, ∫ η : ℝ,
        ∑ n ∈ I, kernelWeight R n ξ * kernelWeight R (m-n) η) := by
  have inner (ξ : ℝ) :
      (∫ η : ℝ, ∑ n ∈ I, kernelWeight R n ξ * kernelWeight R (m-n) η) =
      ∑ n ∈ I, ∫ η : ℝ, kernelWeight R n ξ * kernelWeight R (m-n) η :=
    integral_finsetSum I (fun n _ => pair_inner_integrable hR n (m-n) ξ)
  simp_rw [inner]
  rw [integral_finsetSum I (fun n _ => pair_outer_integrable hR n (m-n))]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  exact majorant_product_integral R n (m-n)

end GoldbachCircleMethodRadicalConvolutionIntegralV18160
