import GoldbachCircleMethodCompanionAbsoluteConvergenceV18141
import Mathlib.MeasureTheory.Integral.DominatedConvergence

set_option autoImplicit false
open scoped BigOperators Classical
open MeasureTheory
open GoldbachCircleMethodCompanionAbsoluteConvergenceV18141

namespace GoldbachCircleMethodCompanionIntegralInterchangeV18142

theorem continuous_radicalExponent (R : ℝ) :
    Continuous (radicalExponent R) := by
  unfold radicalExponent
  fun_prop

/-- Actual coefficient continuity on the fixed vertical line. -/
theorem continuous_complementary_vertical_term (R : ℝ) (k n : ℕ) :
    Continuous (fun ξ : ℝ => complementaryDirichletTerm k (radicalExponent R ξ) n) := by
  unfold complementaryDirichletTerm
  by_cases h : Squarefree n ∧ Nat.Coprime k n
  · simp_rw [if_pos h]
    have hn : (n : ℂ)≠0 := by exact_mod_cast h.1.ne_zero
    have hp : (n.totient : ℂ)≠0 := by
      exact_mod_cast (Nat.totient_pos.mpr h.1.ne_zero.bot_lt).ne'
    have hc : Continuous (fun ξ : ℝ => (n : ℂ)^radicalExponent R ξ) :=
      (continuous_radicalExponent R).const_cpow (Or.inl hn)
    exact continuous_const.div (continuous_const.mul hc)
      (fun ξ => mul_ne_zero hp (Complex.cpow_ne_zero_iff.mpr (Or.inl hn)))
  · simp only [h,if_false]
    exact continuous_const

/-- Sum/integral interchange for the actual complementary coefficient.
The Fourier weight is required to be integrable, explicitly. No assertion
that an unspecified weight is the transform of G is made. -/
theorem weighted_vertical_series_hasSum_integral {R : ℝ} (hR : 1<R)
    (k : ℕ) (ψ : ℝ → ℂ) (hψ : Integrable ψ) :
    HasSum
      (fun n : ℕ => ∫ ξ : ℝ, ψ ξ *
        complementaryDirichletTerm k (radicalExponent R ξ) n)
      (∫ ξ : ℝ, ψ ξ * (∑' n, complementaryDirichletTerm k (radicalExponent R ξ) n)) := by
  let D : ℕ → ℝ := divisorMajorant (1/Real.log R)
  have hD : Summable D :=
    summable_divisorMajorant (one_div_pos.mpr (Real.log_pos hR))
  apply hasSum_integral_of_dominated_convergence
    (fun n ξ => ‖ψ ξ‖*D n)
  · intro n
    exact hψ.aestronglyMeasurable.mul
      (continuous_complementary_vertical_term R k n).aestronglyMeasurable
  · intro n
    exact Filter.Eventually.of_forall (fun ξ => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left
        ((radical_line_absolute_domination hR k ξ).2.1 n) (norm_nonneg _))
  · exact Filter.Eventually.of_forall (fun ξ => hD.mul_left ‖ψ ξ‖)
  · have heq : (fun ξ => ∑' n, ‖ψ ξ‖*D n) =
        (fun ξ => ‖ψ ξ‖*(∑' n,D n)) := by
      funext ξ
      exact hD.tsum_mul_left _
    rw [heq]
    exact hψ.norm.mul_const _
  · exact Filter.Eventually.of_forall (fun ξ =>
      (summable_complementaryDirichletTerm k (radicalExponent_re_pos hR ξ)).hasSum.mul_left (ψ ξ))

theorem weighted_vertical_integral_tsum {R : ℝ} (hR : 1<R)
    (k : ℕ) (ψ : ℝ → ℂ) (hψ : Integrable ψ) :
    (∫ ξ : ℝ, ψ ξ * (∑' n, complementaryDirichletTerm k (radicalExponent R ξ) n)) =
      ∑' n : ℕ, ∫ ξ : ℝ, ψ ξ *
        complementaryDirichletTerm k (radicalExponent R ξ) n :=
  (weighted_vertical_series_hasSum_integral hR k ψ hψ).tsum_eq.symm


/-- The actual positive-integer prefactor has norm at most one
on the V98 line, including m=1. -/
theorem vertical_reciprocal_power_norm_le_one {R : ℝ} (hR : 1<R)
    {m : ℕ} (hm : 0 < m) (ξ : ℝ) :
    ‖1/((m : ℂ)^radicalExponent R ξ)‖ ≤ 1 := by
  rw [norm_div,norm_one,Complex.norm_natCast_cpow_of_pos hm]
  have hp : 1≤(m : ℝ)^(radicalExponent R ξ).re :=
    Real.one_le_rpow (by exact_mod_cast hm) (radicalExponent_re_pos hR ξ).le
  exact (div_le_one (zero_lt_one.trans_le hp)).mpr hp

theorem continuous_vertical_reciprocal_power (R : ℝ)
    {m : ℕ} (hm : 0 < m) :
    Continuous (fun ξ : ℝ => 1/((m : ℂ)^radicalExponent R ξ)) := by
  have hn : (m : ℂ)≠0 := by exact_mod_cast hm.ne'
  exact continuous_const.div
    ((continuous_radicalExponent R).const_cpow (Or.inl hn))
    (fun _ => Complex.cpow_ne_zero_iff.mpr (Or.inl hn))

/-- Therefore the actual factor (r*d)^(-s) can be attached without
inventing a new integrability hypothesis on the modified weight. -/
theorem integrable_weighted_vertical_power {R : ℝ} (hR : 1<R)
    {m : ℕ} (hm : 0 < m) (ψ : ℝ → ℂ) (hψ : Integrable ψ) :
    Integrable (fun ξ : ℝ => ψ ξ/((m : ℂ)^radicalExponent R ξ)) := by
  have hc := continuous_vertical_reciprocal_power R hm
  apply hψ.norm.mono'
  · exact (hψ.aestronglyMeasurable.mul hc.aestronglyMeasurable).congr
      (Filter.Eventually.of_forall (fun ξ => by simp [div_eq_mul_inv]))
  exact Filter.Eventually.of_forall (fun ξ => by
    calc
      _ = ‖ψ ξ‖*‖1/((m : ℂ)^radicalExponent R ξ)‖ := by
        rw [norm_div,norm_div,norm_one]
        ring
      _ ≤ ‖ψ ξ‖*1 :=
        mul_le_mul_of_nonneg_left (vertical_reciprocal_power_norm_le_one hR hm ξ)
          (norm_nonneg _)
      _ = _ := mul_one _)

/-- Interchange including the actual positive product m=r*d.
The only Fourier-weight premise remains Integrable psi. -/
theorem prefactored_vertical_series_hasSum_integral {R : ℝ} (hR : 1<R)
    (k : ℕ) {m : ℕ} (hm : 0 < m) (ψ : ℝ → ℂ) (hψ : Integrable ψ) :
    HasSum
      (fun n : ℕ => ∫ ξ : ℝ, (ψ ξ/((m : ℂ)^radicalExponent R ξ)) *
        complementaryDirichletTerm k (radicalExponent R ξ) n)
      (∫ ξ : ℝ, (ψ ξ/((m : ℂ)^radicalExponent R ξ)) *
        (∑' n, complementaryDirichletTerm k (radicalExponent R ξ) n)) :=
  weighted_vertical_series_hasSum_integral hR k _
    (integrable_weighted_vertical_power hR hm ψ hψ)

end GoldbachCircleMethodCompanionIntegralInterchangeV18142
