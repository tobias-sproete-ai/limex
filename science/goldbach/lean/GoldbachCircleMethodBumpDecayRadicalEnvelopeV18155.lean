import GoldbachCircleMethodActualCompanionRadicalIntegralV18154
import Mathlib.Topology.Algebra.Module.FiniteDimension

set_option autoImplicit false
open scoped BigOperators Classical ContDiff FourierTransform SchwartzMap
open MeasureTheory
open GoldbachCircleMethodBumpFourierRepresentationV18143
open GoldbachCircleMethodLocalEulerRadicalBoundsV18149
open GoldbachCircleMethodActualCompanionRadicalIntegralV18154
namespace GoldbachCircleMethodBumpDecayRadicalEnvelopeV18155

/-- The actual normalized, rescaled Fourier weight is itself Schwartz. -/
theorem actual_bump_weight_is_schwartz {G : ℝ → ℝ}
    (hc : HasCompactSupport G) (hd : ContDiff ℝ ∞ G) :
    ∃ F : SchwartzMap ℝ ℂ, (F : ℝ → ℂ) = bumpFourierWeight G := by
  let F : SchwartzMap ℝ ℂ :=
    (weightedBump_compact hc).toSchwartzMap (weightedBump_smooth hd)
  let L : ℝ ≃L[ℝ] ℝ := (LinearEquiv.smulOfNeZero ℝ ℝ ((2*Real.pi)⁻¹)
    (inv_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero))).toContinuousLinearEquiv
  let H : SchwartzMap ℝ ℂ := (1/((2*Real.pi : ℝ) : ℂ)) •
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L (𝓕⁻ F))
  refine ⟨H,funext (fun ξ => ?_)⟩
  change (1/((2*Real.pi : ℝ) : ℂ)) * (𝓕⁻ F) (L ξ) = bumpFourierWeight G ξ
  have hL : L ξ = ξ/(2*Real.pi) := by
    change (2*Real.pi)⁻¹ * ξ = ξ/(2*Real.pi)
    ring
  rw [hL,SchwartzMap.fourierInv_coe]
  rfl

/-- Explicit finite seminorm expression supplies the bump-dependent constant. -/
theorem schwartz_decay_tenth (F : SchwartzMap ℝ ℂ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ ξ : ℝ, ‖F ξ‖ ≤ B/(1+|ξ|)^10 := by
  let B : ℝ := 2^10 * (Finset.Iic (10,0)).sup
    (fun m : ℕ × ℕ => SchwartzMap.seminorm ℂ m.1 m.2) F
  refine ⟨B,by dsimp [B]; positivity,fun ξ => ?_⟩
  apply (le_div_iff₀ (by positivity : 0 < (1+|ξ|)^10)).mpr
  have hb := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ)
    (m := (10,0)) (k := 10) (n := 0) le_rfl le_rfl F ξ
  simpa only [norm_iteratedFDeriv_zero,Real.norm_eq_abs,mul_comm] using hb

theorem actual_bump_decay_tenth {G : ℝ → ℝ}
    (hc : HasCompactSupport G) (hd : ContDiff ℝ ∞ G) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ ξ : ℝ, ‖bumpFourierWeight G ξ‖ ≤ B/(1+|ξ|)^10 := by
  obtain ⟨F,hF⟩ := actual_bump_weight_is_schwartz hc hd
  obtain ⟨B,hB,hbound⟩ := schwartz_decay_tenth F
  exact ⟨B,hB,fun ξ => by simpa only [hF] using hbound ξ⟩

noncomputable def tenthDecay (ξ : ℝ) : ℝ := 1/(1+|ξ|)^10

theorem tenthDecay_nonneg (ξ : ℝ) : 0 ≤ tenthDecay ξ := by
  unfold tenthDecay
  positivity

theorem tenthDecay_integrable : Integrable tenthDecay := by
  have hi := integrable_one_add_norm (E := ℝ) (μ := (volume : Measure ℝ))
    (r := (10 : ℝ)) (by norm_num)
  apply hi.congr
  exact Filter.Eventually.of_forall (fun ξ => by
    simp only [tenthDecay,Real.norm_eq_abs,Real.rpow_neg (by positivity : 0 ≤ 1+|ξ|),one_div]
    norm_num)

theorem weighted_tenth_radical_integrable {R : ℝ} (hR : 1 < R) (N : ℕ) :
    Integrable (fun ξ => tenthDecay ξ*radicalEnvelope R ξ N) := by
  apply tenthDecay_integrable.mono'
  · exact (show Continuous tenthDecay by
      unfold tenthDecay
      exact continuous_const.div (by fun_prop) (fun ξ => by positivity)).aestronglyMeasurable.mul
      (continuous_radicalEnvelope R N).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun ξ => by
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (tenthDecay_nonneg ξ) (radicalEnvelope_nonneg hR ξ N))]
    exact mul_le_of_le_one_right (tenthDecay_nonneg ξ) (radicalEnvelope_le_one hR ξ N))

/-- Same radical envelope as the V98 paper candidate, now a defined integral. -/
noncomputable def radicalMajorant (R : ℝ) (N : ℕ) : ℝ :=
  (N.divisors.card : ℝ)*Real.log R*
    (∫ ξ : ℝ, tenthDecay ξ*radicalEnvelope R ξ N)

theorem radicalMajorant_nonneg {R : ℝ} (hR : 1 < R) (N : ℕ) :
    0 ≤ radicalMajorant R N := by
  unfold radicalMajorant
  apply mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Real.log_pos hR).le)
  exact integral_nonneg (fun ξ => mul_nonneg (tenthDecay_nonneg ξ) (radicalEnvelope_nonneg hR ξ N))

theorem actual_weighted_integral_le_decay {G : ℝ → ℝ}
    (hc : HasCompactSupport G) (hd : ContDiff ℝ ∞ G)
    {R : ℝ} (hR : 1 < R) (N : ℕ) {B : ℝ}
    (hB : ∀ ξ : ℝ, ‖bumpFourierWeight G ξ‖ ≤ B/(1+|ξ|)^10) :
    (∫ ξ : ℝ, ‖bumpFourierWeight G ξ‖*radicalEnvelope R ξ N) ≤
      B*(∫ ξ : ℝ, tenthDecay ξ*radicalEnvelope R ξ N) := by
  rw [← integral_const_mul]
  apply integral_mono (integrable_weighted_radical hR N (bumpFourierWeight_integrable hc hd))
    ((weighted_tenth_radical_integrable hR N).const_mul B)
  intro ξ
  have hh := mul_le_mul_of_nonneg_right (hB ξ) (radicalEnvelope_nonneg hR ξ N)
  simpa only [tenthDecay,div_eq_mul_inv,mul_one,one_mul,mul_assoc] using hh

end GoldbachCircleMethodBumpDecayRadicalEnvelopeV18155
