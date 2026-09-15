import GoldbachCircleMethodCompanionIntegralInterchangeV18142
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

set_option autoImplicit false
open scoped BigOperators Classical FourierTransform SchwartzMap ContDiff
open MeasureTheory
open GoldbachCircleMethodCompanionAbsoluteConvergenceV18141
open GoldbachCircleMethodCompanionIntegralInterchangeV18142

namespace GoldbachCircleMethodBumpFourierRepresentationV18143

noncomputable def weightedBump (G : ℝ → ℝ) (t : ℝ) : ℂ :=
  (Real.exp t : ℂ)*(G t : ℂ)

theorem weightedBump_compact {G : ℝ → ℝ} (hG : HasCompactSupport G) :
    HasCompactSupport (weightedBump G) := by
  have hc : HasCompactSupport (fun t : ℝ => (G t : ℂ)) :=
    hG.comp_left Complex.ofReal_zero
  exact hc.mul_left

theorem weightedBump_smooth {G : ℝ → ℝ} (hG : ContDiff ℝ ∞ G) :
    ContDiff ℝ ∞ (weightedBump G) := by
  unfold weightedBump
  exact (Complex.ofRealCLM.contDiff.comp Real.contDiff_exp).mul
    (Complex.ofRealCLM.contDiff.comp hG)

/-- Exact normalization of the V98 positive-sign Fourier weight.
The inverse transform of Mathlib uses exp(+2*pi*i*t*eta). -/
noncomputable def bumpFourierWeight (G : ℝ → ℝ) (ξ : ℝ) : ℂ :=
  (1/((2*Real.pi : ℝ) : ℂ)) *
    (𝓕⁻ (weightedBump G)) (ξ/(2*Real.pi))

/-- Discharges the weight-integrability premise using the actual
smooth compactly supported bump, not a replacement function. -/
theorem bumpFourierWeight_integrable {G : ℝ → ℝ}
    (hc : HasCompactSupport G) (hd : ContDiff ℝ ∞ G) :
    Integrable (bumpFourierWeight G) := by
  let F : SchwartzMap ℝ ℂ :=
    (weightedBump_compact hc).toSchwartzMap (weightedBump_smooth hd)
  have heq : (F : ℝ → ℂ)=weightedBump G := rfl
  have hInv : Integrable (𝓕⁻ (weightedBump G)) := by
    have hh : Integrable (fun x : ℝ => (𝓕⁻ F) x) (volume : Measure ℝ) :=
      (𝓕⁻ F).integrable
    exact hh.congr (Filter.Eventually.of_forall (fun x => by
      rw [SchwartzMap.fourierInv_coe,heq]))
  have hscale := hInv.comp_div (mul_ne_zero (by norm_num : (2 : ℝ)≠0) Real.pi_ne_zero)
  exact hscale.const_mul _

/-- The normalized weight equals the literal V98 integral with a
positive i*xi*t phase. No implicit sign or 2*pi change is allowed. -/
theorem bumpFourierWeight_exact_integral (G : ℝ → ℝ) (ξ : ℝ) :
    bumpFourierWeight G ξ =
      (1/((2*Real.pi : ℝ) : ℂ)) *
        ∫ t : ℝ, weightedBump G t * Complex.exp (Complex.I*(ξ : ℂ)*(t : ℂ)) := by
  unfold bumpFourierWeight
  congr 1
  rw [Real.fourierInv_eq']
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun t => by
    dsimp only
    have he : ((2*Real.pi*inner ℝ t (ξ/(2*Real.pi)) : ℝ) : ℂ)*Complex.I =
        Complex.I*(ξ : ℂ)*(t : ℂ) := by
      change ((2*Real.pi*((ξ/(2*Real.pi))*t) : ℝ) : ℂ)*Complex.I = _
      push_cast
      field_simp
    rw [he]
    simp only [smul_eq_mul,mul_comm])

/-- Pointwise inversion for the actual bump, via the Schwartz-space
Fourier pair in the pinned Mathlib. -/
theorem weightedBump_fourier_inverse {G : ℝ → ℝ}
    (hc : HasCompactSupport G) (hd : ContDiff ℝ ∞ G) (t : ℝ) :
    (𝓕 (𝓕⁻ (weightedBump G))) t = weightedBump G t := by
  let F : SchwartzMap ℝ ℂ :=
    (weightedBump_compact hc).toSchwartzMap (weightedBump_smooth hd)
  have heq : (F : ℝ → ℂ)=weightedBump G := rfl
  have hpair : (𝓕 ((𝓕⁻ F) : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ) = F :=
    FourierTransform.fourier_fourierInv_eq F
  have hp := congrArg (fun f : SchwartzMap ℝ ℂ => f t) hpair
  simpa only [SchwartzMap.fourier_coe,SchwartzMap.fourierInv_coe,heq] using hp

/-- Literal negative-phase inverse of the positive-phase weight.
The real change of variables records its exact 2*pi Jacobian. -/
theorem bumpFourierWeight_inversion {G : ℝ → ℝ}
    (hc : HasCompactSupport G) (hd : ContDiff ℝ ∞ G) (t : ℝ) :
    (∫ ξ : ℝ, bumpFourierWeight G ξ *
      Complex.exp (-Complex.I*(ξ : ℂ)*(t : ℂ))) = weightedBump G t := by
  let c : ℝ := 2*Real.pi
  have hcpos : 0 < c := mul_pos (by norm_num) Real.pi_pos
  have hcne : (c : ℂ) ≠ 0 := by exact_mod_cast hcpos.ne'
  let g : ℝ → ℂ := fun η => (𝓕⁻ (weightedBump G)) η *
    Complex.exp (-Complex.I*(c : ℂ)*(η : ℂ)*(t : ℂ))
  have hs (ξ : ℝ) : bumpFourierWeight G ξ *
      Complex.exp (-Complex.I*(ξ : ℂ)*(t : ℂ)) = (1/(c : ℂ))*g (ξ/c) := by
    dsimp [bumpFourierWeight,g]
    rw [mul_assoc]
    congr 2
    push_cast
    field_simp
  calc
    _ = (1/(c : ℂ))*(∫ ξ : ℝ, g (ξ/c)) := by
      simp_rw [hs]
      exact integral_const_mul _ _
    _ = (1/(c : ℂ))*(|c| • ∫ η : ℝ, g η) := by
      rw [Measure.integral_comp_div]
    _ = ∫ η : ℝ, g η := by
      rw [abs_of_pos hcpos,Complex.real_smul]
      field_simp
    _ = (𝓕 (𝓕⁻ (weightedBump G))) t := by
      rw [Real.fourier_eq']
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun η => by
        change (𝓕⁻ (weightedBump G)) η *
          Complex.exp (-Complex.I*((2*Real.pi : ℝ) : ℂ)*(η : ℂ)*(t : ℂ)) =
          Complex.exp (((-2*Real.pi*(t*η) : ℝ) : ℂ)*Complex.I) *
            (𝓕⁻ (weightedBump G)) η
        rw [mul_comm]
        congr 1
        congr 1
        push_cast
        ring)
    _ = weightedBump G t := weightedBump_fourier_inverse hc hd t

/-- Specializes the already checked interchange to this actual bump
weight; no Integrable psi premise remains. -/
theorem actual_bump_prefactored_interchange {G : ℝ → ℝ}
    (hc : HasCompactSupport G) (hd : ContDiff ℝ ∞ G)
    {R : ℝ} (hR : 1 < R) (k : ℕ) {m : ℕ} (hm : 0 < m) :
    HasSum
      (fun n : ℕ => ∫ ξ : ℝ,
        (bumpFourierWeight G ξ/((m : ℂ)^radicalExponent R ξ)) *
          complementaryDirichletTerm k (radicalExponent R ξ) n)
      (∫ ξ : ℝ, (bumpFourierWeight G ξ/((m : ℂ)^radicalExponent R ξ)) *
        (∑' n, complementaryDirichletTerm k (radicalExponent R ξ) n)) :=
  prefactored_vertical_series_hasSum_integral hR k hm _
    (bumpFourierWeight_integrable hc hd)

end GoldbachCircleMethodBumpFourierRepresentationV18143
