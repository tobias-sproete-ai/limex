import GoldbachCircleMethodActualResidualMomentCompositionV18193

/-! Explicit elementary admission of V193's actual scale hypotheses.
This is not a source theorem, reserve or a Goldbach result. -/
set_option autoImplicit false
open scoped Classical BigOperators ContDiff
open GoldbachCircleMethodLogCutoffPresieveBindingV18120
open GoldbachCircleMethodActiveExceptionalCenteringV18129
open GoldbachCircleMethodActualInputModelResidualV18138
open GoldbachCircleMethodRealApproximationMinorAdapterV1873
open GoldbachCircleMethodSupportedModelErrorConvolutionV18182
open GoldbachCircleMethodUncorrectedSupportedErrorConvolutionV18184
open GoldbachCircleMethodSupportedResidualParsevalV18190

namespace GoldbachCircleMethodResidualScaleAdmissionV18196

/-- For a genuine block x>1, the lower scale restriction already forces
the displayed logarithmic threshold; x=1 is explicitly outside the equivalence. -/
theorem lower_scale_iff_log_threshold (x rho : ℝ) (hx : 1 < x) (hrho : 0 < rho) :
    Real.exp (Real.sqrt (Real.log x)) ≤ x^rho ↔ 1/rho^2 ≤ Real.log x := by
  have hx0 : 0 < x := lt_trans zero_lt_one hx
  have hl : 0 < Real.log x := Real.log_pos hx
  rw [Real.rpow_def_of_pos hx0, Real.exp_le_exp, Real.sqrt_le_iff]
  constructor
  · rintro ⟨_hpos,hsq⟩
    apply (div_le_iff₀ (sq_pos_of_pos hrho)).mpr
    by_contra h
    have hh := mul_lt_mul_of_pos_left (lt_of_not_ge h) hl
    nlinarith
  · intro h
    have hp : (1 : ℝ) ≤ Real.log x * rho^2 :=
      (div_le_iff₀ (sq_pos_of_pos hrho)).mp h
    refine ⟨mul_nonneg hl.le hrho.le, ?_⟩
    have hh := mul_le_mul_of_nonneg_left hp hl.le
    nlinarith

noncomputable def logThreshold (rho : ℝ) : ℝ :=
  max (Real.log 6) (max (1 / rho^2) (Real.log 2 / rho))

noncomputable def blockThreshold (rho : ℝ) : ℕ :=
  ⌈Real.exp (logThreshold rho)⌉₊

theorem actual_scale_admission (rho : ℝ)
    (hrho : 0 < rho) (hrhoUpper : rho ≤ (1 : ℝ) / 10000)
    (B : ℕ) (hB : blockThreshold rho ≤ B) :
    6 ≤ B ∧ 2 ≤ (B : ℝ)^rho ∧
      Real.exp (Real.sqrt (Real.log (B : ℝ))) ≤ (B : ℝ)^rho ∧
      (B : ℝ)^rho ≤ (B : ℝ)^((1 : ℝ) / 10000) := by
  have hexp : Real.exp (logThreshold rho) ≤ (B : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hB)
  have hBpos : (0 : ℝ) < B := (Real.exp_pos _).trans_le hexp
  have hlog : logThreshold rho ≤ Real.log (B : ℝ) := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos _) hexp
  have hlog6 : Real.log 6 ≤ Real.log (B : ℝ) :=
    (le_max_left _ _).trans hlog
  have hB6r : (6 : ℝ) ≤ B := by
    have h := Real.exp_le_exp.mpr hlog6
    simpa only [Real.exp_log (by norm_num : (0 : ℝ) < 6),
      Real.exp_log hBpos] using h
  have hB6 : 6 ≤ B := by exact_mod_cast hB6r
  have hlogB0 : 0 ≤ Real.log (B : ℝ) :=
    Real.log_nonneg (by linarith)
  have hinv : 1 / rho^2 ≤ Real.log (B : ℝ) :=
    (le_trans (le_max_left _ _) (le_max_right _ _)).trans hlog
  have hlog2 : Real.log 2 / rho ≤ Real.log (B : ℝ) :=
    (le_trans (le_max_right _ _) (le_max_right _ _)).trans hlog
  have hpower2 : 2 ≤ (B : ℝ)^rho := by
    rw [Real.rpow_def_of_pos hBpos]
    have hmul : Real.log 2 ≤ Real.log (B : ℝ) * rho :=
      (div_le_iff₀ hrho).mp hlog2
    have h := Real.exp_le_exp.mpr hmul
    simpa only [Real.exp_log (by norm_num : (0 : ℝ) < 2)] using h
  have hprod : (1 : ℝ) ≤ Real.log (B : ℝ) * rho^2 :=
    (div_le_iff₀ (sq_pos_of_pos hrho)).mp hinv
  have hsq : Real.log (B : ℝ) ≤ (Real.log (B : ℝ)*rho)^2 := by
    have h := mul_le_mul_of_nonneg_left hprod hlogB0
    nlinarith
  have hsqrt : Real.sqrt (Real.log (B : ℝ)) ≤ Real.log (B : ℝ)*rho :=
    Real.sqrt_le_iff.mpr ⟨mul_nonneg hlogB0 hrho.le, hsq⟩
  refine ⟨hB6,hpower2,?_,?_⟩
  · rw [Real.rpow_def_of_pos hBpos]
    exact Real.exp_le_exp.mpr hsqrt
  · exact Real.rpow_le_rpow_of_exponent_le (by linarith) hrhoUpper

/-- The logarithmic admission threshold is quantitatively large in the allowed
rho range; this is not a finite verification range for Goldbach. -/
theorem logThreshold_ge_one_hundred_million (rho : ℝ)
    (hrho : 0 < rho) (hupper : rho ≤ (1:ℝ)/10000) :
    (100000000:ℝ) ≤ logThreshold rho := by
  have hs := mul_self_le_mul_self hrho.le hupper
  have hi : (100000000:ℝ) ≤ 1/rho^2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hrho)).mpr
    nlinarith
  exact hi.trans ((le_max_left _ _).trans (le_max_right _ _))

/-- An actual admitted power scale is strictly larger than one. -/
theorem one_lt_power_of_admitted (rho : ℝ)
    (hrho : 0 < rho) (hrhoUpper : rho ≤ (1:ℝ)/10000)
    (B : ℕ) (hB : blockThreshold rho ≤ B) :
    1 < (B:ℝ)^rho :=
  lt_of_lt_of_le (by norm_num) (actual_scale_admission rho hrho hrhoUpper B hB).2.1

/-- V193 principal moment with all three scale tests discharged by an explicit
block threshold. The analytical source and fixed mask assumptions remain. -/
theorem principal_moment_above_explicit_scale {G : ℝ → ℝ}
    (hc : HasCompactSupport G) (hd : ContDiff ℝ ∞ G)
    (hGsupport : ∀ t : ℝ, 2 < t → G t = 0)
    (C MG rho : ℝ) (hC : 0 ≤ C) (hV : RealVaughanEstimate C)
    (hMG : 0 ≤ MG) (hG : ∀ u : ℝ, |G u| ≤ MG)
    (hplateau : ∀ u : ℝ, 0 ≤ u → u ≤ 1 → G u = 1)
    (hrho : 0 < rho) (hrhoUpper : rho ≤ (1:ℝ)/10000) :
    ∃ Crho : ℝ, 0 ≤ Crho ∧ ∀ (B : ℕ) (hB : blockThreshold rho ≤ B),
      (∑ k ∈ Finset.Icc (0 : ℤ) (2 * B : ℕ),
        ‖integerPairConvolution (blockCarrier B)
          (fun N => inputPrincipalResidual B N ((B : ℝ)^rho)
            (one_lt_power_of_admitted rho hrho hrhoUpper B hB) G)
          (fun N => blockInput B N + supportedPrincipalModel B N ((B : ℝ)^rho) G) k‖^2) ≤
        Crho * (B : ℝ)^3 * ((B : ℝ)^rho)^(-(5 : ℝ) / 8) *
          (Real.log (B : ℝ))^2 := by
  obtain ⟨Crho,hCrho,hbound⟩ :=
    GoldbachCircleMethodActualResidualMomentCompositionV18193.actual_principal_residual_moment_power_bound
      hc hd hGsupport C MG rho hC hV hMG hG hplateau hrho
  refine ⟨Crho,hCrho,?_⟩
  intro B hB
  obtain ⟨hB6,hR2,hlower,hupper⟩ := actual_scale_admission rho hrho hrhoUpper B hB
  exact hbound B hB6 hR2 hlower hupper

/-- Active counterpart: the same Crho is chosen before B, b and the actual slot. -/
theorem active_moment_above_explicit_scale {G : ℝ → ℝ}
    (hc : HasCompactSupport G) (hd : ContDiff ℝ ∞ G)
    (hGsupport : ∀ t : ℝ, 2 < t → G t = 0)
    (C MG rho : ℝ) (hC : 0 ≤ C) (hV : RealVaughanEstimate C)
    (hMG : 0 ≤ MG) (hG : ∀ u : ℝ, |G u| ≤ MG)
    (hplateau : ∀ u : ℝ, 0 ≤ u → u ≤ 1 → G u = 1)
    (hrho : 0 < rho) (hrhoUpper : rho ≤ (1:ℝ)/10000) :
    ∃ Crho : ℝ, 0 ≤ Crho ∧ ∀ (B : ℕ) (hB : blockThreshold rho ≤ B),
      ∀ b : ℝ, 0 ≤ b → b ≤ 1 →
      ∀ e : CharacterSlot ⌊((B : ℝ)^rho)^2⌋₊,
      (∑ k ∈ Finset.Icc (0 : ℤ) (2 * B : ℕ),
        ‖integerPairConvolution (blockCarrier B)
          (fun N => inputActiveResidual B N ((B : ℝ)^rho)
            (one_lt_power_of_admitted rho hrho hrhoUpper B hB) b G e)
          (fun N => blockInput B N +
            supportedAdjustedModel B N ((B : ℝ)^rho) b G e) k‖^2) ≤
        Crho * (B : ℝ)^3 * ((B : ℝ)^rho)^(-(5 : ℝ) / 8) *
          (Real.log (B : ℝ))^2 := by
  obtain ⟨Crho,hCrho,hbound⟩ :=
    GoldbachCircleMethodActualResidualMomentCompositionV18193.actual_active_residual_moment_power_bound
      hc hd hGsupport C MG rho hC hV hMG hG hplateau hrho
  refine ⟨Crho,hCrho,?_⟩
  intro B hB b hb hb1 e
  obtain ⟨hB6,hR2,hlower,hupper⟩ := actual_scale_admission rho hrho hrhoUpper B hB
  exact hbound B hB6 hR2 hlower hupper b hb hb1 e

end GoldbachCircleMethodResidualScaleAdmissionV18196
