import GoldbachCircleMethodUnstarredIntervalSourceBindingV18188
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions

/-!
# Supported residual Parseval transfer, V1.8.190

This module zero-extends a finite sequence by summing only over its declared
carrier.  Its convolution uses integer frequencies and a pair-filtered finite
sum, so no truncated natural subtraction is present.  The final theorem applies
the literal V138 principal residual Fourier estimate.  It does not estimate the
companion energy or prove any later reserve, source, or Goldbach statement.
-/

set_option autoImplicit false

open scoped BigOperators Classical
open MeasureTheory AddCircle
open GoldbachCircleMethodFourierIdentityV171
open GoldbachCircleMethodFiniteCompanionBindingV18118
open GoldbachCircleMethodFiniteWindowConvolutionV18119
open GoldbachCircleMethodLogCutoffPresieveBindingV18120
open GoldbachCircleMethodPrincipalWindowBoundaryV18121
open GoldbachCircleMethodActualInputModelResidualV18138
open GoldbachCircleMethodRealApproximationMinorAdapterV1873
open GoldbachCircleMethodUncorrectedSupportedErrorConvolutionV18184
open GoldbachCircleMethodUnstarredIntervalSourceBindingV18188

namespace GoldbachCircleMethodSupportedResidualParsevalV18190

/-- Fourier polynomial of the zero extension of `a` from the finite carrier `J`. -/
noncomputable def supportedFourierPolynomial (J : Finset ℕ) (a : ℕ → ℂ) :
    C(UnitAddCircle, ℂ) :=
  ∑ n ∈ J, a n • fourier (n : ℤ)

/-- Integer-frequency convolution of two sequences supported on the same finite
carrier.  This is deliberately not expressed with natural subtraction. -/
noncomputable def integerPairConvolution (J : Finset ℕ) (v w : ℕ → ℂ)
    (k : ℤ) : ℂ :=
  ∑ n ∈ J, ∑ u ∈ J,
    if k = (n : ℤ) + (u : ℤ) then v n * w u else 0

/-- A convolution of two sequences supported on the actual block has no
integer-frequency coefficient outside `[0,2B]`. -/
theorem integerPairConvolution_block_zero_outside (B : ℕ) (v w : ℕ → ℂ)
    {k : ℤ} (hk : k ∉ Finset.Icc (0 : ℤ) (2 * B : ℕ)) :
    integerPairConvolution (blockCarrier B) v w k = 0 := by
  unfold integerPairConvolution
  apply Finset.sum_eq_zero
  intro n hn
  apply Finset.sum_eq_zero
  intro u hu
  rw [if_neg]
  intro heq
  apply hk
  rw [Finset.mem_Icc]
  constructor
  · rw [heq]
    positivity
  · rw [heq]
    norm_cast
    simp only [blockCarrier, Finset.mem_Ioc] at hn hu
    omega

@[simp] theorem supportedFourierPolynomial_apply (J : Finset ℕ) (a : ℕ → ℂ)
    (x : UnitAddCircle) :
    supportedFourierPolynomial J a x =
      ∑ n ∈ J, a n * fourier (n : ℤ) x := by
  simp [supportedFourierPolynomial, smul_eq_mul]

private lemma integrable_const_mul_fourier (c : ℂ) (n : ℤ) :
    Integrable (fun x : UnitAddCircle => c * fourier n x) haarAddCircle := by
  have h : Integrable (fourier n : UnitAddCircle → ℂ) haarAddCircle := by
    simpa only [IntegrableOn, Measure.restrict_univ] using
      (ContinuousOn.integrableOn_compact
        (μ := haarAddCircle) (K := Set.univ) isCompact_univ
        (fourier n).continuous.continuousOn)
  exact h.const_mul c

private lemma coeff_const_mul_fourier (c : ℂ) (n k : ℤ) :
    fourierCoeff (fun x : UnitAddCircle => c * fourier n x) k =
      if k = n then c else 0 := by
  rw [fourierCoeff.const_mul]
  rw [congrFun (fourierCoeff_fourier n) k]
  by_cases h : k = n
  · subst k
    simp
  · simp [h]

private lemma coeff_finset_fourier_sum (J : Finset ℕ) (a : ℕ → ℂ)
    (frequency : ℕ → ℤ) (k : ℤ) :
    fourierCoeff
        (fun x : UnitAddCircle => ∑ n ∈ J, a n * fourier (frequency n) x) k =
      ∑ n ∈ J, if k = frequency n then a n else 0 := by
  have hfun :
      (fun x : UnitAddCircle => ∑ n ∈ J, a n * fourier (frequency n) x) =
        ∑ n ∈ J, (fun x : UnitAddCircle => a n * fourier (frequency n) x) := by
    funext x
    simp only [Finset.sum_apply]
  rw [hfun, fourierCoeff.sum]
  simp only [Finset.sum_apply]
  · apply Finset.sum_congr rfl
    intro n hn
    exact coeff_const_mul_fourier _ _ _
  · intro n hn
    exact integrable_const_mul_fourier _ _

private lemma integrable_finset_fourier_sum (J : Finset ℕ) (a : ℕ → ℂ)
    (frequency : ℕ → ℤ) :
    Integrable
      (fun x : UnitAddCircle => ∑ n ∈ J, a n * fourier (frequency n) x)
      haarAddCircle := by
  have hfun :
      (fun x : UnitAddCircle => ∑ n ∈ J, a n * fourier (frequency n) x) =
        ∑ n ∈ J, (fun x : UnitAddCircle => a n * fourier (frequency n) x) := by
    funext x
    simp only [Finset.sum_apply]
  rw [hfun]
  exact integrable_finsetSum' _ fun n hn => integrable_const_mul_fourier _ _

theorem fourierCoeff_supportedFourierPolynomial (J : Finset ℕ) (a : ℕ → ℂ)
    (k : ℤ) :
    fourierCoeff (supportedFourierPolynomial J a) k =
      ∑ n ∈ J, if k = (n : ℤ) then a n else 0 := by
  rw [supportedFourierPolynomial]
  have hfun :
      (⇑(∑ n ∈ J, a n • fourier (n : ℤ)) : UnitAddCircle → ℂ) =
        (fun x : UnitAddCircle => ∑ n ∈ J, a n * fourier (n : ℤ) x) := by
    funext x
    simp [smul_eq_mul]
  rw [hfun]
  exact coeff_finset_fourier_sum J a (fun n => (n : ℤ)) k

private lemma fourierCoeff_supported_at (J : Finset ℕ) (a : ℕ → ℂ)
    {n : ℕ} (hn : n ∈ J) :
    fourierCoeff (supportedFourierPolynomial J a) (n : ℤ) = a n := by
  rw [fourierCoeff_supportedFourierPolynomial]
  calc
    (∑ m ∈ J, if (n : ℤ) = (m : ℤ) then a m else 0) =
        (if (n : ℤ) = (n : ℤ) then a n else 0) := by
      apply Finset.sum_eq_single n
      · intro m hm hmn
        simp [show n ≠ m by omega]
      · simp [hn]
    _ = a n := by simp

private lemma fourierCoeff_supported_zero (J : Finset ℕ) (a : ℕ → ℂ)
    {k : ℤ} (hk : k ∉ J.image (fun n : ℕ => (n : ℤ))) :
    fourierCoeff (supportedFourierPolynomial J a) k = 0 := by
  rw [fourierCoeff_supportedFourierPolynomial]
  apply Finset.sum_eq_zero
  intro n hn
  have hne : k ≠ (n : ℤ) := by
    intro h
    apply hk
    exact Finset.mem_image.mpr ⟨n, hn, h.symm⟩
  simp [hne]

/-- Exact Parseval identity for a finite supported Fourier polynomial. -/
theorem integral_supportedFourierPolynomial_norm_sq (J : Finset ℕ)
    (a : ℕ → ℂ) :
    (∫ x : UnitAddCircle, ‖supportedFourierPolynomial J a x‖ ^ 2 ∂haarAddCircle) =
      ∑ n ∈ J, ‖a n‖ ^ 2 := by
  let h := ContinuousMap.memLp (p := 2) haarAddCircle ℂ
    (supportedFourierPolynomial J a)
  have hc := fourierCoeff_congr_ae h.coeFn_toLp
  have hi :
      (∫ x : UnitAddCircle,
          ‖h.toLp (supportedFourierPolynomial J a) x‖ ^ 2 ∂haarAddCircle) =
        ∫ x : UnitAddCircle,
          ‖supportedFourierPolynomial J a x‖ ^ 2 ∂haarAddCircle := by
    apply integral_congr_ae
    filter_upwards [h.coeFn_toLp] with x hx
    rw [hx]
  have hp := tsum_sq_fourierCoeff (h.toLp (supportedFourierPolynomial J a))
  rw [hc, hi] at hp
  rw [tsum_eq_sum (s := J.image (fun n : ℕ => (n : ℤ))) (fun k hk => by
    rw [fourierCoeff_supported_zero J a hk]
    norm_num)] at hp
  rw [Finset.sum_image] at hp
  · calc
      (∫ x : UnitAddCircle,
          ‖supportedFourierPolynomial J a x‖ ^ 2 ∂haarAddCircle) =
          ∑ n ∈ J,
            ‖fourierCoeff (supportedFourierPolynomial J a) (n : ℤ)‖ ^ 2 := hp.symm
      _ = ∑ n ∈ J, ‖a n‖ ^ 2 := by
        apply Finset.sum_congr rfl
        intro n hn
        rw [fourierCoeff_supported_at J a hn]
  · intro n hn m hm hnm
    exact Int.ofNat_inj.mp hnm

private lemma coeff_double_finset_fourier_sum (J : Finset ℕ)
    (c : ℕ → ℕ → ℂ) (k : ℤ) :
    fourierCoeff
        (fun x : UnitAddCircle =>
          ∑ n ∈ J, ∑ u ∈ J, c n u * fourier ((n : ℤ) + (u : ℤ)) x) k =
      ∑ n ∈ J, ∑ u ∈ J,
        if k = (n : ℤ) + (u : ℤ) then c n u else 0 := by
  have houter :
      (fun x : UnitAddCircle =>
        ∑ n ∈ J, ∑ u ∈ J, c n u * fourier ((n : ℤ) + (u : ℤ)) x) =
        ∑ n ∈ J, (fun x : UnitAddCircle =>
          ∑ u ∈ J, c n u * fourier ((n : ℤ) + (u : ℤ)) x) := by
    funext x
    simp only [Finset.sum_apply]
  rw [houter, fourierCoeff.sum]
  simp only [Finset.sum_apply]
  · apply Finset.sum_congr rfl
    intro n hn
    exact coeff_finset_fourier_sum J (c n) (fun u => (n : ℤ) + (u : ℤ)) k
  · intro n hn
    exact integrable_finset_fourier_sum J (c n) (fun u => (n : ℤ) + (u : ℤ))

/-- The coefficient of the product polynomial is the literal pair-filtered
integer convolution. -/
theorem fourierCoeff_supported_product (J : Finset ℕ) (v w : ℕ → ℂ)
    (k : ℤ) :
    fourierCoeff
        (fun x : UnitAddCircle =>
          supportedFourierPolynomial J v x * supportedFourierPolynomial J w x) k =
      integerPairConvolution J v w k := by
  have hfun :
      (fun x : UnitAddCircle =>
        supportedFourierPolynomial J v x * supportedFourierPolynomial J w x) =
      (fun x : UnitAddCircle =>
        ∑ n ∈ J, ∑ u ∈ J,
          (v n * w u) * fourier ((n : ℤ) + (u : ℤ)) x) := by
    funext x
    rw [supportedFourierPolynomial_apply, supportedFourierPolynomial_apply]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro n hn
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u hu
    rw [fourier_add]
    ring
  rw [hfun]
  exact coeff_double_finset_fourier_sum J (fun n u => v n * w u) k

/-- Finite Bessel/Parseval transfer.  Only the declared carrier contributes,
and `targets` may be any finite set of integer frequencies. -/
theorem finite_supported_convolution_parseval_bound (J : Finset ℕ)
    (v w : ℕ → ℂ) (targets : Finset ℤ) (A : ℝ) (hA : 0 ≤ A)
    (hfourier : ∀ x : UnitAddCircle, ‖supportedFourierPolynomial J v x‖ ≤ A) :
    (∑ k ∈ targets, ‖integerPairConvolution J v w k‖ ^ 2) ≤
      A ^ 2 * ∑ n ∈ J, ‖w n‖ ^ 2 := by
  let F : C(UnitAddCircle, ℂ) :=
    supportedFourierPolynomial J v * supportedFourierPolynomial J w
  let h := ContinuousMap.memLp (p := 2) haarAddCircle ℂ F
  have hc := fourierCoeff_congr_ae h.coeFn_toLp
  have hi :
      (∫ x : UnitAddCircle, ‖h.toLp F x‖ ^ 2 ∂haarAddCircle) =
        ∫ x : UnitAddCircle, ‖F x‖ ^ 2 ∂haarAddCircle := by
    apply integral_congr_ae
    filter_upwards [h.coeFn_toLp] with x hx
    rw [hx]
  have hp := hasSum_sq_fourierCoeff (h.toLp F)
  rw [hc, hi] at hp
  have hbessel := sum_le_hasSum targets
    (fun k hk => sq_nonneg ‖fourierCoeff F k‖) hp
  have hFmem : MemLp (F : UnitAddCircle → ℂ) 2 haarAddCircle :=
    ContinuousMap.memLp (p := 2) haarAddCircle ℂ F
  have hWmem : MemLp
      (supportedFourierPolynomial J w : UnitAddCircle → ℂ) 2 haarAddCircle :=
    ContinuousMap.memLp (p := 2) haarAddCircle ℂ
      (supportedFourierPolynomial J w)
  have hpoint (x : UnitAddCircle) :
      ‖F x‖ ^ 2 ≤ A ^ 2 * ‖supportedFourierPolynomial J w x‖ ^ 2 := by
    have hsq : ‖supportedFourierPolynomial J v x‖ ^ 2 ≤ A ^ 2 := by
      nlinarith [norm_nonneg (supportedFourierPolynomial J v x), hfourier x]
    change ‖supportedFourierPolynomial J v x *
      supportedFourierPolynomial J w x‖ ^ 2 ≤ _
    rw [norm_mul]
    nlinarith [sq_nonneg ‖supportedFourierPolynomial J w x‖]
  calc
    _ = ∑ k ∈ targets, ‖fourierCoeff F k‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro k hk
      dsimp [F]
      change ‖integerPairConvolution J v w k‖ ^ 2 =
        ‖fourierCoeff (fun x : UnitAddCircle =>
          supportedFourierPolynomial J v x * supportedFourierPolynomial J w x) k‖ ^ 2
      rw [fourierCoeff_supported_product]
    _ ≤ ∫ x : UnitAddCircle, ‖F x‖ ^ 2 ∂haarAddCircle := hbessel
    _ ≤ ∫ x : UnitAddCircle,
        A ^ 2 * ‖supportedFourierPolynomial J w x‖ ^ 2 ∂haarAddCircle := by
      apply integral_mono hFmem.integrable_norm_pow'
        (hWmem.integrable_norm_pow'.const_mul (A ^ 2)) hpoint
    _ = A ^ 2 *
        (∫ x : UnitAddCircle,
          ‖supportedFourierPolynomial J w x‖ ^ 2 ∂haarAddCircle) := by
      rw [integral_const_mul]
    _ = A ^ 2 * ∑ n ∈ J, ‖w n‖ ^ 2 := by
      rw [integral_supportedFourierPolynomial_norm_sq]

/-- The squared V138 pointwise scale has the requested exact exponent. -/
theorem residual_scale_square (Cv R : ℝ) (B : ℕ) (hR : 0 ≤ R) :
    (Cv * (B : ℝ) * R^(-(1 : ℝ) / 3))^2 =
      Cv^2 * (B : ℝ)^2 * R^(-(2 : ℝ) / 3) := by
  rw [mul_pow, mul_pow, ← Real.rpow_mul_natCast hR]
  norm_num

/-- Literal application to the supported V138 principal residual.  The right
side deliberately retains the actual finite energy of `blockInput` plus the
supported principal companion; no estimate of that energy is asserted. -/
theorem principal_residual_convolution_parseval_bound
    (B : ℕ) (hB : 6 ≤ B) (R C : ℝ) (hR : 1 < R) (hC : 0 ≤ C)
    (hV : RealVaughanEstimate C)
    (hlower : Real.exp (Real.sqrt (Real.log (B : ℝ))) ≤ R)
    (hupper : R ≤ (B : ℝ)^((1 : ℝ) / 10000))
    (G : ℝ → ℝ) (M : ℝ) (hM : 0 ≤ M) (hG : ∀ u : ℝ, |G u| ≤ M)
    (hplateau : ∀ u : ℝ, 0 ≤ u → u ≤ 1 → G u = 1) :
    let Cv :=
      9 * ((1 + M) / 2 + 3 * Real.pi) +
        (8 * (48 : ℝ)^8 * C) * (1 + 2 * M) + (81 / 2) * M
    let companion := fun N : ℕ =>
      blockInput B N + supportedPrincipalModel B N R G
    (∑ k ∈ Finset.Icc (0 : ℤ) (2 * B : ℕ),
      ‖integerPairConvolution (blockCarrier B)
        (fun N => inputPrincipalResidual B N R hR G) companion k‖ ^ 2) ≤
      Cv^2 * (B : ℝ)^2 * R^(-(2 : ℝ) / 3) *
        ∑ N ∈ blockCarrier B, ‖companion N‖ ^ 2 := by
  dsimp only
  have hbase := finite_supported_convolution_parseval_bound
    (blockCarrier B) (fun N => inputPrincipalResidual B N R hR G)
    (fun N => blockInput B N + supportedPrincipalModel B N R G)
    (Finset.Icc (0 : ℤ) (2 * B : ℕ))
    ((9 * ((1 + M) / 2 + 3 * Real.pi) +
      8 * 48^8 * C * (1 + 2 * M) + 81 / 2 * M) *
      (B : ℝ) * R^(-(1 : ℝ) / 3)) (by positivity) (by
        intro x
        rw [supportedFourierPolynomial_apply]
        exact input_principal_fourier_bound B hB R C hR hC hV hlower hupper
          G M hM hG hplateau x)
  have hR0 : 0 ≤ R := le_trans (by norm_num) hR.le
  rw [residual_scale_square _ R B hR0] at hbase
  exact hbase

end GoldbachCircleMethodSupportedResidualParsevalV18190
