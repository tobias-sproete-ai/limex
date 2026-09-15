import GoldbachCircleMethodArithmeticProgressionInputMatchV1871
import GoldbachCircleMethodTwoScaleBesselBridgeV1834

/-! # V1.8.72: exact finite L2 identity for the existing exponential sum.
No distribution or uniform minor-arc estimate is supplied here.
-/
open scoped BigOperators ComplexConjugate
open MeasureTheory AddCircle
open GoldbachCircleMethodFourierIdentityV171
open GoldbachCircleMethodFiniteAbelAdapterV1863
open GoldbachPrimePowerDefectBoundV161
open GoldbachCircleMethodTwoScaleIntegralPartitionV1831
open GoldbachCircleMethodTwoScaleBesselBridgeV1834

namespace GoldbachCircleMethodFiniteFourierL2MinorMomentV1872

theorem exponentialSum_inner_self (M : ℕ) :
    inner ℂ (ContinuousMap.toLp 2 haarAddCircle ℂ (exponentialSum M.succ))
      (ContinuousMap.toLp 2 haarAddCircle ℂ (exponentialSum M.succ)) =
        ∑ n ∈ Finset.range M.succ, ((ArithmeticFunction.vonMangoldt n)^2 : ℝ) := by
  have hinj : Function.Injective (fun n : ℕ => (n : ℤ)) := by
    intro a b h; exact Int.ofNat_inj.mp h
  have horth := (orthonormal_fourier (T := (1 : ℝ))).comp
    (fun n : ℕ => (n : ℤ)) hinj
  have h := horth.inner_sum (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
    (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (Finset.range M.succ)
  simpa [exponentialSum, map_sum, map_smul, fourierLp, Function.comp_def,
    Complex.ofReal_pow, pow_two] using h

theorem exponentialSum_integral_norm_sq (M : ℕ) :
    (∫ x : UnitAddCircle, ‖exponentialSum M.succ x‖^2 ∂haarAddCircle) =
      ∑ n ∈ Finset.range M, (ArithmeticFunction.vonMangoldt (n+1))^2 := by
  have hint : Integrable
      (fun x : UnitAddCircle => exponentialSum M.succ x * conj (exponentialSum M.succ x))
      haarAddCircle := by
    simpa only [IntegrableOn, Measure.restrict_univ] using
      ContinuousOn.integrableOn_compact (μ := haarAddCircle) (K := Set.univ)
        isCompact_univ (by fun_prop)
  have h := congrArg Complex.re (exponentialSum_inner_self M)
  rw [ContinuousMap.inner_toLp] at h
  have hir := integral_re hint
  change (∫ x : UnitAddCircle,
    (exponentialSum M.succ x * conj (exponentialSum M.succ x)).re ∂haarAddCircle) =
      (∫ x : UnitAddCircle,
        exponentialSum M.succ x * conj (exponentialSum M.succ x) ∂haarAddCircle).re at hir
  rw [← hir] at h
  simp only [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq] at h
  convert h using 1
  simp [Finset.sum_range_succ', pow_two]

theorem exponentialSum_integral_norm_sq_le (M : ℕ) :
    (∫ x : UnitAddCircle, ‖exponentialSum M.succ x‖^2 ∂haarAddCircle) ≤
      (M : ℝ) * (Real.log (M : ℝ))^2 := by
  rw [exponentialSum_integral_norm_sq]
  calc
    _ ≤ ∑ _n ∈ Finset.range M, (Real.log (M : ℝ))^2 := by
      apply Finset.sum_le_sum
      intro n hn
      have hnM : n+1 ≤ M := by have := Finset.mem_range.mp hn; omega
      have hupper := vonMangoldt_le_log_nat_of_le hnM
      have hnonneg : 0 ≤ ArithmeticFunction.vonMangoldt (n+1) :=
        ArithmeticFunction.vonMangoldt_nonneg
      nlinarith
    _ = _ := by simp

theorem exponentialSum_norm_pow_integrable (M k : ℕ) :
    Integrable (fun x : UnitAddCircle => ‖exponentialSum M.succ x‖^k)
      haarAddCircle := by
  simpa only [IntegrableOn, Measure.restrict_univ] using
    ContinuousOn.integrableOn_compact (μ := haarAddCircle) (K := Set.univ)
      isCompact_univ (by fun_prop)

theorem minorFourthMoment_le_bound_mul_L2 (M P R₀ : ℕ) (A : ℝ) (hA : 0 ≤ A)
    (hMinor : ∀ x ∈ twoScaleMinorMask M P R₀, ‖exponentialSum M.succ x‖^2 ≤ A) :
    minorFourthMoment M P R₀ ≤
      A * (∫ x : UnitAddCircle, ‖exponentialSum M.succ x‖^2 ∂haarAddCircle) := by
  have h2 := exponentialSum_norm_pow_integrable M 2
  have h4 := exponentialSum_norm_pow_integrable M 4
  unfold minorFourthMoment
  calc
    _ ≤ ∫ x in twoScaleMinorMask M P R₀,
        A * ‖exponentialSum M.succ x‖^2 ∂haarAddCircle := by
      apply setIntegral_mono_on h4.integrableOn (h2.const_mul A).integrableOn
        (twoScaleMinorMask_measurable M P R₀)
      intro x hx
      have hb := mul_le_mul_of_nonneg_right (hMinor x hx)
        (sq_nonneg ‖exponentialSum M.succ x‖)
      nlinarith
    _ = A * (∫ x in twoScaleMinorMask M P R₀,
        ‖exponentialSum M.succ x‖^2 ∂haarAddCircle) := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (setIntegral_le_integral h2 (Filter.Eventually.of_forall (fun x => sq_nonneg _))) hA

theorem minorFourthMoment_le_bound_mul_weight_square_sum
    (M P R₀ : ℕ) (A : ℝ) (hA : 0 ≤ A)
    (hMinor : ∀ x ∈ twoScaleMinorMask M P R₀, ‖exponentialSum M.succ x‖^2 ≤ A) :
    minorFourthMoment M P R₀ ≤
      A * (∑ n ∈ Finset.range M, (ArithmeticFunction.vonMangoldt (n+1))^2) := by
  simpa only [exponentialSum_integral_norm_sq] using
    minorFourthMoment_le_bound_mul_L2 M P R₀ A hA hMinor

theorem minorFourthMoment_le_bound_mul_M_log_sq
    (M P R₀ : ℕ) (A : ℝ) (hA : 0 ≤ A)
    (hMinor : ∀ x ∈ twoScaleMinorMask M P R₀, ‖exponentialSum M.succ x‖^2 ≤ A) :
    minorFourthMoment M P R₀ ≤ A * ((M : ℝ) * (Real.log (M : ℝ))^2) :=
  (minorFourthMoment_le_bound_mul_L2 M P R₀ A hA hMinor).trans
    (mul_le_mul_of_nonneg_left (exponentialSum_integral_norm_sq_le M) hA)

end GoldbachCircleMethodFiniteFourierL2MinorMomentV1872
