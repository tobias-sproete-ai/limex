import GoldbachCircleMethodDiscreteArcModelReserveV1855

/-! # V1.8.56: actual rational phases and complex-to-real coefficient binding.
The local model integrals may be complex. Their coefficient is proved real;
this justifies the real model in V55 without multiplying real parts blindly.
The closed-ball union and the von-Mangoldt approximation are not identified here.
-/
open scoped BigOperators
open GoldbachCircleMethodRamanujanCoprimeBindingV1840
open GoldbachCircleMethodFullSquarefreeCarrierV1846
open GoldbachCircleMethodFullSquarefreeCoefficientV1847
open GoldbachCircleMethodSignedFullPrefixV1850
open GoldbachCircleMethodDiscreteArcTailV1854
open GoldbachCircleMethodDiscreteArcModelReserveV1855

namespace GoldbachCircleMethodComplexArcModelBindingV1856

attribute [local instance] Classical.propDecidable

theorem rational_fourier_phase_eq_stdAddChar (q : ℕ) [NeZero q]
    (a : ZMod q) (n : ℤ) :
    fourier n (((a.val : ℝ)/(q : ℝ) : ℝ) : UnitAddCircle) =
      ZMod.stdAddChar (a*(n : ZMod q)) := by
  have harg : a*(n : ZMod q) = (((a.val : ℤ)*n : ℤ) : ZMod q) := by simp
  rw [harg, ZMod.stdAddChar_coe, fourier_coe_apply]
  simp only [Complex.ofReal_div, Complex.ofReal_natCast, Complex.ofReal_one, div_one,
    Int.cast_mul, Int.cast_natCast]
  congr 1
  ring

theorem rational_phase_sum_eq_integerFourierRamanujan (q : ℕ) [NeZero q] (n : ℤ) :
    (∑ a : ZMod q, if IsUnit a then
      fourier n (((a.val : ℝ)/(q : ℝ) : ℝ) : UnitAddCircle) else 0) =
        integerFourierRamanujan q n (NeZero.ne q) := by
  classical
  simp only [integerFourierRamanujan, rational_fourier_phase_eq_stdAddChar]

noncomputable def complexMajorCoefficient (N q : ℕ) : ℂ :=
  if hq : q = 0 then 0 else
    (((ArithmeticFunction.moebius q : ℤ)^2 : ℤ) : ℂ) *
      integerFourierRamanujan q (-(N : ℤ)) hq / (Nat.totient q : ℂ)^2

theorem complexMajorCoefficient_eq_ofReal_signed (N q : ℕ) :
    complexMajorCoefficient N q = (signedMajorCoefficient N q : ℂ) := by
  by_cases hq0 : q = 0
  · simp [complexMajorCoefficient, signedMajorCoefficient, hq0]
  by_cases hq : Squarefree q
  · have hp := canonical_pair_mem (N := N) (mem_fullSquarefreePrefix.mpr ⟨le_rfl, hq⟩)
    have heq := finiteFourierRamanujan_pair_eq_totient_mul_moebius hp (R := q) le_rfl
    have heq' : finiteFourierRamanujan q N hq0 =
        (Nat.totient (Nat.gcd q N) : ℂ) *
          ((ArithmeticFunction.moebius (q / Nat.gcd q N) : ℤ) : ℂ) := by
      simpa only [canonical_product] using heq
    have hreal : integerFourierRamanujan q (-(N : ℤ)) hq0 =
        (((Nat.totient (Nat.gcd q N) : ℝ) *
          ((ArithmeticFunction.moebius (q / Nat.gcd q N) : ℤ) : ℝ) : ℝ) : ℂ) := by
      rw [integerFourierRamanujan_neg_natCast, heq']
      push_cast
      rfl
    simp [complexMajorCoefficient, signedMajorCoefficient, hq0, hreal]
  · simp [complexMajorCoefficient, signedMajorCoefficient, hq0,
      ArithmeticFunction.moebius_eq_zero_of_not_squarefree hq]

theorem coefficient_mul_real_part (N q : ℕ) (J : ℂ) :
    (complexMajorCoefficient N q * J).re = signedMajorCoefficient N q * J.re := by
  rw [complexMajorCoefficient_eq_ofReal_signed]
  simp

noncomputable def complexDiscreteArcMainModel (M N R : ℕ) (P : ℝ) : ℂ :=
  ∑ q ∈ Finset.Icc 1 R, complexMajorCoefficient N q *
    localDiscreteMainIntegral M N (P/((q : ℝ)*(M : ℝ)))

theorem complexDiscreteArcMainModel_re (M N R : ℕ) (P : ℝ) :
    (complexDiscreteArcMainModel M N R P).re = discreteArcMainModel M N R P := by
  simp only [complexDiscreteArcMainModel, discreteArcMainModel, Complex.re_sum,
    coefficient_mul_real_part]

end GoldbachCircleMethodComplexArcModelBindingV1856
