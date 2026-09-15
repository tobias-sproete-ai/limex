import GoldbachCircleMethodGeneralCoprimeCharacterV1868
import Mathlib.Analysis.Fourier.ZMod

/-! Exact primitive-character projection on the existing Ramanujan kernel.
This finite normalization lemma does not claim the full conductor regrouping
or any analytic estimate for primes. -/
set_option autoImplicit false
open scoped BigOperators Classical
open GoldbachCircleMethodFiniteResiduePrefixV1866

namespace GoldbachCircleMethodPrimitiveRamanujanProjectionV18103

variable (q : ℕ) [NeZero q]

theorem dft_nonunit_zero (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (a : ZMod q) (ha : ¬ IsUnit a) :
    ZMod.dft (χ : ZMod q → ℂ) a = 0 := by
  rw [hχ.fourierTransform_eq_inv_mul_gaussSum]
  have hneg : ¬ IsUnit (-a) := by simpa using ha
  rw [MulChar.map_nonunit _ hneg, zero_mul]

theorem ramanujan_convolution_dft (f : ZMod q → ℂ) (n : ZMod q) :
    (∑ u : ZMod q, unitCharacterSum q (n-u) * f u) =
      ∑ a : ZMod q, if IsUnit a then
        ZMod.stdAddChar (n*a) * ZMod.dft f a else 0 := by
  simp only [unitCharacterSum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : IsUnit a
  · simp only [ha, if_true, ZMod.dft_apply, smul_eq_mul,
      sub_eq_add_neg, add_mul, neg_mul, AddChar.map_add_eq_mul,
      Finset.mul_sum, mul_assoc]
  · simp only [ha, if_false, zero_mul, Finset.sum_const_zero]

theorem primitive_ramanujan_convolution (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (n : ZMod q) :
    (∑ u : ZMod q, unitCharacterSum q (n-u) * χ u) =
      (q : ℂ) * χ n := by
  rw [ramanujan_convolution_dft]
  have hdrop :
      (∑ a : ZMod q, if IsUnit a then
          ZMod.stdAddChar (n*a) * ZMod.dft (χ : ZMod q → ℂ) a else 0) =
      ∑ a : ZMod q, ZMod.stdAddChar (n*a) * ZMod.dft (χ : ZMod q → ℂ) a := by
    apply Finset.sum_congr rfl
    intro a _
    by_cases ha : IsUnit a
    · simp only [ha, if_true]
    · simp only [ha, if_false, dft_nonunit_zero q χ hχ a ha, mul_zero]
  rw [hdrop]
  have hi := congrFun (ZMod.dft_dft (χ : ZMod q → ℂ)) (-n)
  simpa only [ZMod.dft_apply, mul_neg, neg_neg, smul_eq_mul, mul_comm n] using hi

theorem primitive_normalized_projection (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (n : ZMod q) :
    (∑ u : ZMod q, unitCharacterSum q (n-u) * χ u) / (q : ℂ) = χ n := by
  rw [primitive_ramanujan_convolution q χ hχ n]
  exact mul_div_cancel_left₀ (χ n) (NeZero.ne (q : ℂ))

end GoldbachCircleMethodPrimitiveRamanujanProjectionV18103
