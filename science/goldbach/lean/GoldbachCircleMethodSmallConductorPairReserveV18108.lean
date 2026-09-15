import GoldbachCircleMethodPrimitiveRamanujanProjectionV18103

/-! Exact finite unit-pair marginal for an actual primitive character.
No zero gap, Euler product, interval estimate or Goldbach claim is added here. -/
set_option autoImplicit false
open scoped BigOperators Classical
open GoldbachCircleMethodFiniteResiduePrefixV1866
open GoldbachCircleMethodGeneralCoprimeCharacterV1868
open GoldbachCircleMethodPrimitiveRamanujanProjectionV18103

namespace GoldbachCircleMethodSmallConductorPairReserveV18108
variable (q : ℕ) [NeZero q]

theorem inverse_fourier_sum (f : ZMod q → ℂ) (x : ZMod q) :
    (∑ a : ZMod q, ZMod.stdAddChar (x*a) * ZMod.dft f a) =
      (q : ℂ) * f x := by
  have h := congrFun (ZMod.dft_dft f) (-x)
  simpa only [ZMod.dft_apply, mul_neg, neg_neg, smul_eq_mul, mul_comm x] using h

theorem cyclic_convolution_fourier (f g : ZMod q → ℂ) (n : ZMod q) :
    (q : ℂ) * (∑ u : ZMod q, f (n-u) * g u) =
      ∑ a : ZMod q, ZMod.stdAddChar (n*a) * ZMod.dft f a * ZMod.dft g a := by
  calc
    _ = ∑ u : ZMod q, g u *
        (∑ a : ZMod q, ZMod.stdAddChar ((n-u)*a) * ZMod.dft f a) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro u _
      rw [inverse_fourier_sum]
      ring
    _ = _ := by
      simp only [ZMod.dft_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro v _
      apply Finset.sum_congr rfl
      intro u _
      simp only [sub_eq_add_neg, add_mul, neg_mul, AddChar.map_add_eq_mul]
      ring

noncomputable def unitIndicator (a : ZMod q) : ℂ := if IsUnit a then 1 else 0

theorem unit_indicator_dft (a : ZMod q) :
    ZMod.dft (unitIndicator q) a = unitCharacterSum q (-a) := by
  simp only [ZMod.dft_apply, unitIndicator, smul_eq_mul, unitCharacterSum]
  apply Finset.sum_congr rfl
  intro u _
  by_cases hu : IsUnit u
  · simp only [hu, if_true, mul_one, neg_mul]
    congr 1
    ring
  · simp only [hu, if_false, mul_zero]

theorem primitive_unit_pair_sum (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (n : ZMod q) :
    (∑ u : ZMod q, χ u * unitIndicator q (n-u)) =
      ((ArithmeticFunction.moebius q : ℤ) : ℂ) * χ n := by
  let μ : ℂ := ((ArithmeticFunction.moebius q : ℤ) : ℂ)
  have h := cyclic_convolution_fourier q (unitIndicator q) (χ : ZMod q → ℂ) n
  have heq :
      (∑ a : ZMod q, ZMod.stdAddChar (n*a) *
        ZMod.dft (unitIndicator q) a * ZMod.dft (χ : ZMod q → ℂ) a) =
      μ * ((q : ℂ) * χ n) := by
    calc
      _ = ∑ a : ZMod q, μ * (ZMod.stdAddChar (n*a) *
          ZMod.dft (χ : ZMod q → ℂ) a) := by
        apply Finset.sum_congr rfl
        intro a _
        by_cases ha : IsUnit a
        · rw [unit_indicator_dft,
            unitCharacterSum_eq_moebius q (-a) (by simpa using ha)]
          ring
        · rw [dft_nonunit_zero q χ hχ a ha]
          ring
      _ = _ := by rw [← Finset.mul_sum, inverse_fourier_sum]
  rw [heq] at h
  have hc : (q : ℂ) * (∑ u : ZMod q, unitIndicator q (n-u) * χ u) =
      (q : ℂ) * (μ * χ n) := by
    calc
      _ = μ * ((q : ℂ) * χ n) := h
      _ = _ := by ring
  have hh := mul_left_cancel₀ (NeZero.ne (q : ℂ)) hc
  simpa only [mul_comm (unitIndicator q _) (χ _)] using hh

end GoldbachCircleMethodSmallConductorPairReserveV18108
