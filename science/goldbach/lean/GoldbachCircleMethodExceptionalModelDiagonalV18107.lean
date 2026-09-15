import GoldbachCircleMethodPrimitiveRamanujanProjectionV18103

/-! Finite primitive quadratic-character sign audit.
The inverse-equals-self hypothesis is explicit. No exceptional zero is postulated.
No analytic model reserve follows from this finite identity alone. -/
set_option autoImplicit false
open scoped BigOperators Classical
open GoldbachCircleMethodFiniteResiduePrefixV1866

namespace GoldbachCircleMethodExceptionalModelDiagonalV18107
variable (q : ℕ) [NeZero q]

theorem quadratic_value_square (χ : DirichletCharacter ℂ q) (hInv : χ⁻¹ = χ)
    (a : ZMod q) :
    χ a * χ a = if IsUnit a then 1 else 0 := by
  by_cases ha : IsUnit a
  · rw [if_pos ha]
    have h := congrArg (fun ψ : DirichletCharacter ℂ q => ψ a) (MulChar.inv_mul χ)
    simpa only [MulChar.mul_apply, hInv, MulChar.one_apply ha] using h
  · rw [if_neg ha, MulChar.map_nonunit _ ha, zero_mul]

theorem quadratic_primitive_gauss_square (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hInv : χ⁻¹ = χ) :
    gaussSum χ ZMod.stdAddChar * gaussSum χ ZMod.stdAddChar =
      χ (-1) * (q : ℂ) := by
  let τ := gaussSum χ ZMod.stdAddChar
  have hminus : χ (-1) * χ (-1) = 1 := by
    rw [← map_mul]
    simp
  have hf : ZMod.dft (χ : ZMod q → ℂ) =
      (fun a => (χ (-1) * τ) * χ a) := by
    funext a
    rw [hχ.fourierTransform_eq_inv_mul_gaussSum, hInv,
      ← neg_one_mul a, map_mul]
    ring
  have hd := congrFun (ZMod.dft_const_mul (χ (-1) * τ) (χ : ZMod q → ℂ)) 1
  rw [← hf] at hd
  change ZMod.dft (ZMod.dft (χ : ZMod q → ℂ)) 1 =
    (χ (-1) * τ) * ZMod.dft (χ : ZMod q → ℂ) 1 at hd
  rw [hχ.fourierTransform_eq_inv_mul_gaussSum, hInv] at hd
  have hi := congrFun (ZMod.dft_dft (χ : ZMod q → ℂ)) 1
  change ZMod.dft (ZMod.dft (χ : ZMod q → ℂ)) 1 = (q : ℂ) * χ (-1) at hi
  calc
    τ * τ = (χ (-1) * χ (-1)) * (τ * τ) := by rw [hminus, one_mul]
    _ = (χ (-1) * τ) * (χ (-1) * τ) := by ring
    _ = ZMod.dft (ZMod.dft (χ : ZMod q → ℂ)) 1 := hd.symm
    _ = χ (-1) * (q : ℂ) := by rw [hi, mul_comm]

theorem primitive_quadratic_self_convolution (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hInv : χ⁻¹ = χ) (n : ZMod q) :
    (∑ u : ZMod q, χ u * χ (n-u)) = χ (-1) * unitCharacterSum q n := by
  let τ := gaussSum χ ZMod.stdAddChar
  have hminus : χ (-1) * χ (-1) = 1 := by rw [← map_mul]; simp
  have hm : χ (-1) ≠ 0 := by
    intro h
    rw [h, zero_mul] at hminus
    exact zero_ne_one hminus
  have hτ : τ ≠ 0 := by
    intro h
    have hs := quadratic_primitive_gauss_square q χ hχ hInv
    change τ * τ = χ (-1) * (q : ℂ) at hs
    rw [h, zero_mul] at hs
    exact (mul_ne_zero hm (NeZero.ne (q : ℂ))) hs.symm
  have hshift (x : ZMod q) :
      (∑ a : ZMod q, χ a * ZMod.stdAddChar (x*a)) = χ x * τ := by
    simpa only [τ, gaussSum, AddChar.mulShift_apply, hInv] using
      gaussSum_mulShift_of_isPrimitive ZMod.stdAddChar hχ x
  apply mul_left_cancel₀ hτ
  calc
    τ * (∑ u : ZMod q, χ u * χ (n-u)) =
        ∑ u : ZMod q, χ u * (∑ a : ZMod q,
          χ a * ZMod.stdAddChar ((n-u)*a)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro u _
      rw [hshift]
      ring
    _ = ∑ a : ZMod q, ZMod.stdAddChar (n*a) * χ a *
        ZMod.dft (χ : ZMod q → ℂ) a := by
      simp only [ZMod.dft_apply, smul_eq_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro u _
      simp only [sub_eq_add_neg, add_mul, neg_mul, AddChar.map_add_eq_mul]
      ring
    _ = τ * (χ (-1) * unitCharacterSum q n) := by
      simp only [unitCharacterSum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      rw [hχ.fourierTransform_eq_inv_mul_gaussSum, hInv,
        ← neg_one_mul a, map_mul χ (-1) a]
      have hs := quadratic_value_square q χ hInv a
      by_cases ha : IsUnit a
      · rw [if_pos ha] at hs ⊢
        change ZMod.stdAddChar (n*a) * χ a * ((χ (-1) * χ a) * τ) =
          τ * (χ (-1) * ZMod.stdAddChar (n*a))
        calc
          _ = τ * (χ (-1) * ZMod.stdAddChar (n*a)) * (χ a * χ a) := by ring
          _ = _ := by rw [hs, mul_one]
      · rw [if_neg ha, MulChar.map_nonunit _ ha]
        ring

end GoldbachCircleMethodExceptionalModelDiagonalV18107
