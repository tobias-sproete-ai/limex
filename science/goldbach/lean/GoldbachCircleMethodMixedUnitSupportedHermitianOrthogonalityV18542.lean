import GoldbachCircleMethodCrossConductorBlockPairReindexV18541
import GoldbachCircleMethodActualTwistSelfConvolutionV18211
import GoldbachCircleMethodFiniteRamanujanEnergyV18131

/-!
# Goldbach V1.8.542: mixed unit-supported Hermitian orthogonality

Distinct reduced denominators are orthogonal not only under translated
convolution, but also under the Hermitian inner product used by the exact
cross-conductor residual from V1.8.541.  This module first closes the literal
additive-character atom.  No incomplete-interval cancellation or global
Goldbach conclusion is asserted.
-/

set_option autoImplicit false

open scoped BigOperators Classical ComplexConjugate

namespace GoldbachCircleMethodMixedUnitSupportedHermitianOrthogonalityV18542

open GoldbachCircleMethodMixedRamanujanOrthogonalityV18203
open GoldbachCircleMethodFiniteRamanujanEnergyV18131
open GoldbachCircleMethodActualTwistedCompleteProjectionV18209
open GoldbachCircleMethodPrimitiveRamanujanProjectionV18103
open GoldbachCircleMethodPrimitiveTwistedRamanujanSupportV18208

/-- Complex conjugation of a lifted standard character equals evaluation at
the additive inverse.  This is the exact bridge from convolutional to
Hermitian orthogonality. -/
theorem star_liftedUnitCharacter {K q : ℕ} [NeZero K] [NeZero q]
    (hq : q ∣ K) (a : (ZMod q)ˣ) (x : ZMod K) :
    star (liftedUnitCharacter hq a x) = liftedUnitCharacter hq a (-x) := by
  simp only [liftedUnitCharacter_apply, map_neg]
  rw [standard_character_conjugate]
  congr 1
  ring

/-- Unit additive characters of distinct exact reduced denominators are
orthogonal for the complete-period Hermitian inner product. -/
theorem liftedUnitCharacter_inner_zero {K q l : ℕ}
    [NeZero K] [NeZero q] [NeZero l]
    (hq : q ∣ K) (hl : l ∣ K) (a : (ZMod q)ˣ) (b : (ZMod l)ˣ)
    (hql : q ≠ l) :
    (∑ x : ZMod K, star (liftedUnitCharacter hq a x) *
      liftedUnitCharacter hl b x) = 0 := by
  simpa only [star_liftedUnitCharacter hq a] using
    liftedUnitCharacter_orthogonality hq hl a b hql

/-- Arbitrary functions whose DFTs are supported on unit frequencies at
distinct exact denominators have zero complete-period Hermitian inner product.
This is the functional statement needed by cross-conductor energy expansions. -/
theorem two_unit_supported_mixed_inner_zero {K q l : ℕ}
    [NeZero K] [NeZero q] [NeZero l]
    (hq : q ∣ K) (hl : l ∣ K) (hql : q ≠ l)
    (f : ZMod q → ℂ) (g : ZMod l → ℂ)
    (hf : ∀ a, ¬ IsUnit a → ZMod.dft f a = 0)
    (hg : ∀ b, ¬ IsUnit b → ZMod.dft g b = 0) :
    (∑ x : ZMod K,
      star (f (ZMod.castHom hq (ZMod q) x)) *
        g (ZMod.castHom hl (ZMod l) x)) = 0 := by
  have hscale : ((q : ℂ) * (l : ℂ)) *
      (∑ x : ZMod K,
        star (f (ZMod.castHom hq (ZMod q) x)) *
          g (ZMod.castHom hl (ZMod l) x)) = 0 := by
    rw [Finset.mul_sum]
    simp_rw [show ∀ x : ZMod K,
      ((q : ℂ) * (l : ℂ)) *
          (star (f (ZMod.castHom hq (ZMod q) x)) *
            g (ZMod.castHom hl (ZMod l) x)) =
        star ((q : ℂ) * f (ZMod.castHom hq (ZMod q) x)) *
          ((l : ℂ) * g (ZMod.castHom hl (ZMod l) x)) by
      intro x
      simp only [Complex.star_def, map_mul, map_natCast]
      ring]
    simp_rw [← unit_supported_fourier_expansion f hf,
      ← unit_supported_fourier_expansion g hg]
    simp_rw [star_sum, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro a _
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro b _
    by_cases ha : IsUnit a
    · by_cases hb : IsUnit b
      · simp only [ha, hb, if_true, star_mul]
        have hz := liftedUnitCharacter_inner_zero hq hl ha.unit hb.unit hql
        have hw := congrArg
          (fun z : ℂ => z * (star (ZMod.dft f a) * ZMod.dft g b)) hz
        simp only [liftedUnitCharacter_apply, IsUnit.unit_spec,
          Finset.sum_mul, zero_mul] at hw
        simpa only [mul_comm, mul_left_comm, mul_assoc] using hw
      · simp [hb]
    · simp [ha]
  exact (mul_eq_zero.mp hscale).resolve_left
    (mul_ne_zero (NeZero.ne (q : ℂ)) (NeZero.ne (l : ℂ)))

/-- Primitive twisted Ramanujan atoms with different ambient denominators
have zero Hermitian correlation on every common complete period.  Equal
conductors are not required; the exact collision condition is `r*l = s*k`. -/
theorem twistedRamanujan_mixed_inner_zero
    {K r s l k : ℕ}
    [NeZero K] [NeZero r] [NeZero s] [NeZero l] [NeZero k]
    (hrl : r * l ∣ K) (hsk : s * k ∣ K)
    (hrlcop : Nat.Coprime r l) (hskcop : Nat.Coprime s k)
    (hden : r * l ≠ s * k)
    (χ : DirichletCharacter ℂ r) (ψ : DirichletCharacter ℂ s)
    (hχ : χ.IsPrimitive) (hψ : ψ.IsPrimitive) :
    (∑ x : ZMod K,
      star (twistedRamanujan r l χ
        (ZMod.castHom hrl (ZMod (r * l)) x)) *
      twistedRamanujan s k ψ
        (ZMod.castHom hsk (ZMod (s * k)) x)) = 0 := by
  let _ : NeZero (r * l) :=
    ⟨Nat.mul_ne_zero (NeZero.ne r) (NeZero.ne l)⟩
  let _ : NeZero (s * k) :=
    ⟨Nat.mul_ne_zero (NeZero.ne s) (NeZero.ne k)⟩
  exact two_unit_supported_mixed_inner_zero hrl hsk hden
    (twistedRamanujan r l χ) (twistedRamanujan s k ψ)
    (twistedRamanujan_dft_nonunit_zero r l hrlcop χ hχ)
    (twistedRamanujan_dft_nonunit_zero s k hskcop ψ hψ)

end GoldbachCircleMethodMixedUnitSupportedHermitianOrthogonalityV18542
