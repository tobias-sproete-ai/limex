import GoldbachCircleMethodPrimitiveLiftSeparationV18578
import GoldbachCircleMethodFiniteRamanujanEnergyV18131

/-!
# Goldbach V1.8.579: same-denominator Hermitian Plancherel

An exact finite Plancherel identity for the DFT convention used by the
Goldbach circle-method chain.  It moves a complete-period Hermitian spatial
correlation to the common frequency denominator without estimates.  No
orthogonality of twisted Ramanujan coefficients is asserted here.
-/

set_option autoImplicit false

open scoped BigOperators Classical ComplexConjugate

namespace GoldbachCircleMethodSameDenominatorHermitianPlancherelV18579

open GoldbachCircleMethodFiniteRamanujanEnergyV18131

/-- Conjugated Fourier inversion in the exact sign convention needed below. -/
theorem star_dft_inversion_sum
    {d : ℕ} [NeZero d] (f : ZMod d → ℂ) (x : ZMod d) :
    (∑ a : ZMod d,
      star (ZMod.dft f a) * ZMod.stdAddChar (-(x * a))) =
      (d : ℂ) * star (f x) := by
  have hs := congrArg star (congrFun (ZMod.dft_dft f) (-x))
  change
    star (∑ a : ZMod d,
      ZMod.stdAddChar (-(a * (-x))) * ZMod.dft f a) =
      star ((d : ℂ) * f (-(-x))) at hs
  simp only [star_sum, star_mul, standard_character_conjugate, neg_neg] at hs
  calc
    (∑ a : ZMod d,
        star (ZMod.dft f a) * ZMod.stdAddChar (-(x * a))) =
        ∑ a : ZMod d,
          star (ZMod.dft f a) * ZMod.stdAddChar (a * -x) := by
            apply Finset.sum_congr rfl
            intro a _ha
            congr 2
            ring
    _ = star (f x) * star (d : ℂ) := hs
    _ = (d : ℂ) * star (f x) := by simp [mul_comm]

/-- Exact unnormalised Hermitian Plancherel identity on one finite residue
ring.  No support or regularity assumption is required. -/
theorem dft_hermitian_plancherel
    {d : ℕ} [NeZero d] (f g : ZMod d → ℂ) :
    (∑ a : ZMod d, star (ZMod.dft f a) * ZMod.dft g a) =
      (d : ℂ) * ∑ x : ZMod d, star (f x) * g x := by
  have hg (a : ZMod d) :
      ZMod.dft g a =
        ∑ x : ZMod d, ZMod.stdAddChar (-(x * a)) * g x := by
    rfl
  simp_rw [hg, Finset.mul_sum]
  simp_rw [show ∀ a x : ZMod d,
    star (ZMod.dft f a) *
        (ZMod.stdAddChar (-(x * a)) * g x) =
      (star (ZMod.dft f a) * ZMod.stdAddChar (-(x * a))) * g x by
        intro a x
        ring]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul]
  simp_rw [star_dft_inversion_sum f]
  apply Finset.sum_congr rfl
  intro x _hx
  ring

end GoldbachCircleMethodSameDenominatorHermitianPlancherelV18579
