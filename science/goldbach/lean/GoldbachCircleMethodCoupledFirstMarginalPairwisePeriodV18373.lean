import GoldbachCircleMethodCanonicalFirstMarginalTwoBranchBoundV18372

/-!
# Goldbach V1.8.373: coupled first marginal on a pairwise period

V1.8.372 controls the naked first character marginal.  The source operator,
however, multiplies that marginal by a Ramanujan factor at a coprime companion
level.  This module therefore tests the actual mixed product over the pairwise
period `r * l`, without introducing a common LCM over all levels.

For an odd active conductor `r`, multiplication by two permutes `ZMod r`.
CRT then factors the complete mixed target sum into a character sum modulo `r`
and a Ramanujan sum modulo `l`; the first factor is zero for every nontrivial
character.  No incomplete-interval estimate or aggregation over companion
levels is asserted here.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodCoupledFirstMarginalPairwisePeriodV18373

open GoldbachCircleMethodFiniteResiduePrefixV1866
open GoldbachCircleMethodEvenTargetWeightedCharacterAverageV18366

variable (r l : ℕ) [NeZero r] [NeZero l]

local instance productNeZero : NeZero (r * l) :=
  ⟨Nat.mul_ne_zero (NeZero.ne r) (NeZero.ne l)⟩

/-- CRT factors a product of two actual residue functions over the pairwise
period.  This is an exact finite identity; no analytic estimate is used. -/
theorem crt_product_sum (hcop : Nat.Coprime r l)
    (f : ZMod r → ℂ) (g : ZMod l → ℂ) :
    (∑ x : ZMod (r * l),
      f (ZMod.castHom (Nat.dvd_mul_right r l) (ZMod r) x) *
        g (ZMod.castHom (Nat.dvd_mul_left l r) (ZMod l) x)) =
      (∑ a : ZMod r, f a) * (∑ b : ZMod l, g b) := by
  let e := (ZMod.chineseRemainder hcop).symm.toEquiv
  rw [← e.sum_comp]
  have hc (x : ZMod r × ZMod l) :
      (ZMod.castHom (Nat.dvd_mul_right r l) (ZMod r) (e x),
       ZMod.castHom (Nat.dvd_mul_left l r) (ZMod l) (e x)) = x := by
    have h := (ZMod.chineseRemainder hcop).apply_symm_apply x
    change (ZMod.cast (e x) : ZMod r × ZMod l) = x at h
    apply Prod.ext
    · simpa only [ZMod.castHom_apply, Prod.fst_zmod_cast] using congrArg Prod.fst h
    · simpa only [ZMod.castHom_apply, Prod.snd_zmod_cast] using congrArg Prod.snd h
  have ht : ∀ x : ZMod r × ZMod l,
      f (ZMod.castHom (Nat.dvd_mul_right r l) (ZMod r) (e x)) *
          g (ZMod.castHom (Nat.dvd_mul_left l r) (ZMod l) (e x)) =
        f x.1 * g x.2 := by
    intro x
    have h1 := congrArg Prod.fst (hc x)
    have h2 := congrArg Prod.snd (hc x)
    change ZMod.castHom (Nat.dvd_mul_right r l) (ZMod r) (e x) = x.1 at h1
    change ZMod.castHom (Nat.dvd_mul_left l r) (ZMod l) (e x) = x.2 at h2
    rw [h1, h2]
  simp_rw [ht]
  rw [Fintype.sum_prod_type, Fintype.sum_mul_sum]

/-- If the first residue factor has zero complete sum, then its product with
any coprime companion factor cancels over the pairwise period. -/
theorem crt_product_sum_eq_zero_of_left
    (hcop : Nat.Coprime r l)
    (f : ZMod r → ℂ) (g : ZMod l → ℂ)
    (hf : ∑ a : ZMod r, f a = 0) :
    (∑ x : ZMod (r * l),
      f (ZMod.castHom (Nat.dvd_mul_right r l) (ZMod r) x) *
        g (ZMod.castHom (Nat.dvd_mul_left l r) (ZMod l) x)) = 0 := by
  rw [crt_product_sum r l hcop, hf, zero_mul]

/-- Source-matched complete-period cancellation for the linear character times
Ramanujan channel along consecutive even targets.  Coprimality of `2` and the
active conductor is the exact odd-conductor gate. -/
theorem even_target_character_ramanujan_complete_period_eq_zero
    (hcop : Nat.Coprime r l)
    (chi : DirichletCharacter ℂ r) (hne : chi ≠ 1)
    (A : ℕ) (h2 : Nat.Coprime 2 r) :
    (∑ x : ZMod (r * l),
      (((ArithmeticFunction.moebius r : ℤ) : ℂ) *
          chi ((A : ZMod r) + ((2 : ℕ) : ZMod r) *
            ZMod.castHom (Nat.dvd_mul_right r l) (ZMod r) x)) *
        unitCharacterSum l
          ((A : ZMod l) + ((2 : ℕ) : ZMod l) *
            ZMod.castHom (Nat.dvd_mul_left l r) (ZMod l) x)) = 0 := by
  let u : (ZMod r)ˣ := ZMod.unitOfCoprime 2 h2
  apply crt_product_sum_eq_zero_of_left r l hcop
      (fun a : ZMod r =>
        ((ArithmeticFunction.moebius r : ℤ) : ℂ) *
          chi ((A : ZMod r) + ((2 : ℕ) : ZMod r) * a))
      (fun b : ZMod l =>
        unitCharacterSum l ((A : ZMod l) + ((2 : ℕ) : ZMod l) * b))
  simpa only [u, ZMod.coe_unitOfCoprime] using
    affine_first_marginal_sum_eq_zero r chi hne (A : ZMod r) u

end GoldbachCircleMethodCoupledFirstMarginalPairwisePeriodV18373
