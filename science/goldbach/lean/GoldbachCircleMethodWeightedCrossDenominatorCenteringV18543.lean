import GoldbachCircleMethodMixedUnitSupportedHermitianOrthogonalityV18542

/-!
# Goldbach V1.8.543: weighted cross-denominator centering

The full-period orthogonality from V1.8.542 removes exactly the constant part
of an arbitrary target-dependent weight.  The centered fluctuation remains
literal.  This records the precise interface gap between bare Fourier-atom
orthogonality and the target-varying primitive-source weights in V1.8.541.
No smallness of that fluctuation is asserted.
-/

set_option autoImplicit false

open scoped BigOperators Classical ComplexConjugate

namespace GoldbachCircleMethodWeightedCrossDenominatorCenteringV18543

open GoldbachCircleMethodMixedUnitSupportedHermitianOrthogonalityV18542
open GoldbachCircleMethodPrimitiveRamanujanProjectionV18103
open GoldbachCircleMethodPrimitiveTwistedRamanujanSupportV18208

/-- Once the unweighted mixed inner product vanishes, every constant component
of an arbitrary weight can be removed exactly. -/
theorem unit_supported_weighted_inner_eq_centered
    {K q l : ℕ} [NeZero K] [NeZero q] [NeZero l]
    (hq : q ∣ K) (hl : l ∣ K) (hql : q ≠ l)
    (f : ZMod q → ℂ) (g : ZMod l → ℂ)
    (hf : ∀ a, ¬ IsUnit a → ZMod.dft f a = 0)
    (hg : ∀ b, ¬ IsUnit b → ZMod.dft g b = 0)
    (weight : ZMod K → ℂ) (c : ℂ) :
    (∑ x : ZMod K,
      (star (f (ZMod.castHom hq (ZMod q) x)) *
        g (ZMod.castHom hl (ZMod l) x)) * weight x) =
    ∑ x : ZMod K,
      (star (f (ZMod.castHom hq (ZMod q) x)) *
        g (ZMod.castHom hl (ZMod l) x)) * (weight x - c) := by
  let atom : ZMod K → ℂ := fun x =>
    star (f (ZMod.castHom hq (ZMod q) x)) *
      g (ZMod.castHom hl (ZMod l) x)
  have hzero : (∑ x : ZMod K, atom x) = 0 := by
    exact two_unit_supported_mixed_inner_zero hq hl hql f g hf hg
  have hdiff :
      (∑ x : ZMod K, atom x * weight x) -
          (∑ x : ZMod K, atom x * (weight x - c)) =
        c * (∑ x : ZMod K, atom x) := by
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _hx
    ring
  rw [hzero, mul_zero] at hdiff
  exact sub_eq_zero.mp hdiff

/-- The same exact centering identity for the genuine primitive twisted
Ramanujan atoms.  Distinct ambient denominators are the only cancellation
hypothesis. -/
theorem twistedRamanujan_weighted_inner_eq_centered
    {K r s l k : ℕ}
    [NeZero K] [NeZero r] [NeZero s] [NeZero l] [NeZero k]
    (hrl : r * l ∣ K) (hsk : s * k ∣ K)
    (hrlcop : Nat.Coprime r l) (hskcop : Nat.Coprime s k)
    (hden : r * l ≠ s * k)
    (χ : DirichletCharacter ℂ r) (ψ : DirichletCharacter ℂ s)
    (hχ : χ.IsPrimitive) (hψ : ψ.IsPrimitive)
    (weight : ZMod K → ℂ) (c : ℂ) :
    (∑ x : ZMod K,
      (star (twistedRamanujan r l χ
        (ZMod.castHom hrl (ZMod (r * l)) x)) *
      twistedRamanujan s k ψ
        (ZMod.castHom hsk (ZMod (s * k)) x)) * weight x) =
    ∑ x : ZMod K,
      (star (twistedRamanujan r l χ
        (ZMod.castHom hrl (ZMod (r * l)) x)) *
      twistedRamanujan s k ψ
        (ZMod.castHom hsk (ZMod (s * k)) x)) * (weight x - c) := by
  let _ : NeZero (r * l) :=
    ⟨Nat.mul_ne_zero (NeZero.ne r) (NeZero.ne l)⟩
  let _ : NeZero (s * k) :=
    ⟨Nat.mul_ne_zero (NeZero.ne s) (NeZero.ne k)⟩
  exact unit_supported_weighted_inner_eq_centered hrl hsk hden
    (twistedRamanujan r l χ) (twistedRamanujan s k ψ)
    (twistedRamanujan_dft_nonunit_zero r l hrlcop χ hχ)
    (twistedRamanujan_dft_nonunit_zero s k hskcop ψ hψ) weight c

end GoldbachCircleMethodWeightedCrossDenominatorCenteringV18543
