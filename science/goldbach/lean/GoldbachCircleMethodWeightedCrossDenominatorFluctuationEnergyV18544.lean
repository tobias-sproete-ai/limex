import GoldbachCircleMethodWeightedCrossDenominatorCenteringV18543

/-!
# Goldbach V1.8.544: weighted cross-denominator fluctuation energy

The exact centering identity of V1.8.543 is converted into a finite L2
interface.  Distinct-denominator orthogonality removes only the constant
weight component; the remaining mixed inner product is charged exactly to
the centered weight energy.  No bound for that energy is asserted.
-/

set_option autoImplicit false

open scoped BigOperators Classical ComplexConjugate

namespace GoldbachCircleMethodWeightedCrossDenominatorFluctuationEnergyV18544

open GoldbachCircleMethodWeightedCrossDenominatorCenteringV18543
open GoldbachCircleMethodPrimitiveRamanujanProjectionV18103
open GoldbachCircleMethodPrimitiveTwistedRamanujanSupportV18208

/-- Cauchy--Schwarz after exact removal of the constant weight component.
The conclusion deliberately exposes both finite energies. -/
theorem unit_supported_weighted_inner_sq_le_centered_energy
    {K q l : ℕ} [NeZero K] [NeZero q] [NeZero l]
    (hq : q ∣ K) (hl : l ∣ K) (hql : q ≠ l)
    (f : ZMod q → ℂ) (g : ZMod l → ℂ)
    (hf : ∀ a, ¬ IsUnit a → ZMod.dft f a = 0)
    (hg : ∀ b, ¬ IsUnit b → ZMod.dft g b = 0)
    (weight : ZMod K → ℂ) (c : ℂ) :
    ‖∑ x : ZMod K,
        (star (f (ZMod.castHom hq (ZMod q) x)) *
          g (ZMod.castHom hl (ZMod l) x)) * weight x‖ ^ 2 ≤
      (∑ x : ZMod K,
          ‖star (f (ZMod.castHom hq (ZMod q) x)) *
            g (ZMod.castHom hl (ZMod l) x)‖ ^ 2) *
        ∑ x : ZMod K, ‖weight x - c‖ ^ 2 := by
  let atom : ZMod K → ℂ := fun x =>
    star (f (ZMod.castHom hq (ZMod q) x)) *
      g (ZMod.castHom hl (ZMod l) x)
  have hcenter := unit_supported_weighted_inner_eq_centered
    hq hl hql f g hf hg weight c
  change ‖∑ x : ZMod K, atom x * weight x‖ ^ 2 ≤ _
  rw [hcenter]
  have htriangle :
      ‖∑ x : ZMod K, atom x * (weight x - c)‖ ≤
        ∑ x : ZMod K, ‖atom x‖ * ‖weight x - c‖ := by
    calc
      _ ≤ ∑ x : ZMod K, ‖atom x * (weight x - c)‖ :=
        norm_sum_le _ _
      _ = _ := by
        apply Finset.sum_congr rfl
        intro x _hx
        rw [norm_mul]
  have hsq := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr htriangle
  exact hsq.trans (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun x : ZMod K => ‖atom x‖)
    (fun x : ZMod K => ‖weight x - c‖))

/-- The fluctuation-energy interface for genuine primitive twisted Ramanujan
atoms at distinct ambient denominators. -/
theorem twistedRamanujan_weighted_inner_sq_le_centered_energy
    {K r s l k : ℕ}
    [NeZero K] [NeZero r] [NeZero s] [NeZero l] [NeZero k]
    (hrl : r * l ∣ K) (hsk : s * k ∣ K)
    (hrlcop : Nat.Coprime r l) (hskcop : Nat.Coprime s k)
    (hden : r * l ≠ s * k)
    (χ : DirichletCharacter ℂ r) (ψ : DirichletCharacter ℂ s)
    (hχ : χ.IsPrimitive) (hψ : ψ.IsPrimitive)
    (weight : ZMod K → ℂ) (c : ℂ) :
    ‖∑ x : ZMod K,
        (star (twistedRamanujan r l χ
          (ZMod.castHom hrl (ZMod (r * l)) x)) *
        twistedRamanujan s k ψ
          (ZMod.castHom hsk (ZMod (s * k)) x)) * weight x‖ ^ 2 ≤
      (∑ x : ZMod K,
          ‖star (twistedRamanujan r l χ
            (ZMod.castHom hrl (ZMod (r * l)) x)) *
          twistedRamanujan s k ψ
            (ZMod.castHom hsk (ZMod (s * k)) x)‖ ^ 2) *
        ∑ x : ZMod K, ‖weight x - c‖ ^ 2 := by
  let _ : NeZero (r * l) :=
    ⟨Nat.mul_ne_zero (NeZero.ne r) (NeZero.ne l)⟩
  let _ : NeZero (s * k) :=
    ⟨Nat.mul_ne_zero (NeZero.ne s) (NeZero.ne k)⟩
  exact unit_supported_weighted_inner_sq_le_centered_energy
    hrl hsk hden
    (twistedRamanujan r l χ) (twistedRamanujan s k ψ)
    (twistedRamanujan_dft_nonunit_zero r l hrlcop χ hχ)
    (twistedRamanujan_dft_nonunit_zero s k hskcop ψ hψ)
    weight c

end GoldbachCircleMethodWeightedCrossDenominatorFluctuationEnergyV18544
