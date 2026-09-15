import GoldbachCircleMethodActualPrincipalTwistCrossDiagonalV18210
set_option autoImplicit false
open scoped BigOperators Classical

namespace GoldbachCircleMethodActualTwistSelfConvolutionV18211
open GoldbachCircleMethodFiniteResiduePrefixV1866
open GoldbachCircleMethodActualCompanionPeriodicLiftV18202
open GoldbachCircleMethodMixedRamanujanOrthogonalityV18203
open GoldbachCircleMethodActualTwistedCompleteProjectionV18209
open GoldbachCircleMethodPrimitiveTwistedRamanujanSupportV18208
open GoldbachCircleMethodExceptionalModelDiagonalV18107

/-- Two actual functions with unit DFT support at distinct denominators have zero
complete common-period convolution. Neither function is replaced by a Ramanujan kernel. -/
theorem two_unit_supported_mixed_convolution_zero {K q l : ℕ}
    [NeZero K] [NeZero q] [NeZero l]
    (hq : q ∣ K) (hl : l ∣ K) (hql : q ≠ l)
    (f : ZMod q → ℂ) (g : ZMod l → ℂ)
    (hf : ∀ a, ¬ IsUnit a → ZMod.dft f a = 0)
    (hg : ∀ b, ¬ IsUnit b → ZMod.dft g b = 0) (m : ZMod K) :
    (∑ x : ZMod K, f (ZMod.castHom hq (ZMod q) (m-x)) *
      g (ZMod.castHom hl (ZMod l) x)) = 0 := by
  have hscale : ((q : ℂ)*(l : ℂ)) *
      (∑ x : ZMod K, f (ZMod.castHom hq (ZMod q) (m-x)) *
        g (ZMod.castHom hl (ZMod l) x)) = 0 := by
    rw [Finset.mul_sum]
    simp_rw [show ∀ x : ZMod K,
      ((q : ℂ)*(l : ℂ)) * (f (ZMod.castHom hq (ZMod q) (m-x)) *
        g (ZMod.castHom hl (ZMod l) x)) =
      ((q : ℂ)*f (ZMod.castHom hq (ZMod q) (m-x))) *
        ((l : ℂ)*g (ZMod.castHom hl (ZMod l) x)) by intro x; ring]
    simp_rw [← unit_supported_fourier_expansion f hf,
      ← unit_supported_fourier_expansion g hg]
    simp_rw [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro a _
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro b _
    by_cases ha : IsUnit a
    · by_cases hb : IsUnit b
      · simp only [ha, hb, if_true]
        have hz := liftedUnitCharacter_convolution_zero hq hl ha.unit hb.unit hql m
        have hw := congrArg (fun z : ℂ => z * (ZMod.dft f a * ZMod.dft g b)) hz
        simp only [liftedUnitCharacter_apply, IsUnit.unit_spec, Finset.sum_mul,
          zero_mul] at hw
        simpa only [mul_comm, mul_left_comm, mul_assoc] using hw
      · simp [hb]
    · simp [ha]
  exact (mul_eq_zero.mp hscale).resolve_left
    (mul_ne_zero (NeZero.ne (q : ℂ)) (NeZero.ne (l : ℂ)))

variable (r l : ℕ) [NeZero r] [NeZero l]
local instance productNeZero : NeZero (r*l) :=
  ⟨Nat.mul_ne_zero (NeZero.ne r) (NeZero.ne l)⟩

/-- Canonical ring CRT factors spatial self-convolution without Fourier rescaling. -/
theorem crt_product_self_convolution (hcop : Nat.Coprime r l)
    (f : ZMod r → ℂ) (g : ZMod l → ℂ) (m : ZMod (r*l)) :
    (∑ x : ZMod (r*l),
      (f (ZMod.castHom (Nat.dvd_mul_right r l) (ZMod r) (m-x)) *
       g (ZMod.castHom (Nat.dvd_mul_left l r) (ZMod l) (m-x))) *
      (f (ZMod.castHom (Nat.dvd_mul_right r l) (ZMod r) x) *
       g (ZMod.castHom (Nat.dvd_mul_left l r) (ZMod l) x))) =
    (∑ a : ZMod r, f (ZMod.castHom (Nat.dvd_mul_right r l) (ZMod r) m-a)*f a) *
    (∑ b : ZMod l, g (ZMod.castHom (Nat.dvd_mul_left l r) (ZMod l) m-b)*g b) := by
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
      (f (ZMod.castHom (Nat.dvd_mul_right r l) (ZMod r) (m-e x)) *
       g (ZMod.castHom (Nat.dvd_mul_left l r) (ZMod l) (m-e x))) *
      (f (ZMod.castHom (Nat.dvd_mul_right r l) (ZMod r) (e x)) *
       g (ZMod.castHom (Nat.dvd_mul_left l r) (ZMod l) (e x))) =
      (f (ZMod.castHom (Nat.dvd_mul_right r l) (ZMod r) m-x.1)*f x.1) *
      (g (ZMod.castHom (Nat.dvd_mul_left l r) (ZMod l) m-x.2)*g x.2) := by
    intro x
    have h1 := congrArg Prod.fst (hc x)
    have h2 := congrArg Prod.snd (hc x)
    dsimp only [Prod.fst, Prod.snd] at h1 h2
    rw [map_sub, map_sub, h1, h2]
    ring
  simp_rw [ht]
  rw [Fintype.sum_prod_type, Fintype.sum_mul_sum]

/-- Actual primitive self-inverse twist: the r factor cancels, while l remains.
There is no conjugation and no squarefree-r hypothesis. -/
theorem twistedRamanujan_self_convolution (hcop : Nat.Coprime r l)
    (χ : DirichletCharacter ℂ r) (hχ : χ.IsPrimitive) (hInv : χ⁻¹ = χ)
    (m : ZMod (r*l)) :
    (∑ x : ZMod (r*l), twistedRamanujan r l χ (m-x) *
      twistedRamanujan r l χ x) =
    (l : ℂ)*χ (-1) *
      unitCharacterSum r (ZMod.castHom (Nat.dvd_mul_right r l) (ZMod r) m) *
      unitCharacterSum l (ZMod.castHom (Nat.dvd_mul_left l r) (ZMod l) m) := by
  unfold twistedRamanujan
  rw [crt_product_self_convolution r l hcop]
  have hc :
      (∑ a : ZMod r, χ (ZMod.castHom (Nat.dvd_mul_right r l) (ZMod r) m-a)*χ a) =
      χ (-1)*unitCharacterSum r (ZMod.castHom (Nat.dvd_mul_right r l) (ZMod r) m) := by
    simpa only [mul_comm] using primitive_quadratic_self_convolution r χ hχ hInv
      (ZMod.castHom (Nat.dvd_mul_right r l) (ZMod r) m)
  rw [hc, ramanujan_self_convolution]
  ring

/-- Lift to a complete common period K. Exact repetition yields K/r, not K or K/l. -/
theorem lifted_twistedRamanujan_self_convolution {K : ℕ} [NeZero K]
    (hrl : r*l ∣ K) (hcop : Nat.Coprime r l)
    (χ : DirichletCharacter ℂ r) (hχ : χ.IsPrimitive) (hInv : χ⁻¹ = χ)
    (m : ZMod K) :
    (∑ x : ZMod K,
      twistedRamanujan r l χ (ZMod.castHom hrl (ZMod (r*l)) (m-x)) *
      twistedRamanujan r l χ (ZMod.castHom hrl (ZMod (r*l)) x)) =
    ((K : ℂ)/(r : ℂ))*χ (-1) *
      unitCharacterSum r (ZMod.castHom (dvd_trans (Nat.dvd_mul_right r l) hrl) (ZMod r) m) *
      unitCharacterSum l (ZMod.castHom (dvd_trans (Nat.dvd_mul_left l r) hrl) (ZMod l) m) := by
  simp only [map_sub]
  rw [sum_reduction_exact hrl (fun y =>
    twistedRamanujan r l χ (ZMod.castHom hrl (ZMod (r*l)) m-y) *
      twistedRamanujan r l χ y), twistedRamanujan_self_convolution r l hcop χ hχ hInv]
  have hrread :=
    congrArg (fun f : ZMod K →+* ZMod r => f m)
      (ZMod.castHom_comp (Nat.dvd_mul_right r l) hrl)
  have hlread :=
    congrArg (fun f : ZMod K →+* ZMod l => f m)
      (ZMod.castHom_comp (Nat.dvd_mul_left l r) hrl)
  simp only [RingHom.comp_apply] at hrread hlread
  rw [hrread, hlread]
  have hK : ((K/(r*l) : ℕ) : ℂ)*(r : ℂ)*(l : ℂ) = (K : ℂ) := by
    rw [← Nat.cast_mul, ← Nat.cast_mul, mul_assoc, Nat.div_mul_cancel hrl]
  have hscale : ((K/(r*l) : ℕ) : ℂ)*(l : ℂ) = (K : ℂ)/(r : ℂ) := by
    apply (eq_div_iff (NeZero.ne (r : ℂ))).mpr
    calc
      _ = ((K/(r*l) : ℕ) : ℂ)*(r : ℂ)*(l : ℂ) := by ring
      _ = (K : ℂ) := hK
  calc
    _ = (((K/(r*l) : ℕ) : ℂ)*(l : ℂ)) *
      (χ (-1) *
      unitCharacterSum r (ZMod.castHom (dvd_trans (Nat.dvd_mul_right r l) hrl) (ZMod r) m) *
      unitCharacterSum l (ZMod.castHom (dvd_trans (Nat.dvd_mul_left l r) hrl) (ZMod l) m)) := by ring
    _ = _ := by rw [hscale]; ring

/-- Distinct l at a fixed positive r give distinct exact denominators r*l. -/
theorem twistedRamanujan_mixed_convolution_zero {K k : ℕ} [NeZero K] [NeZero k]
    (hrl : r*l ∣ K) (hrk : r*k ∣ K)
    (hlcop : Nat.Coprime r l) (hkcop : Nat.Coprime r k) (hlk : l ≠ k)
    (χ : DirichletCharacter ℂ r) (hχ : χ.IsPrimitive) (m : ZMod K) :
    (∑ x : ZMod K,
      twistedRamanujan r l χ (ZMod.castHom hrl (ZMod (r*l)) (m-x)) *
      twistedRamanujan r k χ (ZMod.castHom hrk (ZMod (r*k)) x)) = 0 := by
  have hprod : r*l ≠ r*k := by
    intro h
    exact hlk (Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero (NeZero.ne r)) h)
  exact two_unit_supported_mixed_convolution_zero hrl hrk hprod
    (twistedRamanujan r l χ) (twistedRamanujan r k χ)
    (twistedRamanujan_dft_nonunit_zero r l hlcop χ hχ)
    (twistedRamanujan_dft_nonunit_zero r k hkcop χ hχ) m

/-- Exact full-period diagonal/off-diagonal matrix for actual fixed-r twists.
Full V121 C*C assembly and sign control are separate obligations. -/
theorem twistedRamanujan_complete_matrix {K k : ℕ} [NeZero K] [NeZero k]
    (hrl : r*l ∣ K) (hrk : r*k ∣ K)
    (hlcop : Nat.Coprime r l) (hkcop : Nat.Coprime r k)
    (χ : DirichletCharacter ℂ r) (hχ : χ.IsPrimitive) (hInv : χ⁻¹ = χ) (m : ZMod K) :
    (∑ x : ZMod K,
      twistedRamanujan r l χ (ZMod.castHom hrl (ZMod (r*l)) (m-x)) *
      twistedRamanujan r k χ (ZMod.castHom hrk (ZMod (r*k)) x)) =
    if l = k then ((K : ℂ)/(r : ℂ))*χ (-1) *
      unitCharacterSum r (ZMod.castHom (dvd_trans (Nat.dvd_mul_right r l) hrl) (ZMod r) m) *
      unitCharacterSum l (ZMod.castHom (dvd_trans (Nat.dvd_mul_left l r) hrl) (ZMod l) m)
    else 0 := by
  by_cases h : l = k
  · subst k
    rw [if_pos rfl]
    exact lifted_twistedRamanujan_self_convolution r l hrl hlcop χ hχ hInv m
  · rw [if_neg h]
    exact twistedRamanujan_mixed_convolution_zero r l hrl hrk hlcop hkcop h χ hχ m

end GoldbachCircleMethodActualTwistSelfConvolutionV18211
