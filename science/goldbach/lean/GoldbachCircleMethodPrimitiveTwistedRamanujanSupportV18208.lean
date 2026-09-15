import GoldbachCircleMethodCoupledCompanionRemainderBoundV18207
set_option autoImplicit false
open scoped BigOperators Classical

namespace GoldbachCircleMethodPrimitiveTwistedRamanujanSupportV18208
open GoldbachCircleMethodFiniteResiduePrefixV1866
open GoldbachCircleMethodActualCompanionPeriodicLiftV18202
open GoldbachCircleMethodPrimitiveRamanujanProjectionV18103
open GoldbachCircleMethodSmallConductorPairReserveV18108
open GoldbachCircleMethodRamanujanCRTMultiplicativityV1842
open GoldbachCircleMethodRamanujanCharacterProductV1843

variable (r l : ℕ) [NeZero r] [NeZero l]
local instance productNeZero : NeZero (r*l) := ⟨Nat.mul_ne_zero (NeZero.ne r) (NeZero.ne l)⟩

/-- Readback of BOTH actual reductions on the existing scaled CRT map. -/
theorem scaledCRT_reductions (hcop : Nat.Coprime r l) (x : ZMod r × ZMod l) :
    (ZMod.castHom (Nat.dvd_mul_right r l) (ZMod r)
       (scaledCRTEquiv (NeZero.ne r) (NeZero.ne l) hcop x),
     ZMod.castHom (Nat.dvd_mul_left l r) (ZMod l)
       (scaledCRTEquiv (NeZero.ne r) (NeZero.ne l) hcop x)) =
      ((l : ZMod r)*x.1, (r : ZMod l)*x.2) := by
  have h := chineseRemainder_scaledCRTEquiv (NeZero.ne r) (NeZero.ne l) hcop x
  change (ZMod.cast (scaledCRTEquiv (NeZero.ne r) (NeZero.ne l) hcop x) :
    ZMod r × ZMod l) = _ at h
  apply Prod.ext
  · simpa only [ZMod.castHom_apply, Prod.fst_zmod_cast] using congrArg Prod.fst h
  · simpa only [ZMod.castHom_apply, Prod.snd_zmod_cast] using congrArg Prod.snd h

/-- Negative Fourier phase, retaining the two CRT scale factors in the spatial maps. -/
theorem negative_phase_scaledCRT (hcop : Nat.Coprime r l)
    (k : ZMod (r*l)) (x : ZMod r × ZMod l) :
    ZMod.stdAddChar (-(scaledCRTEquiv (NeZero.ne r) (NeZero.ne l) hcop x*k)) =
      ZMod.stdAddChar (-(x.1 * ZMod.castHom (Nat.dvd_mul_right r l) (ZMod r) k)) *
      ZMod.stdAddChar (-(x.2 * ZMod.castHom (Nat.dvd_mul_left l r) (ZMod l) k)) := by
  have h := stdAddChar_scaledCRTEquiv (NeZero.ne r) (NeZero.ne l) hcop k.val x
  rw [ZMod.natCast_zmod_val, cast_val_eq_reduction (Nat.dvd_mul_right r l),
    cast_val_eq_reduction (Nat.dvd_mul_left l r)] at h
  simpa only [AddChar.map_neg_eq_inv, mul_inv] using congrArg Inv.inv h

/-- Generic finite CRT factorization of the DFT of a product of actual reductions. -/
theorem crt_product_dft (hcop : Nat.Coprime r l)
    (f : ZMod r → ℂ) (g : ZMod l → ℂ) (k : ZMod (r*l)) :
    ZMod.dft (fun x : ZMod (r*l) =>
      f (ZMod.castHom (Nat.dvd_mul_right r l) (ZMod r) x) *
      g (ZMod.castHom (Nat.dvd_mul_left l r) (ZMod l) x)) k =
    ZMod.dft (fun a : ZMod r => f ((l : ZMod r)*a))
      (ZMod.castHom (Nat.dvd_mul_right r l) (ZMod r) k) *
    ZMod.dft (fun b : ZMod l => g ((r : ZMod l)*b))
      (ZMod.castHom (Nat.dvd_mul_left l r) (ZMod l) k) := by
  let e := scaledCRTEquiv (NeZero.ne r) (NeZero.ne l) hcop
  simp only [ZMod.dft_apply, smul_eq_mul]
  rw [← e.sum_comp]
  have ht : ∀ x : ZMod r × ZMod l,
      ZMod.stdAddChar (-(e x*k)) *
        (f (ZMod.castHom (Nat.dvd_mul_right r l) (ZMod r) (e x)) *
         g (ZMod.castHom (Nat.dvd_mul_left l r) (ZMod l) (e x))) =
      (ZMod.stdAddChar (-(x.1*ZMod.castHom (Nat.dvd_mul_right r l) (ZMod r) k)) *
         f ((l : ZMod r)*x.1)) *
      (ZMod.stdAddChar (-(x.2*ZMod.castHom (Nat.dvd_mul_left l r) (ZMod l) k)) *
         g ((r : ZMod l)*x.2)) := by
    intro x
    have hc := scaledCRT_reductions r l hcop x
    have h1 := congrArg Prod.fst hc
    have h2 := congrArg Prod.snd hc
    dsimp only [Prod.fst, Prod.snd] at h1 h2
    rw [show e x = scaledCRTEquiv (NeZero.ne r) (NeZero.ne l) hcop x by rfl,
      negative_phase_scaledCRT, h1, h2]
    ring
  simp_rw [ht]
  rw [Fintype.sum_prod_type, Fintype.sum_mul_sum]

/-- Unit rescaling preserves a previously proved nonunit-frequency zero. -/
theorem dft_nonunit_zero_after_unit_scaling {q : ℕ} [NeZero q]
    (f : ZMod q → ℂ) (u : (ZMod q)ˣ)
    (hf : ∀ a, ¬ IsUnit a → ZMod.dft f a = 0)
    (a : ZMod q) (ha : ¬ IsUnit a) :
    ZMod.dft (fun x => f (u.val*x)) a = 0 := by
  rw [ZMod.dft_comp_unitMul]
  apply hf
  simpa only [Units.isUnit_units_mul] using ha

/-- This is the actual spatial product, not an induced changeLevel character. -/
noncomputable def twistedRamanujan (χ : DirichletCharacter ℂ r)
    (x : ZMod (r*l)) : ℂ :=
  χ (ZMod.castHom (Nat.dvd_mul_right r l) (ZMod r) x) *
    unitCharacterSum l (ZMod.castHom (Nat.dvd_mul_left l r) (ZMod l) x)

/-- The true primitive-character/Ramanujan product has only unit DFT support.
No squarefree or self-inverse assumption is added to the primitive character. -/
theorem twistedRamanujan_dft_nonunit_zero (hcop : Nat.Coprime r l)
    (χ : DirichletCharacter ℂ r) (hχ : χ.IsPrimitive)
    (k : ZMod (r*l)) (hk : ¬ IsUnit k) :
    ZMod.dft (twistedRamanujan r l χ) k = 0 := by
  unfold twistedRamanujan
  rw [crt_product_dft r l hcop]
  have hcrt := isUnit_map_iff (ZMod.chineseRemainder hcop) k
  change IsUnit (ZMod.cast k : ZMod r × ZMod l) ↔ IsUnit k at hcrt
  rw [Prod.isUnit_iff, Prod.fst_zmod_cast, Prod.snd_zmod_cast] at hcrt
  by_cases hr : IsUnit (ZMod.castHom (Nat.dvd_mul_right r l) (ZMod r) k)
  · have hl : ¬ IsUnit (ZMod.castHom (Nat.dvd_mul_left l r) (ZMod l) k) :=
      fun h => hk (hcrt.mp ⟨hr,h⟩)
    have hz := dft_nonunit_zero_after_unit_scaling (unitCharacterSum l)
      (ZMod.unitOfCoprime r hcop)
      (fun a ha => by rw [ramanujan_dft]; simp [unitIndicator, ha]) _ hl
    simpa only [ZMod.coe_unitOfCoprime, hz, mul_zero] using
      congrArg (fun z => ZMod.dft (fun a : ZMod r => χ ((l : ZMod r)*a))
        (ZMod.castHom (Nat.dvd_mul_right r l) (ZMod r) k) * z) hz
  · have hz := dft_nonunit_zero_after_unit_scaling (χ : ZMod r → ℂ)
      (ZMod.unitOfCoprime l hcop.symm) (dft_nonunit_zero r χ hχ) _ hr
    simpa only [ZMod.coe_unitOfCoprime, hz, zero_mul] using
      congrArg (fun z => z * ZMod.dft (fun b : ZMod l => unitCharacterSum l ((r : ZMod l)*b))
        (ZMod.castHom (Nat.dvd_mul_left l r) (ZMod l) k)) hz

end GoldbachCircleMethodPrimitiveTwistedRamanujanSupportV18208
