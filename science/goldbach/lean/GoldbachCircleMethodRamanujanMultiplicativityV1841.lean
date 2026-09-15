import GoldbachCircleMethodRamanujanCoprimeBindingV1840

/-!
# V1.8.41: coprime-argument invariance for the genuine finite Fourier carrier

This is a strict intermediate bridge. It removes the coprime argument by an exact
permutation of `ZMod q`. It does not prove modulus multiplicativity or a composite-modulus
Möbius evaluation.
-/

open scoped BigOperators

namespace GoldbachCircleMethodRamanujanMultiplicativityV1841

open GoldbachCircleMethodRamanujanCoprimeBindingV1840

set_option linter.style.haveILetI false

/-- Multiplication by an argument coprime to `q` permutes the genuine unit carrier, so the
finite Fourier Ramanujan sum reduces exactly to argument one. -/
theorem finiteFourierRamanujan_coprime_argument
    {q N : ℕ} (hq : q ≠ 0) (hN : Nat.Coprime N q) :
    finiteFourierRamanujan q N hq = finiteFourierRamanujan q 1 hq := by
  letI : NeZero q := ⟨hq⟩
  classical
  let u : (ZMod q)ˣ := ZMod.unitOfCoprime N hN
  have hbij : Function.Bijective (fun a : ZMod q => (u : ZMod q) * a) :=
    u.mulLeft_bijective
  have hNunit : IsUnit (N : ZMod q) := (ZMod.isUnit_iff_coprime N q).mpr hN
  unfold finiteFourierRamanujan
  exact Fintype.sum_bijective (fun a : ZMod q => (u : ZMod q) * a) hbij _ _ fun a => by
    by_cases ha : IsUnit a
    · simp [ha, hNunit, u, mul_comm]
    · simp [ha, hNunit, u]
end GoldbachCircleMethodRamanujanMultiplicativityV1841
