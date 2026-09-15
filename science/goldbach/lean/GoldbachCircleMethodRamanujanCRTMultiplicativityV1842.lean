import GoldbachCircleMethodRamanujanMultiplicativityV1841
import Mathlib.Data.ZMod.Basic

/-!
# V1.8.42: scaled CRT carrier for Fourier multiplicativity

This module constructs the exact scaled CRT permutation required before the standard additive
character can factor. It does not yet prove the character factorization or Ramanujan-sum
multiplicativity.
-/

namespace GoldbachCircleMethodRamanujanCRTMultiplicativityV1842

set_option linter.style.haveILetI false

/-- The scaled CRT parametrization `(a,b) ↦ CRT⁻¹(r*a,q*b)`. The two scale factors are
units under `Coprime q r`, so this is an equivalence. -/
noncomputable def scaledCRTEquiv {q r : ℕ} (_hq : q ≠ 0) (_hr : r ≠ 0)
    (hqr : Nat.Coprime q r) : ZMod q × ZMod r ≃ ZMod (q * r) := by
  let uq : (ZMod q)ˣ := ZMod.unitOfCoprime r hqr.symm
  let ur : (ZMod r)ˣ := ZMod.unitOfCoprime q hqr
  exact (Equiv.prodCongr uq.mulLeft ur.mulLeft).trans (ZMod.chineseRemainder hqr).symm.toEquiv

/-- Readback through the canonical CRT map exposes the two required scale factors. -/
theorem chineseRemainder_scaledCRTEquiv {q r : ℕ} (hq : q ≠ 0) (hr : r ≠ 0)
    (hqr : Nat.Coprime q r) (x : ZMod q × ZMod r) :
    ZMod.chineseRemainder hqr (scaledCRTEquiv hq hr hqr x) =
      ((r : ZMod q) * x.1, (q : ZMod r) * x.2) := by
  letI : NeZero q := ⟨hq⟩
  letI : NeZero r := ⟨hr⟩
  let uq : (ZMod q)ˣ := ZMod.unitOfCoprime r hqr.symm
  let ur : (ZMod r)ˣ := ZMod.unitOfCoprime q hqr
  change ZMod.chineseRemainder hqr
      ((ZMod.chineseRemainder hqr).symm ((uq : ZMod q) * x.1, (ur : ZMod r) * x.2)) = _
  rw [RingEquiv.apply_symm_apply]
  rfl

/-- The scaled CRT equivalence matches the unit carrier exactly with the product unit carrier. -/
theorem isUnit_scaledCRTEquiv_iff {q r : ℕ} (hq : q ≠ 0) (hr : r ≠ 0)
    (hqr : Nat.Coprime q r) (x : ZMod q × ZMod r) :
    IsUnit (scaledCRTEquiv hq hr hqr x) ↔ IsUnit x.1 ∧ IsUnit x.2 := by
  letI : NeZero q := ⟨hq⟩
  letI : NeZero r := ⟨hr⟩
  let uq : (ZMod q)ˣ := ZMod.unitOfCoprime r hqr.symm
  let ur : (ZMod r)ˣ := ZMod.unitOfCoprime q hqr
  change IsUnit ((ZMod.chineseRemainder hqr).symm ((uq : ZMod q) * x.1, (ur : ZMod r) * x.2)) ↔ _
  rw [isUnit_map_iff, Prod.isUnit_iff, Units.isUnit_units_mul, Units.isUnit_units_mul]

end GoldbachCircleMethodRamanujanCRTMultiplicativityV1842
