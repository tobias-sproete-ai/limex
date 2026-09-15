import GoldbachCircleMethodCoprimeInducedGaussV18112
import Mathlib.RingTheory.Nilpotent.Basic

set_option autoImplicit false
open scoped BigOperators Classical

namespace GoldbachCircleMethodNoncoprimeInducedGaussV18113

variable {q r : ℕ} [NeZero q] [NeZero r]

omit [NeZero q] in
/-- Nilpotent translation preserves precisely the unit support. -/
theorem isUnit_add_nilpotent_iff (x t : ZMod q) (ht : IsNilpotent t) :
    IsUnit (x+t) ↔ IsUnit x := by
  constructor
  · intro hx
    have h := ht.neg.isUnit_add_left_of_commute hx (Commute.all _ _)
    simpa only [add_neg_cancel_right] using h
  · intro hx
    exact ht.isUnit_add_left_of_commute hx (Commute.all _ _)

omit [NeZero r] in
/-- A nilpotent ambient shift reducing to zero at the source level is an exact
period of the ACTUAL induced character, including its zero values. -/
theorem changeLevel_nilpotent_period (hr : r ∣ q) (χ : DirichletCharacter ℂ r)
    (t : ZMod q) (ht : IsNilpotent t) (ht0 : (ZMod.cast t : ZMod r)=0)
    (x : ZMod q) :
    (DirichletCharacter.changeLevel hr χ) (x+t) =
      (DirichletCharacter.changeLevel hr χ) x := by
  have hu := isUnit_add_nilpotent_iff x t ht
  by_cases hx : IsUnit x
  · have hxt := hu.mpr hx
    have hleft := DirichletCharacter.changeLevel_eq_cast_of_dvd χ hr hxt.unit
    have hright := DirichletCharacter.changeLevel_eq_cast_of_dvd χ hr hx.unit
    simp only [hxt.unit_spec] at hleft
    simp only [hx.unit_spec] at hright
    rw [hleft, hright, ZMod.cast_add hr, ht0, add_zero]
  · rw [MulChar.map_nonunit _ hx, MulChar.map_nonunit _ (mt hu.mp hx)]

/-- A nontrivial additive period forces the standard Gauss sum to vanish. -/
theorem standard_gauss_zero_of_period (χ : DirichletCharacter ℂ q)
    (t : ZMod q) (ht : t ≠ 0) (hperiod : ∀ x, χ (x+t)=χ x) :
    gaussSum χ ZMod.stdAddChar = 0 := by
  have hs : gaussSum χ ZMod.stdAddChar =
      ZMod.stdAddChar t * gaussSum χ ZMod.stdAddChar := by
    unfold gaussSum
    conv_lhs =>
      rw [← Equiv.sum_comp (Equiv.addRight t) (fun x => χ x * ZMod.stdAddChar x)]
    change (∑ x : ZMod q, χ (x+t) * ZMod.stdAddChar (x+t)) = _
    simp only [hperiod, AddChar.map_add_eq_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    ring
  have he : ZMod.stdAddChar t ≠ (1 : ℂ) := by
    intro h
    apply ht
    apply ZMod.injective_stdAddChar
    simpa using h
  by_contra h
  apply he
  exact (mul_left_cancel₀ h (by simpa [mul_comm] using hs.symm))

/-- The noncoprime source/complement case vanishes, even without primitivity. -/
theorem induced_gauss_zero_of_noncoprime (r l : ℕ) [NeZero r] [NeZero l]
    (hcop : ¬ Nat.Coprime r l) (χ : DirichletCharacter ℂ r) :
    gaussSum (DirichletCharacter.changeLevel (Nat.dvd_mul_right r l) χ)
      (@ZMod.stdAddChar (r*l) ⟨Nat.mul_ne_zero (NeZero.ne r) (NeZero.ne l)⟩) = 0 := by
  obtain ⟨p, hp, hpr, hpl⟩ := Nat.Prime.not_coprime_iff_dvd.mp hcop
  obtain ⟨a, rfl⟩ := hpr
  obtain ⟨b, rfl⟩ := hpl
  let : NeZero ((p*a)*(p*b)) := ⟨Nat.mul_ne_zero (NeZero.ne (p*a)) (NeZero.ne (p*b))⟩
  let t : ZMod ((p*a)*(p*b)) := (p*a*b : ℕ)
  have hb : b ≠ 0 := by
    intro hb
    exact NeZero.ne (p*b) (by simp [hb])
  have htpos : 0 < p*a*b :=
    Nat.mul_pos (Nat.pos_of_ne_zero (NeZero.ne (p*a))) (Nat.pos_of_ne_zero hb)
  have htlt : p*a*b < (p*a)*(p*b) := by
    calc
      p*a*b = 1*(p*a*b) := by ring
      _ < p*(p*a*b) := Nat.mul_lt_mul_of_pos_right hp.one_lt htpos
      _ = (p*a)*(p*b) := by ring
  have ht : t ≠ 0 := by
    intro h
    have hd : (p*a)*(p*b) ∣ p*a*b := (ZMod.natCast_eq_zero_iff _ _).mp h
    exact (not_le_of_gt htlt) (Nat.le_of_dvd htpos hd)
  have htnil : IsNilpotent t := by
    refine ⟨2, ?_⟩
    change ((p*a*b : ℕ) : ZMod ((p*a)*(p*b))) ^ 2 = 0
    rw [← Nat.cast_pow, ZMod.natCast_eq_zero_iff]
    exact ⟨a*b, by ring⟩
  have ht0 : (ZMod.cast t : ZMod (p*a)) = 0 := by
    dsimp [t]
    rw [ZMod.cast_natCast (Nat.dvd_mul_right (p*a) (p*b))]
    simp
  apply standard_gauss_zero_of_period _ t ht
  exact changeLevel_nilpotent_period (Nat.dvd_mul_right (p*a) (p*b)) χ t htnil ht0

/-- Complete standard Gauss induction formula; the noncoprime branch is
encoded by the character's actual zero value, not by an extra assumption. -/
theorem induced_standard_gauss (r l : ℕ) [NeZero r] [NeZero l]
    (χ : DirichletCharacter ℂ r) :
    gaussSum (DirichletCharacter.changeLevel (Nat.dvd_mul_right r l) χ)
      (@ZMod.stdAddChar (r*l) ⟨Nat.mul_ne_zero (NeZero.ne r) (NeZero.ne l)⟩) =
      χ (l : ZMod r) * gaussSum χ ZMod.stdAddChar *
        ((ArithmeticFunction.moebius l : ℤ) : ℂ) := by
  by_cases hcop : Nat.Coprime r l
  · exact GoldbachCircleMethodCoprimeInducedGaussV18112.induced_standard_gauss_coprime
      r l hcop χ
  · have hunit : ¬ IsUnit (l : ZMod r) := by
      intro h
      exact hcop ((ZMod.isUnit_iff_coprime l r).mp h).symm
    rw [induced_gauss_zero_of_noncoprime r l hcop χ, MulChar.map_nonunit χ hunit]
    simp

end GoldbachCircleMethodNoncoprimeInducedGaussV18113
