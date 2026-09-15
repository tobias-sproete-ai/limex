import GoldbachCircleMethodActualCompanionPeriodicLiftV18202

set_option autoImplicit false
open scoped BigOperators Classical

namespace GoldbachCircleMethodMixedRamanujanOrthogonalityV18203

/-- A unit frequency has exact denominator q, including q=1. -/
theorem unit_stdAddChar_pow_eq_one_iff (q : ℕ) [NeZero q]
    (a : (ZMod q)ˣ) (k : ℕ) :
    ZMod.stdAddChar (a : ZMod q) ^ k = 1 ↔ q ∣ k := by
  rw [← AddChar.map_nsmul_eq_pow, nsmul_eq_mul]
  rw [← AddChar.map_zero_eq_one (ZMod.stdAddChar (N := q)),
    ZMod.injective_stdAddChar.eq_iff, a.mul_left_eq_zero]
  exact ZMod.natCast_eq_zero_iff k q

/-- Distinct positive reduced denominators cannot give the same root value. -/
theorem unit_stdAddChar_eq_implies_modulus_eq
    (q l : ℕ) [NeZero q] [NeZero l]
    (a : (ZMod q)ˣ) (b : (ZMod l)ˣ)
    (h : ZMod.stdAddChar (a : ZMod q) = ZMod.stdAddChar (b : ZMod l)) :
    q = l := by
  apply Nat.dvd_antisymm
  · apply (unit_stdAddChar_pow_eq_one_iff q a l).mp
    rw [h]
    exact (unit_stdAddChar_pow_eq_one_iff l b l).mpr (dvd_refl l)
  · apply (unit_stdAddChar_pow_eq_one_iff l b q).mp
    rw [← h]
    exact (unit_stdAddChar_pow_eq_one_iff q a q).mpr (dvd_refl q)

/-- Pull back the original standard additive character along divisor reduction. -/
noncomputable def liftedUnitCharacter {K q : ℕ} [NeZero K] [NeZero q]
    (hq : q ∣ K) (a : (ZMod q)ˣ) : AddChar (ZMod K) ℂ :=
  (ZMod.stdAddChar.mulShift (a : ZMod q)).compAddMonoidHom
    (ZMod.castHom hq (ZMod q)).toAddMonoidHom

@[simp] theorem liftedUnitCharacter_apply {K q : ℕ} [NeZero K] [NeZero q]
    (hq : q ∣ K) (a : (ZMod q)ˣ) (x : ZMod K) :
    liftedUnitCharacter hq a x =
      ZMod.stdAddChar ((a : ZMod q) * ZMod.castHom hq (ZMod q) x) := rfl

theorem liftedUnitCharacter_ne {K q l : ℕ} [NeZero K] [NeZero q] [NeZero l]
    (hq : q ∣ K) (hl : l ∣ K) (a : (ZMod q)ˣ) (b : (ZMod l)ˣ)
    (hql : q ≠ l) :
    liftedUnitCharacter hq a ≠ liftedUnitCharacter hl b := by
  intro h
  have hv := congrArg (fun f : AddChar (ZMod K) ℂ => f 1) h
  simp only [liftedUnitCharacter_apply, map_one, mul_one] at hv
  exact hql (unit_stdAddChar_eq_implies_modulus_eq q l a b hv)

theorem liftedUnitCharacter_orthogonality {K q l : ℕ}
    [NeZero K] [NeZero q] [NeZero l]
    (hq : q ∣ K) (hl : l ∣ K) (a : (ZMod q)ˣ) (b : (ZMod l)ˣ)
    (hql : q ≠ l) :
    (∑ x : ZMod K, liftedUnitCharacter hq a (-x) *
      liftedUnitCharacter hl b x) = 0 := by
  have hne : liftedUnitCharacter hl b / liftedUnitCharacter hq a ≠ 1 := by
    rw [div_ne_one]
    exact (liftedUnitCharacter_ne hq hl a b hql).symm
  have hs := AddChar.sum_eq_zero_of_ne_one hne
  simpa only [AddChar.div_apply, mul_comm] using hs

/-- Translation preserves mixed-character cancellation over a complete period. -/
theorem liftedUnitCharacter_convolution_zero {K q l : ℕ}
    [NeZero K] [NeZero q] [NeZero l]
    (hq : q ∣ K) (hl : l ∣ K) (a : (ZMod q)ˣ) (b : (ZMod l)ˣ)
    (hql : q ≠ l) (m : ZMod K) :
    (∑ x : ZMod K, liftedUnitCharacter hq a (m - x) *
      liftedUnitCharacter hl b x) = 0 := by
  simp_rw [sub_eq_add_neg, AddChar.map_add_eq_mul, mul_assoc]
  rw [← Finset.mul_sum, liftedUnitCharacter_orthogonality hq hl a b hql, mul_zero]

/-- The actual V66 Ramanujan sums have zero mixed convolution on a common full period.
    No assertion is made for incomplete intervals or variable weights. -/
theorem actual_unitCharacterSum_mixed_convolution_zero {K q l : ℕ}
    [NeZero K] [NeZero q] [NeZero l]
    (hq : q ∣ K) (hl : l ∣ K) (hql : q ≠ l) (m : ZMod K) :
    (∑ x : ZMod K,
      GoldbachCircleMethodFiniteResiduePrefixV1866.unitCharacterSum q
        (ZMod.castHom hq (ZMod q) (m - x)) *
      GoldbachCircleMethodFiniteResiduePrefixV1866.unitCharacterSum l
        (ZMod.castHom hl (ZMod l) x)) = 0 := by
  unfold GoldbachCircleMethodFiniteResiduePrefixV1866.unitCharacterSum
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
      simpa only [liftedUnitCharacter_apply, IsUnit.unit_spec, mul_comm]
        using liftedUnitCharacter_convolution_zero hq hl ha.unit hb.unit hql m
    · simp [hb]
  · simp [ha]

end GoldbachCircleMethodMixedRamanujanOrthogonalityV18203
