import GoldbachCircleMethodNonreducedMassEnvelopeV1867

/-! # V1.8.68: general coprime character evaluation, including prime powers.
The higher-prime-power cancellation is a finite translation argument.
-/
open scoped BigOperators
open GoldbachCircleMethodFiniteResiduePrefixV1866
open GoldbachCircleMethodRamanujanCoprimeBindingV1840
open GoldbachCircleMethodRamanujanCharacterProductV1843

namespace GoldbachCircleMethodGeneralCoprimeCharacterV1868

attribute [local instance] Classical.propDecidable

theorem prime_power_unit_translation (p k : ℕ) (hp : p.Prime)
    (r : ZMod (p^(k+2))) :
    IsUnit (r+((p^(k+1) : ℕ) : ZMod (p^(k+2)))) ↔ IsUnit r := by
  let _ : NeZero (p^(k+2)) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have ht : p ∣ p^(k+1) := by rw [pow_succ]; exact dvd_mul_left p (p^k)
  have heq : r+((p^(k+1) : ℕ) : ZMod (p^(k+2))) =
      ((r.val+p^(k+1) : ℕ) : ZMod (p^(k+2))) := by simp
  have hr : IsUnit r ↔ ¬ p ∣ r.val := by
    simpa only [ZMod.natCast_zmod_val] using
      (ZMod.isUnit_natCast_iff_not_dvd_pow (a := r.val) hp (by omega : 0 < k+2))
  rw [heq, ZMod.isUnit_natCast_iff_not_dvd_pow hp (by omega)]
  exact (not_congr (Nat.dvd_add_left ht)).trans hr.symm

theorem higher_prime_power_character_zero (p k : ℕ) (hp : p.Prime)
    (a : ZMod (p^(k+2))) (ha : IsUnit a) :
    @unitCharacterSum (p^(k+2)) ⟨pow_ne_zero _ hp.ne_zero⟩ a = 0 := by
  let _ : NeZero (p^(k+2)) := ⟨pow_ne_zero _ hp.ne_zero⟩
  let t : ZMod (p^(k+2)) := ((p^(k+1) : ℕ) : ZMod (p^(k+2)))
  have ht0 : t ≠ 0 := by
    intro ht
    have hv := congrArg ZMod.val ht
    have hlt : p^(k+1) < p^(k+2) := by
      exact pow_lt_pow_right₀ hp.one_lt (by omega)
    simp only [t, ZMod.val_natCast_of_lt hlt, ZMod.val_zero] at hv
    exact (pow_ne_zero _ hp.ne_zero) hv
  have hchar : ZMod.stdAddChar (a*t) ≠ 1 := by
    intro h
    have hz : a*t=0 := ZMod.injective_stdAddChar (h.trans (ZMod.stdAddChar.map_zero_eq_one).symm)
    exact ht0 (ha.mul_right_eq_zero.mp hz)
  let f : ZMod (p^(k+2)) → ℂ := fun r =>
    if IsUnit r then ZMod.stdAddChar (a*r) else 0
  have ht (r : ZMod (p^(k+2))) : f (r+t)=f r*ZMod.stdAddChar (a*t) := by
    dsimp only [f]
    have hu : IsUnit (r+t) ↔ IsUnit r := prime_power_unit_translation p k hp r
    simp only [hu, mul_add, AddChar.map_add_eq_mul, ite_mul, zero_mul]
  have hsum : unitCharacterSum (p^(k+2)) a =
      unitCharacterSum (p^(k+2)) a*ZMod.stdAddChar (a*t) := by
    change (∑ r, f r) = (∑ r, f r)*ZMod.stdAddChar (a*t)
    calc
      (∑ r, f r) = ∑ r, f (r+t) := (Equiv.sum_comp (Equiv.addRight t) f).symm
      _ = _ := by simp only [ht, Finset.sum_mul]
  have hz : unitCharacterSum (p^(k+2)) a*(1-ZMod.stdAddChar (a*t))=0 := by
    linear_combination hsum
  exact (mul_eq_zero.mp hz).resolve_right (sub_ne_zero.mpr (Ne.symm hchar))

theorem finiteFourierRamanujan_eq_unitCharacterSum (q N : ℕ) (hq : q ≠ 0) :
    finiteFourierRamanujan q N hq = @unitCharacterSum q ⟨hq⟩ (N : ZMod q) := by
  let _ : NeZero q := ⟨hq⟩
  unfold finiteFourierRamanujan unitCharacterSum
  apply Finset.sum_congr rfl
  intro r _
  by_cases hr : IsUnit r <;> simp only [hr, if_true, if_false, mul_comm]

theorem finiteFourierRamanujan_eq_moebius_of_coprime (q : ℕ) :
    ∀ N : ℕ, Nat.Coprime N q → ∀ hq : q ≠ 0,
      finiteFourierRamanujan q N hq = ((ArithmeticFunction.moebius q : ℤ) : ℂ) := by
  refine Nat.recOnPrimeCoprime (motive := fun q => ∀ N : ℕ, Nat.Coprime N q →
    ∀ hq : q ≠ 0, finiteFourierRamanujan q N hq =
      ((ArithmeticFunction.moebius q : ℤ) : ℂ)) ?_ ?_ ?_ q
  · intro _ _ hq
    exact (hq rfl).elim
  · intro p n hp N hN hq
    rcases n with _ | (_ | k)
    · simpa using finiteFourierRamanujan_one N
    · simpa using finiteFourierRamanujan_eq_moebius_of_prime hp (by simpa using hN)
    · rw [finiteFourierRamanujan_eq_unitCharacterSum,
        ArithmeticFunction.moebius_apply_prime_pow hp (by omega), if_neg (by omega),
        Int.cast_zero]
      exact higher_prime_power_character_zero p k hp (N : ZMod (p^(k+2)))
        ((ZMod.isUnit_iff_coprime N (p^(k+2))).mpr hN)
  · intro u v hu hv huv ihu ihv N hN hq
    have hu0 : u ≠ 0 := by omega
    have hv0 : v ≠ 0 := by omega
    have hNu : Nat.Coprime N u := hN.of_dvd_right (dvd_mul_right u v)
    have hNv : Nat.Coprime N v := hN.of_dvd_right (dvd_mul_left v u)
    rw [finiteFourierRamanujan_mul_of_coprime hu0 hv0 huv N,
      ihu N hNu hu0, ihv N hNv hv0,
      ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime huv]
    norm_cast

theorem unitCharacterSum_eq_moebius (q : ℕ) [NeZero q] (a : ZMod q) (ha : IsUnit a) :
    unitCharacterSum q a = ((ArithmeticFunction.moebius q : ℤ) : ℂ) := by
  have hcop : Nat.Coprime a.val q := by
    apply (ZMod.isUnit_iff_coprime a.val q).mp
    simpa only [ZMod.natCast_zmod_val] using ha
  have h := finiteFourierRamanujan_eq_moebius_of_coprime q a.val hcop (NeZero.ne q)
  simpa only [finiteFourierRamanujan_eq_unitCharacterSum, ZMod.natCast_zmod_val] using h

theorem rational_prefix_error_moebius (M k q : ℕ) [NeZero q] (a : ZMod q)
    (ha : IsUnit a) (hkM : k ≤ M) (B : ℝ) (hB : 0 ≤ B)
    (hclasses : ∀ r : ZMod q, IsUnit r →
      |psiResidue k q r-(k : ℝ)/(Nat.totient q : ℝ)| ≤ B) :
    ‖GoldbachCircleMethodFourierIdentityV171.exponentialSum k.succ
      (((a.val : ℝ)/(q : ℝ) : ℝ) : UnitAddCircle)-
        ((((ArithmeticFunction.moebius q : ℤ) : ℂ)/(Nat.totient q : ℂ))*(k : ℂ))‖ ≤
      (q : ℝ)*B+((q+1 : ℝ)+2*Real.sqrt (M : ℝ))*Real.log (M : ℝ) := by
  have h := rational_prefix_error_le k q a B hB hclasses
  rw [unitCharacterSum_eq_moebius q a ha] at h
  have heq : ((k : ℂ)/(Nat.totient q : ℂ))*((ArithmeticFunction.moebius q : ℤ) : ℂ) =
      ((((ArithmeticFunction.moebius q : ℤ) : ℂ)/(Nat.totient q : ℂ))*(k : ℂ)) := by ring
  rw [heq] at h
  exact h.trans (add_le_add le_rfl
    (GoldbachCircleMethodNonreducedMassEnvelopeV1867.nonreducedMass_le_uniform_envelope M k q hkM))

end GoldbachCircleMethodGeneralCoprimeCharacterV1868
