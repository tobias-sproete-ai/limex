import GoldbachCircleMethodActualUnitPairWeightedReserveV18195

/-! Prime-power counting and unconditional even-target nonemptiness for the
literal V194 two-unit residue carrier. No model reserve or Goldbach conclusion. -/
set_option autoImplicit false
open scoped BigOperators Classical
open GoldbachCircleMethodActualUnitPairArithmeticV18194

namespace GoldbachCircleMethodActualUnitPairPrimePowerV18197

noncomputable def primeReduction (p k : ℕ) :
    ZMod (p ^ (k + 1)) →+* ZMod p :=
  ZMod.castHom (dvd_pow_self p (by omega : k + 1 ≠ 0)) (ZMod p)

theorem primeReduction_surjective (p k : ℕ) :
    Function.Surjective (primeReduction p k) :=
  ZMod.castHom_surjective (dvd_pow_self p (by omega : k + 1 ≠ 0))

theorem isUnit_primePower_iff_reduction {p k : ℕ} (hp : p.Prime)
    (x : ZMod (p ^ (k + 1))) :
    IsUnit x ↔ IsUnit (primeReduction p k x) := by
  let _ : NeZero p := ⟨hp.ne_zero⟩
  let _ : NeZero (p ^ (k + 1)) := ⟨pow_ne_zero _ hp.ne_zero⟩
  rw [← ZMod.natCast_zmod_val x]
  simp only [primeReduction, ZMod.castHom_apply]
  rw [ZMod.cast_eq_val]
  rw [ZMod.isUnit_iff_coprime, ZMod.isUnit_iff_coprime,
    Nat.coprime_pow_right_iff (by omega : 0 < k + 1)]
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt x.val_lt]

theorem mem_unitPairResidues_primePower_iff {p k : ℕ}
    [NeZero p] [NeZero (p ^ (k + 1))] (hp : p.Prime)
    (m : ℤ) (x : ZMod (p ^ (k + 1))) :
    x ∈ unitPairResidues (p ^ (k + 1)) m ↔
      primeReduction p k x ∈ unitPairResidues p m := by
  let _ : NeZero p := ⟨hp.ne_zero⟩
  let _ : NeZero (p ^ (k + 1)) := ⟨pow_ne_zero _ hp.ne_zero⟩
  rw [mem_unitPairResidues, mem_unitPairResidues,
    isUnit_primePower_iff_reduction hp,
    isUnit_primePower_iff_reduction hp]
  change IsUnit (primeReduction p k x) ∧
      IsUnit (primeReduction p k (((m : ℤ) : ZMod (p ^ (k + 1))) - x)) ↔ _
  simp [primeReduction]

noncomputable def primeReductionFiber (p k : ℕ)
    [NeZero p] [NeZero (p ^ (k + 1))] (y : ZMod p) :
    Finset (ZMod (p ^ (k + 1))) :=
  Finset.univ.filter fun x ↦ primeReduction p k x = y

theorem primeReduction_fiber_card {p k : ℕ}
    [NeZero p] [NeZero (p ^ (k + 1))]
    (hp : p.Prime) (y : ZMod p) :
    (primeReductionFiber p k y).card = p ^ k := by
  let f := (primeReduction p k).toAddMonoidHom
  have hsurj : Function.Surjective f := primeReduction_surjective p k
  have hsame : ∀ z : ZMod p,
      (primeReductionFiber p k z).card =
        (primeReductionFiber p k 0).card := by
    intro z
    simpa [primeReductionFiber, f] using
      AddMonoidHom.card_fiber_eq_of_mem_range f (hsurj z) (hsurj 0)
  have htotal : Fintype.card (ZMod (p ^ (k + 1))) =
      ∑ z : ZMod p, (primeReductionFiber p k z).card := by
    rw [Fintype.card]
    simpa [primeReductionFiber, f] using
      (Finset.card_eq_sum_card_fiberwise
        (s := (Finset.univ : Finset (ZMod (p ^ (k + 1)))))
        (t := (Finset.univ : Finset (ZMod p))) (f := f)
        (fun _ _ ↦ Finset.mem_univ _))
  have hzero : (primeReductionFiber p k 0).card = p ^ k := by
    simp_rw [hsame] at htotal
    simp only [ZMod.card, Finset.sum_const, nsmul_eq_mul] at htotal
    have htotal' : p ^ (k + 1) = p * (primeReductionFiber p k 0).card := by
      simpa using htotal
    have hcancel : p * p ^ k = p * (primeReductionFiber p k 0).card := by
      calc
        p * p ^ k = p ^ (k + 1) := by rw [pow_succ']
        _ = p * (primeReductionFiber p k 0).card := htotal'
    exact Nat.eq_of_mul_eq_mul_left hp.pos hcancel.symm
  exact (hsame y).trans hzero

theorem unitPairCount_prime_pow_succ {p k : ℕ} (hp : p.Prime) (m : ℤ) :
    @unitPairCount (p ^ (k + 1)) ⟨pow_ne_zero _ hp.ne_zero⟩ m =
      p ^ k * (if (p : ℤ) ∣ m then p - 1 else p - 2) := by
  let _ : NeZero p := ⟨hp.ne_zero⟩
  let _ : NeZero (p ^ (k + 1)) := ⟨pow_ne_zero _ hp.ne_zero⟩
  let f := primeReduction p k
  have hcarrier : unitPairResidues (p ^ (k + 1)) m =
      Finset.univ.filter (fun x : ZMod (p ^ (k + 1)) ↦
        f x ∈ unitPairResidues p m) := by
    ext x
    simpa [f] using mem_unitPairResidues_primePower_iff hp m x
  rw [unitPairCount, hcarrier, ← Finset.sum_card_fiberwise_eq_card_filter]
  simp_rw [show ∀ y : ZMod p,
      ((Finset.univ : Finset (ZMod (p ^ (k + 1)))).filter fun x ↦ f x = y).card =
        p ^ k by
      intro y
      simpa [primeReductionFiber, f] using primeReduction_fiber_card hp y]
  simp only [Finset.sum_const, nsmul_eq_mul]
  change unitPairCount p m * p ^ k = _
  let _ : Fact p.Prime := ⟨hp⟩
  rw [unitPairCount_prime]
  by_cases hpm : (p : ℤ) ∣ m <;> simp [hpm, mul_comm]

/-- Every prime-power factor has a nonempty literal two-unit carrier at an
even natural target.  The `p = 2` branch necessarily lies in the divisible
case, while every odd prime leaves at least one admissible residue. -/
theorem unitPairCount_prime_pow_succ_pos_of_even {p k m : ℕ}
    (hp : p.Prime) (hm : Even m) :
    0 < @unitPairCount (p ^ (k + 1)) ⟨pow_ne_zero _ hp.ne_zero⟩ (m : ℤ) := by
  rw [unitPairCount_prime_pow_succ hp]
  have hpow : 0 < p ^ k := pow_pos hp.pos k
  by_cases hpm : (p : ℤ) ∣ (m : ℤ)
  · rw [if_pos hpm]
    exact Nat.mul_pos hpow (Nat.sub_pos_of_lt hp.one_lt)
  · rw [if_neg hpm]
    have hp2 : p ≠ 2 := by
      intro hp2
      subst p
      have htwoNat : 2 ∣ m := even_iff_two_dvd.mp hm
      have htwoInt : (2 : ℤ) ∣ (m : ℤ) := by exact_mod_cast htwoNat
      exact hpm htwoInt
    exact Nat.mul_pos hpow (by have := hp.two_le; omega)

/-- For every positive modulus and every even natural target, the literal
carrier `{x : ZMod r | IsUnit x ∧ IsUnit (m - x)}` is nonempty.  This is a
finite arithmetic statement, obtained from the prime-power count and the
existing coprime CRT product law. -/
theorem unitPairCount_pos_of_even (r : ℕ) :
    ∀ m : ℕ, ∀ hr0 : r ≠ 0, Even m →
      0 < @unitPairCount r ⟨hr0⟩ (m : ℤ) := by
  induction r using Nat.recOnPrimeCoprime with
  | zero =>
      intro _ hr0
      exact (hr0 rfl).elim
  | prime_pow p k hp =>
      intro m hr0 hm
      rcases k with _ | k
      · simp only [pow_zero] at hr0 ⊢
        rw [unitPairCount]
        change 0 < (unitPairResidues 1 (m : ℤ)).card
        have hall : unitPairResidues 1 (m : ℤ) = Finset.univ := by
          apply Finset.filter_eq_self.mpr
          intro x _
          constructor
          · rw [Subsingleton.elim x 1]
            exact isUnit_one
          · rw [Subsingleton.elim (((m : ℤ) : ZMod 1) - x) 1]
            exact isUnit_one
        rw [hall]
        simp
      · simpa only [] using unitPairCount_prime_pow_succ_pos_of_even hp hm
  | coprime a b ha hb hab iha ihb =>
      intro m hab0 hm
      have ha0 : a ≠ 0 := by omega
      have hb0 : b ≠ 0 := by omega
      have hia := iha m ha0 hm
      have hib := ihb m hb0 hm
      let _ : NeZero a := ⟨ha0⟩
      let _ : NeZero b := ⟨hb0⟩
      rw [unitPairCount_mul hab]
      exact Nat.mul_pos hia hib

end GoldbachCircleMethodActualUnitPairPrimePowerV18197
