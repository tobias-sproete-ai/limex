import GoldbachCircleMethodActualResidualMomentCompositionV18193
import GoldbachCircleMethodSmallConductorPairReserveV18108

set_option autoImplicit false

/-!
# Actual finite unit-pair arithmetic

This module records only the literal finite carrier
`{x : ZMod r | IsUnit x ∧ IsUnit (m - x)}`.  It proves the prime count and
the exact coprime CRT product law.  No infinite Euler product, exceptional
character property, analytic reserve, or Goldbach conclusion is asserted.
-/

open scoped BigOperators

namespace GoldbachCircleMethodActualUnitPairArithmeticV18194

/-- The literal residue carrier on which both linear forms are units. -/
noncomputable def unitPairResidues (r : ℕ) [NeZero r] (m : ℤ) : Finset (ZMod r) := by
  classical
  exact Finset.univ.filter fun x => IsUnit x ∧ IsUnit ((m : ZMod r) - x)

/-- The cardinality of the literal unit-pair residue carrier. -/
noncomputable def unitPairCount (r : ℕ) [NeZero r] (m : ℤ) : ℕ :=
  (unitPairResidues r m).card

theorem mem_unitPairResidues {r : ℕ} [NeZero r] {m : ℤ} {x : ZMod r} :
    x ∈ unitPairResidues r m ↔ IsUnit x ∧ IsUnit ((m : ZMod r) - x) := by
  simp [unitPairResidues]

/-- Over a prime modulus the two forbidden residues are exactly `0` and `m`. -/
theorem unitPairResidues_prime_eq {p : ℕ} [hp : Fact p.Prime] (m : ℤ) :
    unitPairResidues p m =
      (Finset.univ.erase (0 : ZMod p)).erase (m : ZMod p) := by
  classical
  ext x
  simp only [unitPairResidues, Finset.mem_filter, Finset.mem_univ, true_and,
    isUnit_iff_ne_zero, Finset.mem_erase]
  constructor
  · rintro ⟨hx0, hmx⟩
    exact ⟨fun hxm => hmx (sub_eq_zero.mpr hxm.symm), hx0, trivial⟩
  · rintro ⟨hxm, hx0, -⟩
    exact ⟨hx0, fun hzero => hxm (sub_eq_zero.mp hzero).symm⟩

/-- The exact prime-modulus count, including `p = 2`. -/
theorem unitPairCount_prime {p : ℕ} [hp : Fact p.Prime] (m : ℤ) :
    unitPairCount p m =
      if (p : ℤ) ∣ m then p - 1 else p - 2 := by
  classical
  rw [unitPairCount, unitPairResidues_prime_eq]
  by_cases hm : (m : ZMod p) = 0
  · have hd : (p : ℤ) ∣ m := (ZMod.intCast_zmod_eq_zero_iff_dvd m p).mp hm
    rw [if_pos hd, hm]
    simp [ZMod.card]
  · have hnd : ¬(p : ℤ) ∣ m := by
      intro hd
      exact hm ((ZMod.intCast_zmod_eq_zero_iff_dvd m p).mpr hd)
    rw [if_neg hnd]
    simp [Finset.card_erase_of_mem, hm, ZMod.card]
    omega

/-- The subtype form of the literal carrier, used only to state the CRT bijection. -/
abbrev UnitPairType (r : ℕ) (m : ℤ) :=
  {x : ZMod r // IsUnit x ∧ IsUnit ((m : ZMod r) - x)}

/-- Chinese remainder preserves both unit predicates and the subtraction `m - x`. -/
noncomputable def unitPairCRTEquiv {q r : ℕ} [NeZero q] [NeZero r]
    (hqr : q.Coprime r) (m : ℤ) :
    UnitPairType (q * r) m ≃ UnitPairType q m × UnitPairType r m := by
  let e := ZMod.chineseRemainder hqr
  refine (e.toEquiv.subtypeEquiv ?_).trans Equiv.subtypeProdEquivProd
  intro x
  change (IsUnit x ∧ IsUnit ((m : ZMod (q * r)) - x)) ↔
    (IsUnit (e x).1 ∧ IsUnit ((m : ZMod q) - (e x).1)) ∧
      (IsUnit (e x).2 ∧ IsUnit ((m : ZMod r) - (e x).2))
  have hsub : e ((m : ZMod (q * r)) - x) =
      ((m : ZMod q) - (e x).1, (m : ZMod r) - (e x).2) := by
    rw [map_sub, map_intCast]
    rfl
  constructor
  · rintro ⟨hx, hmx⟩
    have hex : IsUnit (e x) := (isUnit_map_iff e x).mpr hx
    have hemx : IsUnit (e ((m : ZMod (q * r)) - x)) :=
      (isUnit_map_iff e ((m : ZMod (q * r)) - x)).mpr hmx
    rw [Prod.isUnit_iff] at hex
    rw [hsub, Prod.isUnit_iff] at hemx
    exact ⟨⟨hex.1, hemx.1⟩, hex.2, hemx.2⟩
  · rintro ⟨⟨hxq, hmq⟩, hxr, hmr⟩
    have hex : IsUnit (e x) := Prod.isUnit_iff.mpr ⟨hxq, hxr⟩
    have hemx : IsUnit (e ((m : ZMod (q * r)) - x)) := by
      rw [hsub, Prod.isUnit_iff]
      exact ⟨hmq, hmr⟩
    exact ⟨(isUnit_map_iff e x).mp hex,
      (isUnit_map_iff e ((m : ZMod (q * r)) - x)).mp hemx⟩

theorem unitPairType_card (r : ℕ) [NeZero r] (m : ℤ) :
    Fintype.card (UnitPairType r m) = unitPairCount r m := by
  classical
  simpa [unitPairCount, unitPairResidues] using
    (Fintype.card_subtype (fun x : ZMod r =>
      IsUnit x ∧ IsUnit ((m : ZMod r) - x)))

/-- Exact coprime multiplicativity of the literal unit-pair cardinality. -/
theorem unitPairCount_mul {q r : ℕ} [NeZero q] [NeZero r]
    (hqr : q.Coprime r) (m : ℤ) :
    unitPairCount (q * r) m = unitPairCount q m * unitPairCount r m := by
  rw [← unitPairType_card, ← unitPairType_card, ← unitPairType_card]
  simpa only [Fintype.card_prod] using Fintype.card_congr (unitPairCRTEquiv hqr m)

/-- The actual first character marginal over the literal two-unit carrier. -/
noncomputable def primitiveUnitPairMarginal (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (m : ℤ) : ℂ :=
  ∑ x ∈ unitPairResidues q m, χ x

theorem primitiveUnitPairMarginal_eq_unit_sum (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (m : ℤ) :
    primitiveUnitPairMarginal q χ m =
      ∑ x : ZMod q, χ x *
        GoldbachCircleMethodSmallConductorPairReserveV18108.unitIndicator q
          ((m : ZMod q) - x) := by
  classical
  unfold primitiveUnitPairMarginal unitPairResidues
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : IsUnit x
  · by_cases hmx : IsUnit ((m : ZMod q) - x)
    · simp [hx, hmx,
        GoldbachCircleMethodSmallConductorPairReserveV18108.unitIndicator]
    · simp [hx, hmx,
        GoldbachCircleMethodSmallConductorPairReserveV18108.unitIndicator]
  · rw [χ.map_nonunit hx]
    simp [hx, GoldbachCircleMethodSmallConductorPairReserveV18108.unitIndicator]

/-- V108's genuine primitive marginal, now restricted to the literal unit-pair carrier. -/
theorem primitiveUnitPairMarginal_eq_moebius_mul
    (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (m : ℤ) :
    primitiveUnitPairMarginal q χ m =
      ((ArithmeticFunction.moebius q : ℤ) : ℂ) * χ (m : ZMod q) := by
  rw [primitiveUnitPairMarginal_eq_unit_sum]
  exact GoldbachCircleMethodSmallConductorPairReserveV18108.primitive_unit_pair_sum
    q χ hχ (m : ZMod q)

/-- On squarefree moduli coprime to the target, the actual count is the finite
product of the prime local counts. -/
theorem unitPairCount_squarefree_coprime (r : ℕ) :
    ∀ m : ℕ, ∀ hr0 : r ≠ 0, Squarefree r → m.Coprime r →
      @unitPairCount r ⟨hr0⟩ (m : ℤ) = ∏ p ∈ r.primeFactors, (p - 2) := by
  induction r using Nat.recOnPrimeCoprime with
  | zero =>
      intro _ hr0
      exact (hr0 rfl).elim
  | prime_pow p k hp =>
      intro m hr0 hsq hcop
      rcases k with _ | k
      · simp only [pow_zero] at hr0 hsq hcop ⊢
        rw [unitPairCount]
        simp only [Nat.primeFactors_one, Finset.prod_empty]
        change (unitPairResidues 1 (m : ℤ)).card = 1
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
      · have hk : k + 1 = 1 :=
          ((Nat.squarefree_pow_iff hp.ne_one (by omega)).mp hsq).2
        have hk0 : k = 0 := by omega
        subst k
        simp only [zero_add, pow_one] at hr0 hsq hcop ⊢
        let _ : Fact p.Prime := ⟨hp⟩
        have hpdvd : ¬p ∣ m := (hp.coprime_iff_not_dvd).mp hcop.symm
        have hpInt : ¬(p : ℤ) ∣ (m : ℤ) := by exact_mod_cast hpdvd
        rw [unitPairCount_prime, if_neg hpInt]
        simp [hp.primeFactors]
  | coprime a b ha hb hab iha ihb =>
      intro m hab0 hsq hcop
      have ha0 : a ≠ 0 := by omega
      have hb0 : b ≠ 0 := by omega
      have hsqa : Squarefree a := hsq.squarefree_of_dvd (dvd_mul_right a b)
      have hsqb : Squarefree b := hsq.squarefree_of_dvd (dvd_mul_left b a)
      have hcopa : m.Coprime a := hcop.of_dvd_right (dvd_mul_right a b)
      have hcopb : m.Coprime b := hcop.of_dvd_right (dvd_mul_left b a)
      let _ : NeZero a := ⟨ha0⟩
      let _ : NeZero b := ⟨hb0⟩
      rw [unitPairCount_mul hab, iha m ha0 hsqa hcopa, ihb m hb0 hsqb hcopb,
        hab.primeFactors_mul, Finset.prod_union hab.disjoint_primeFactors]

/-- In the squarefree, target-coprime, even-target range the actual count is
positive; once the modulus exceeds `3`, it is at least `3`. -/
theorem unitPairCount_pos_and_three_le (r : ℕ) :
    ∀ m : ℕ, ∀ hr0 : r ≠ 0, Even m → Squarefree r → m.Coprime r →
      1 ≤ @unitPairCount r ⟨hr0⟩ (m : ℤ) ∧
        (3 < r → 3 ≤ @unitPairCount r ⟨hr0⟩ (m : ℤ)) := by
  induction r using Nat.recOnPrimeCoprime with
  | zero =>
      intro _ hr0
      exact (hr0 rfl).elim
  | prime_pow p k hp =>
      intro m hr0 hmEven hsq hcop
      rcases k with _ | k
      · simp only [pow_zero] at hr0 hsq hcop ⊢
        have hcount := unitPairCount_squarefree_coprime 1 m hr0 hsq hcop
        simp only [Nat.primeFactors_one, Finset.prod_empty] at hcount
        omega
      · have hk : k + 1 = 1 :=
          ((Nat.squarefree_pow_iff hp.ne_one (by omega)).mp hsq).2
        have hk0 : k = 0 := by omega
        subst k
        simp only [zero_add, pow_one] at hr0 hsq hcop ⊢
        let _ : Fact p.Prime := ⟨hp⟩
        have hpdvd : ¬p ∣ m := (hp.coprime_iff_not_dvd).mp hcop.symm
        have hpInt : ¬(p : ℤ) ∣ (m : ℤ) := by exact_mod_cast hpdvd
        have hp2 : p ≠ 2 := by
          rintro rfl
          exact hpdvd ((even_iff_two_dvd.mp hmEven))
        have hpLower : 2 ≤ p := hp.two_le
        have hp3 : 3 ≤ p := by omega
        have hp4 : p ≠ 4 := by
          rintro rfl
          norm_num at hp
        rw [unitPairCount_prime, if_neg hpInt]
        change 1 ≤ p - 2 ∧ (3 < p → 3 ≤ p - 2)
        constructor <;> omega
  | coprime a b ha hb hab iha ihb =>
      intro m hab0 hmEven hsq hcop
      have ha0 : a ≠ 0 := by omega
      have hb0 : b ≠ 0 := by omega
      have hsqa : Squarefree a := hsq.squarefree_of_dvd (dvd_mul_right a b)
      have hsqb : Squarefree b := hsq.squarefree_of_dvd (dvd_mul_left b a)
      have hcopa : m.Coprime a := hcop.of_dvd_right (dvd_mul_right a b)
      have hcopb : m.Coprime b := hcop.of_dvd_right (dvd_mul_left b a)
      have hia := iha m ha0 hmEven hsqa hcopa
      have hib := ihb m hb0 hmEven hsqb hcopb
      let _ : NeZero a := ⟨ha0⟩
      let _ : NeZero b := ⟨hb0⟩
      rw [unitPairCount_mul hab]
      constructor
      · exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero
          (Nat.one_le_iff_ne_zero.mp hia.1) (Nat.one_le_iff_ne_zero.mp hib.1))
      · intro hab3
        have ha2 : a ≠ 2 := by
          rintro rfl
          exact (Nat.not_coprime_of_dvd_of_dvd (by omega)
            (even_iff_two_dvd.mp hmEven) (dvd_refl 2)) hcopa
        have hb2 : b ≠ 2 := by
          rintro rfl
          exact (Nat.not_coprime_of_dvd_of_dvd (by omega)
            (even_iff_two_dvd.mp hmEven) (dvd_refl 2)) hcopb
        have hor : 3 < a ∨ 3 < b := by
          by_contra hnot
          push Not at hnot
          have hae : a = 3 := by omega
          have hbe : b = 3 := by omega
          subst a
          subst b
          norm_num at hab
        rcases hor with ha3 | hb3
        · exact le_trans (by simpa using hia.2 ha3)
            (Nat.le_mul_of_pos_right (unitPairCount a (m : ℤ)) hib.1)
        · exact le_trans (by simpa using hib.2 hb3)
            (Nat.le_mul_of_pos_left (unitPairCount b (m : ℤ)) hia.1)

/-- The exact `D ≥ 3` finite arithmetic input requested for the later reserve step. -/
theorem three_le_unitPairCount_of_squarefree_coprime_even
    {r m : ℕ} (hr0 : r ≠ 0) (hmEven : Even m) (hsq : Squarefree r)
    (hcop : m.Coprime r) (hr3 : 3 < r) :
    3 ≤ @unitPairCount r ⟨hr0⟩ (m : ℤ) :=
  (unitPairCount_pos_and_three_le r m hr0 hmEven hsq hcop).2 hr3

end GoldbachCircleMethodActualUnitPairArithmeticV18194
