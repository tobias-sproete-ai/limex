import GoldbachCircleMethodPrimitiveGaussCoefficientV18114

set_option autoImplicit false
open scoped BigOperators Classical
open GoldbachCircleMethodFiniteResiduePrefixV1866
open GoldbachCircleMethodPrimitiveConductorRegroupingV18111
open GoldbachCircleMethodUnitCharacterExpansionAuditV18110
open GoldbachCircleMethodPrimitiveGaussCoefficientV18114

namespace GoldbachCircleMethodFullPrimitiveExpansionV18115

/-- Transport of the actual finite Ramanujan sum along equality of levels. -/
theorem unitCharacterSum_nat_level_congr (a b : ℕ) [NeZero a] [NeZero b]
    (h : a = b) (N : ℕ) :
    unitCharacterSum a (N : ZMod a) = unitCharacterSum b (N : ZMod b) := by
  subst b
  rfl

variable (q : ℕ) [NeZero q]

/-- The quotient level is positive because the primitive level actually divides q. -/
theorem primitive_complement_ne_zero (i : PrimitiveIndex q) : q / i.1.val ≠ 0 := by
  intro hz
  have h := Nat.mul_div_cancel' i.1.property
  rw [hz, mul_zero] at h
  exact NeZero.ne q h.symm

noncomputable def primitiveCoefficient (i : PrimitiveIndex q) (N : ℕ) : ℂ :=
  let : NeZero i.1.val := ⟨primitive_index_ne_zero q i⟩
  let : NeZero (q / i.1.val) := ⟨primitive_complement_ne_zero q i⟩
  if Nat.Coprime i.1.val (q / i.1.val) then
    (i.1.val : ℂ) * ((ArithmeticFunction.moebius (q / i.1.val) : ℤ) : ℂ) *
      unitCharacterSum (q / i.1.val) (N : ZMod (q / i.1.val)) *
      i.2.val (N : ZMod i.1.val)
  else 0

/-- Every V111 index receives the proved V114 coefficient, with the quotient
bound to q/r by divisibility, rather than chosen independently. -/
theorem primitive_index_convolution_coefficient (i : PrimitiveIndex q) (N : ℕ) :
    (∑ v : ZMod q, (liftIndex i) v * unitCharacterSum q ((N : ZMod q)-v)) =
      primitiveCoefficient q i N := by
  rcases i with ⟨⟨r, hr⟩, ⟨χ, hχ⟩⟩
  obtain ⟨l, hq⟩ := hr
  subst q
  have hr0 : r ≠ 0 := by
    intro h
    exact NeZero.ne (r*l) (by simp [h])
  have hl0 : l ≠ 0 := by
    intro h
    exact NeZero.ne (r*l) (by simp [h])
  let : NeZero r := ⟨hr0⟩
  let : NeZero l := ⟨hl0⟩
  let : NeZero (r*l/r) := ⟨primitive_complement_ne_zero (r*l)
    ⟨⟨r, Nat.dvd_mul_right r l⟩, ⟨χ,hχ⟩⟩⟩
  have hquot : r*l/r=l := Nat.mul_div_cancel_left l (Nat.pos_of_ne_zero hr0)
  have hsum := unitCharacterSum_nat_level_congr (r*l/r) l hquot N
  simp only [liftIndex, primitiveCoefficient, hsum, hquot]
  exact lifted_ramanujan_coefficient r l χ hχ N

/-- The full exact finite primitive-conductor expansion, still retaining phi(q). -/
theorem full_primitive_expansion (N : ℕ) (u : ZMod q) (hu : IsUnit u) :
    (∑ i : PrimitiveIndex q, (liftIndex i) u⁻¹ * primitiveCoefficient q i N) =
      (q.totient : ℂ) * unitCharacterSum q ((N : ZMod q)-u) := by
  calc
    _ = ∑ i : PrimitiveIndex q, (liftIndex i) u⁻¹ *
        (∑ v : ZMod q, (liftIndex i) v * unitCharacterSum q ((N : ZMod q)-v)) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [primitive_index_convolution_coefficient]
    _ = _ := by
      rw [sum_over_primitive_conductors q (fun χ =>
        χ u⁻¹ * (∑ v : ZMod q, χ v * unitCharacterSum q ((N : ZMod q)-v)))]
      exact ramanujan_unit_character_expansion q (N : ZMod q) u hu

omit [NeZero q] in
/-- The ambient unit input is also pulled back to the actual primitive parent.
No identification of inverse and complex conjugate is assumed. -/
theorem liftIndex_at_inverse_unit (i : PrimitiveIndex q) (u : ZMod q) (hu : IsUnit u) :
    (liftIndex i) u⁻¹ = i.2.val (ZMod.cast u⁻¹ : ZMod i.1.val) := by
  obtain ⟨w, rfl⟩ := hu
  simpa only [liftIndex, ZMod.inv_coe_unit] using
    DirichletCharacter.changeLevel_eq_cast_of_dvd i.2.val i.1.property w⁻¹

/-- All summands now use primitive-parent data with the exact finite complement. -/
theorem full_primitive_parent_expansion (N : ℕ) (u : ZMod q) (hu : IsUnit u) :
    (∑ i : PrimitiveIndex q,
      i.2.val (ZMod.cast u⁻¹ : ZMod i.1.val) * primitiveCoefficient q i N) =
      (q.totient : ℂ) * unitCharacterSum q ((N : ZMod q)-u) := by
  simpa only [liftIndex_at_inverse_unit q _ u hu] using full_primitive_expansion q N u hu

/-- Normalization is division by the positive totient, never by a Gauss sum. -/
theorem normalized_primitive_parent_expansion (N : ℕ) (u : ZMod q) (hu : IsUnit u) :
    unitCharacterSum q ((N : ZMod q)-u) =
      (∑ i : PrimitiveIndex q,
        i.2.val (ZMod.cast u⁻¹ : ZMod i.1.val) * primitiveCoefficient q i N) /
          (q.totient : ℂ) := by
  have hphi : (q.totient : ℂ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q)))
  rw [full_primitive_parent_expansion q N u hu]
  field_simp

end GoldbachCircleMethodFullPrimitiveExpansionV18115
