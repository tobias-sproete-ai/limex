import GoldbachCircleMethodTotientConjugateMatchV18116
import Mathlib.Data.Sigma.Basic

set_option autoImplicit false
open scoped BigOperators Classical
open GoldbachCircleMethodPrimitiveConductorRegroupingV18111
open GoldbachCircleMethodFiniteResiduePrefixV1866
open GoldbachCircleMethodFullPrimitiveExpansionV18115
open GoldbachCircleMethodTotientConjugateMatchV18116

namespace GoldbachCircleMethodBoundedConductorReindexV18117

abbrev PositiveLevel (Q : ℕ) := {q : ℕ // q ∈ Finset.Icc 1 Q}

instance positiveLevelNeZero {Q : ℕ} (q : PositiveLevel Q) : NeZero q.val :=
  ⟨Nat.ne_of_gt (Nat.lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp q.property).1)⟩

abbrev BoundedIndex (Q : ℕ) := Σ q : PositiveLevel Q, PrimitiveIndex q.val
abbrev ProductData (Q : ℕ) :=
  Σ r : PositiveLevel Q, {χ : DirichletCharacter ℂ r.val // χ.IsPrimitive} × PositiveLevel Q
abbrev ProductIndex (Q : ℕ) :=
  {j : ProductData Q // j.1.val * j.2.2.val ≤ Q}

/-- Product reconstruction uses the coupled bound r*l<=Q and retains the actual character. -/
def reassemble {Q : ℕ} (j : ProductIndex Q) : BoundedIndex Q :=
  ⟨⟨j.val.1.val * j.val.2.2.val,
      Finset.mem_Icc.mpr ⟨Nat.mul_pos
        (Nat.pos_of_ne_zero (NeZero.ne j.val.1.val))
        (Nat.pos_of_ne_zero (NeZero.ne j.val.2.2.val)), j.property⟩⟩,
    ⟨⟨j.val.1.val, Nat.dvd_mul_right _ _⟩, j.val.2.1⟩⟩

/-- Every bounded ambient character index has a positive bounded complement. -/
theorem reassemble_surjective (Q : ℕ) : Function.Surjective (@reassemble Q) := by
  rintro ⟨⟨q, hq⟩, ⟨⟨r, hr⟩, ⟨χ, hχ⟩⟩⟩
  have hqpos : 0 < q := (Finset.mem_Icc.mp hq).1
  have hqbound : q ≤ Q := (Finset.mem_Icc.mp hq).2
  change DirichletCharacter ℂ r at χ
  change r ∣ q at hr
  obtain ⟨l, hprod⟩ := hr
  subst q
  have hrpos : 0 < r := Nat.pos_of_mul_pos_right hqpos
  have hlpos : 0 < l := Nat.pos_of_mul_pos_left hqpos
  have hrbound : r ≤ Q := (Nat.le_mul_of_pos_right r hlpos).trans hqbound
  have hlbound : l ≤ Q := (Nat.le_mul_of_pos_left l hrpos).trans hqbound
  exact ⟨⟨⟨⟨r, Finset.mem_Icc.mpr ⟨hrpos,hrbound⟩⟩, ⟨χ,hχ⟩,
    ⟨l, Finset.mem_Icc.mpr ⟨hlpos,hlbound⟩⟩⟩, hqbound⟩, rfl⟩

/-- The ambient level and the primitive conductor determine the complement;
character equality then follows inside the unchanged primitive level. -/
theorem reassemble_injective (Q : ℕ) : Function.Injective (@reassemble Q) := by
  rintro ⟨⟨⟨r, hr⟩, χ, ⟨l, hl⟩⟩, hrl⟩ ⟨⟨⟨s, hs⟩, ψ, ⟨k, hk⟩⟩, hsk⟩ h
  have hrs : r=s := congrArg (fun x : BoundedIndex Q => x.2.1.val) h
  subst s
  have hprod : r*l=r*k := congrArg (fun x : BoundedIndex Q => x.1.val) h
  have hrpos : 0 < r := (Finset.mem_Icc.mp hr).1
  have hlk : l=k := Nat.eq_of_mul_eq_mul_left hrpos hprod
  subst k
  dsimp only [reassemble] at h
  have h1 :
      (⟨⟨r, Nat.dvd_mul_right r l⟩, χ⟩ : PrimitiveIndex (r*l)) =
        ⟨⟨r, Nat.dvd_mul_right r l⟩, ψ⟩ :=
    eq_of_heq (Sigma.mk.inj_iff.mp h).2
  have hχψ : χ=ψ := eq_of_heq (Sigma.mk.inj_iff.mp h1).2
  cases hχψ
  rfl

/-- A proved finite carrier equivalence, not an assumed reindexing oracle. -/
noncomputable def boundedConductorEquiv (Q : ℕ) : ProductIndex Q ≃ BoundedIndex Q :=
  Equiv.ofBijective reassemble ⟨reassemble_injective Q, reassemble_surjective Q⟩

/-- Exact finite reindexing with the product cutoff, for any complex summand. -/
theorem sum_bounded_conductor_reindex (Q : ℕ) (F : BoundedIndex Q → ℂ) :
    (∑ i : BoundedIndex Q, F i) =
      ∑ j : ProductIndex Q, F (reassemble j) := by
  exact ((boundedConductorEquiv Q).sum_comp F).symm

/-- The quotient in the old index is exactly the retained complement. -/
theorem quotient_reassemble {Q : ℕ} (j : ProductIndex Q) :
    (reassemble j).1.val / (reassemble j).2.1.val = j.val.2.2.val := by
  exact Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero (NeZero.ne j.val.1.val))

/-- The same complement coefficient on the explicit product carrier. -/
noncomputable def productComplement {Q : ℕ} (j : ProductIndex Q) (N : ℕ) : ℂ :=
  if Nat.Coprime j.val.1.val j.val.2.2.val then
    ((ArithmeticFunction.moebius j.val.2.2.val : ℤ) : ℂ) *
      unitCharacterSum j.val.2.2.val (N : ZMod j.val.2.2.val) /
        (j.val.2.2.val.totient : ℂ)
  else 0

/-- Transport of the actual coefficient, not just equality of scalar indices. -/
theorem complement_reassemble {Q : ℕ} (j : ProductIndex Q) (N : ℕ) :
    complementCoefficient (reassemble j).1.val (reassemble j).2 N =
      productComplement j N := by
  let : NeZero ((reassemble j).1.val / (reassemble j).2.1.val) :=
    ⟨primitive_complement_ne_zero _ (reassemble j).2⟩
  have hsum := unitCharacterSum_nat_level_congr
    ((reassemble j).1.val / (reassemble j).2.1.val)
    j.val.2.2.val (quotient_reassemble j) N
  simp only [complementCoefficient, productComplement, hsum, quotient_reassemble]
  rfl

noncomputable def boundedTerm {Q : ℕ} (w : ℕ → ℂ) (N U : ℕ)
    (i : BoundedIndex Q) : ℂ :=
  w i.1.val * ((i.2.1.val : ℂ)/(i.2.1.val.totient : ℂ)) *
    complementCoefficient i.1.val i.2 N *
      i.2.2.val (N : ZMod i.2.1.val) *
        star (i.2.2.val (U : ZMod i.2.1.val))

/-- Insert the actual V116 expansion at every retained positive q.
The rough-input condition is explicit and is not inferred from the weight. -/
theorem weighted_ramanujan_eq_bounded_sum (Q N U : ℕ) (w : ℕ → ℂ)
    (hU : ∀ q : PositiveLevel Q, IsUnit (U : ZMod q.val)) :
    (∑ q : PositiveLevel Q, w q.val *
      unitCharacterSum q.val ((N : ZMod q.val)-(U : ZMod q.val))) =
      ∑ i : BoundedIndex Q, boundedTerm w N U i := by
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro q _
  rw [conjugate_factored_primitive_expansion q.val N (U : ZMod q.val) (hU q),
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [boundedTerm, ZMod.cast_natCast i.1.property]
  ring

/-- Actual weighted Ramanujan sum on the coupled r*l<=Q carrier.
The q weight is evaluated at the PRODUCT r*l without altering its support. -/
theorem weighted_ramanujan_product_expansion (Q N U : ℕ) (w : ℕ → ℂ)
    (hU : ∀ q : PositiveLevel Q, IsUnit (U : ZMod q.val)) :
    (∑ q : PositiveLevel Q, w q.val *
      unitCharacterSum q.val ((N : ZMod q.val)-(U : ZMod q.val))) =
      ∑ j : ProductIndex Q,
        w (j.val.1.val*j.val.2.2.val) *
          ((j.val.1.val : ℂ)/(j.val.1.val.totient : ℂ)) *
            productComplement j N * j.val.2.1.val (N : ZMod j.val.1.val) *
              star (j.val.2.1.val (U : ZMod j.val.1.val)) := by
  rw [weighted_ramanujan_eq_bounded_sum Q N U w hU,
    sum_bounded_conductor_reindex]
  apply Finset.sum_congr rfl
  intro j _
  dsimp only [boundedTerm]
  rw [complement_reassemble]
  rfl

end GoldbachCircleMethodBoundedConductorReindexV18117
