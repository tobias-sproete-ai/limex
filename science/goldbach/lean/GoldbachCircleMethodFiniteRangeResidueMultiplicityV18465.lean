import GoldbachCircleMethodNonunitCharacterEnergyV18464

/-!
# Goldbach V1.8.465: finite range residue multiplicity

For a nonzero modulus, a fixed residue occurs at most `L / q + 1` times among
the natural numbers below `L`.  The proof embeds the residue fiber into the
quotient coordinate `n / q`; no asymptotic estimate is used.  A second theorem
transfers the bound to any finite carrier contained in `range L`, including the
actual centered-window carrier used later.
-/

set_option autoImplicit false

open scoped Classical

namespace GoldbachCircleMethodFiniteRangeResidueMultiplicityV18465

open GoldbachCircleMethodNonunitCharacterEnergyV18464

/-- A fixed `ZMod q` residue below `L` has at most `L / q + 1` representatives. -/
theorem fin_residue_fiber_card_le (q L : ℕ) [NeZero q] (v : ZMod q) :
    Fintype.card {i : Fin L // (i.val : ZMod q) = v} ≤ L / q + 1 := by
  let e : {i : Fin L // (i.val : ZMod q) = v} ↪ Fin (L / q + 1) :=
    { toFun := fun i =>
        ⟨i.val.val / q, Nat.lt_succ_iff.mpr
          (Nat.div_le_div_right i.val.isLt.le)⟩
      inj' := by
        intro x y hxy
        have hdiv : x.val.val / q = y.val.val / q :=
          congrArg Fin.val hxy
        have hmod : x.val.val % q = y.val.val % q := by
          exact (ZMod.natCast_eq_natCast_iff'
            x.val.val y.val.val q).mp (x.property.trans y.property.symm)
        apply Subtype.ext
        apply Fin.ext
        calc
          x.val.val = q * (x.val.val / q) + x.val.val % q :=
            (Nat.div_add_mod x.val.val q).symm
          _ = q * (y.val.val / q) + y.val.val % q := by rw [hdiv, hmod]
          _ = y.val.val := Nat.div_add_mod y.val.val q }
  simpa using Fintype.card_le_of_embedding e

/-- Any finite natural carrier lying below `L` inherits the same bound on each
unit-residue fiber. -/
theorem finset_unit_fiber_card_le
    (q L : ℕ) [NeZero q] (I : Finset ℕ)
    (hI : ∀ n ∈ I, n < L) (u : (ZMod q)ˣ) :
    Fintype.card
        {i : UnitIndex q (fun n : ↥I => (n.val : ZMod q)) //
          unitResidueOf q (fun n : ↥I => (n.val : ZMod q)) i = u} ≤
      L / q + 1 := by
  let z : ↥I → ZMod q := fun n => (n.val : ZMod q)
  let e :
      {i : UnitIndex q z // unitResidueOf q z i = u} ↪
        {j : Fin L // (j.val : ZMod q) = (u : ZMod q)} :=
    { toFun := fun i =>
        ⟨⟨i.val.val.val, hI i.val.val.val i.val.val.property⟩, by
          calc
            (i.val.val.val : ZMod q) =
                (unitResidueOf q z i.val : ZMod q) :=
              (coe_unitResidueOf q z i.val).symm
            _ = (u : ZMod q) := by rw [i.property]⟩
      inj' := by
        intro x y hxy
        apply Subtype.ext
        apply Subtype.ext
        apply Subtype.ext
        exact congrArg (fun t => t.val.val) hxy }
  exact (Fintype.card_le_of_embedding e).trans
    (fin_residue_fiber_card_le q L (u : ZMod q))

end GoldbachCircleMethodFiniteRangeResidueMultiplicityV18465
