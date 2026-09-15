import GoldbachCircleMethodPrimitiveBasePolynomialEnvelopeV18475

/-!
# Goldbach V1.8.476: window-span residue multiplicity

The collision count is sharpened from the whole dyadic block to the literal
integer span of the centered window.  This is the counting gain required by
the central energy argument.
-/

set_option autoImplicit false

open scoped Classical

namespace GoldbachCircleMethodWindowSpanResidueMultiplicityV18476

open GoldbachCircleMethodNonunitCharacterEnergyV18464
open GoldbachCircleMethodActualWindowInputEnergyV18469
open GoldbachCircleMethodExactPrincipalBoundaryCostV18126

/-- A fixed residue in any finite carrier contained in `[A,A+D]` occurs at
most `D/q+1` times. -/
theorem finset_unit_fiber_card_le_span
    (q A D : ℕ) [NeZero q] (I : Finset ℕ)
    (hI : ∀ n ∈ I, A ≤ n ∧ n ≤ A + D) (u : (ZMod q)ˣ) :
    Fintype.card
        {i : UnitIndex q (fun n : ↑I => (n.val : ZMod q)) //
          unitResidueOf q (fun n : ↑I => (n.val : ZMod q)) i = u} ≤
      D / q + 1 := by
  let z : ↑I → ZMod q := fun n => (n.val : ZMod q)
  let e :
      {i : UnitIndex q z // unitResidueOf q z i = u} ↪
        Fin (D / q + 1) :=
    { toFun := fun i =>
        ⟨(i.val.val.val - A) / q, Nat.lt_succ_iff.mpr
          (Nat.div_le_div_right (by
            have hi := hI i.val.val.val i.val.val.property
            omega))⟩
      inj' := by
        intro x y hxy
        have hxI := hI x.val.val.val x.val.val.property
        have hyI := hI y.val.val.val y.val.val.property
        have hdiv : (x.val.val.val - A) / q = (y.val.val.val - A) / q :=
          congrArg Fin.val hxy
        have hcast : (x.val.val.val : ZMod q) = (y.val.val.val : ZMod q) := by
          calc
            (x.val.val.val : ZMod q) =
                (unitResidueOf q z x.val : ZMod q) :=
              (coe_unitResidueOf q z x.val).symm
            _ = (u : ZMod q) := by rw [x.property]
            _ = (unitResidueOf q z y.val : ZMod q) := by rw [y.property]
            _ = (y.val.val.val : ZMod q) :=
              coe_unitResidueOf q z y.val
        have hsubcast : ((x.val.val.val - A : ℕ) : ZMod q) =
            ((y.val.val.val - A : ℕ) : ZMod q) := by
          rw [Nat.cast_sub hxI.1, Nat.cast_sub hyI.1, hcast]
        have hmod : (x.val.val.val - A) % q = (y.val.val.val - A) % q :=
          (ZMod.natCast_eq_natCast_iff'
            (x.val.val.val - A) (y.val.val.val - A) q).mp hsubcast
        apply Subtype.ext
        apply Subtype.ext
        apply Subtype.ext
        have hsub : x.val.val.val - A = y.val.val.val - A := by
          calc
            x.val.val.val - A =
                q * ((x.val.val.val - A) / q) + (x.val.val.val - A) % q :=
              (Nat.div_add_mod (x.val.val.val - A) q).symm
            _ = q * ((y.val.val.val - A) / q) + (y.val.val.val - A) % q := by
              rw [hdiv, hmod]
            _ = y.val.val.val - A := Nat.div_add_mod (y.val.val.val - A) q
        omega }
  simpa only [z, Fintype.card_fin] using Fintype.card_le_of_embedding e

/-- The actual centered window inherits the span bound `2*floor(H)`. -/
theorem actualWindow_unit_fiber_card_le_span
    (q B N : ℕ) [NeZero q] (H : ℝ) (hH : 0 ≤ H)
    (u : (ZMod q)ˣ) :
    Fintype.card
        {i : UnitIndex q
            (fun n : ↑(actualWindowCarrier B N H) => (n.val : ZMod q)) //
          unitResidueOf q
            (fun n : ↑(actualWindowCarrier B N H) => (n.val : ZMod q)) i = u} ≤
      (2 * ⌊H⌋₊) / q + 1 := by
  apply finset_unit_fiber_card_le_span q (N - ⌊H⌋₊) (2 * ⌊H⌋₊)
    (actualWindowCarrier B N H) _ u
  intro n hn
  have hdist := (abs_sub_le_iff_floor N n H hH).mp
    ((GoldbachCircleMethodFiniteWindowConvolutionV18119.mem_centeredWindow
      (GoldbachCircleMethodLogCutoffPresieveBindingV18120.blockCarrier B)
      N n H).mp hn).2
  omega

end GoldbachCircleMethodWindowSpanResidueMultiplicityV18476
