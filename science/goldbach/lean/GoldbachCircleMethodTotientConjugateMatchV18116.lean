import GoldbachCircleMethodFullPrimitiveExpansionV18115
import Mathlib.NumberTheory.MulChar.Lemmas

set_option autoImplicit false
open scoped BigOperators Classical
open GoldbachCircleMethodFiniteResiduePrefixV1866
open GoldbachCircleMethodPrimitiveConductorRegroupingV18111
open GoldbachCircleMethodFullPrimitiveExpansionV18115

namespace GoldbachCircleMethodTotientConjugateMatchV18116

/-- On an actual unit, the residue inverse gives the complex-conjugate value.
No DivisionMonoid structure is assumed on a composite residue ring. -/
theorem unit_character_inverse_conjugate (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (u : ZMod q) (hu : IsUnit u) :
    χ u⁻¹ = star (χ u) := by
  obtain ⟨w, rfl⟩ := hu
  calc
    χ (w : ZMod q)⁻¹ = χ (Ring.inverse (w : ZMod q)) := by
      rw [ZMod.inv_coe_unit, Ring.inverse_unit]
    _ = χ⁻¹ (w : ZMod q) := (MulChar.inv_apply χ _).symm
    _ = star (χ (w : ZMod q)) := (MulChar.star_apply' χ _).symm

variable (q : ℕ) [NeZero q]

/-- Complex conjugation commutes with the actual primitive-parent pullback. -/
theorem primitive_parent_inverse_conjugate (i : PrimitiveIndex q)
    (u : ZMod q) (hu : IsUnit u) :
    i.2.val (ZMod.cast u⁻¹ : ZMod i.1.val) =
      star (i.2.val (ZMod.cast u : ZMod i.1.val)) := by
  rw [← liftIndex_at_inverse_unit q i u hu,
    unit_character_inverse_conjugate q (liftIndex i) u hu]
  have hc := DirichletCharacter.changeLevel_eq_cast_of_dvd i.2.val i.1.property hu.unit
  have hc' : (liftIndex i) u = i.2.val (ZMod.cast u : ZMod i.1.val) := by
    simpa only [liftIndex, hu.unit_spec] using hc
  rw [hc']

/-- The exact complement kernel, retaining coprimality and every Mobius zero. -/
noncomputable def complementCoefficient (i : PrimitiveIndex q) (N : ℕ) : ℂ :=
  let : NeZero (q / i.1.val) := ⟨primitive_complement_ne_zero q i⟩
  if Nat.Coprime i.1.val (q / i.1.val) then
    ((ArithmeticFunction.moebius (q / i.1.val) : ℤ) : ℂ) *
      unitCharacterSum (q / i.1.val) (N : ZMod (q / i.1.val)) /
        ((q / i.1.val).totient : ℂ)
  else 0

omit [NeZero q] in
/-- The conductor/complement totient factorization has its actual coprimality premise. -/
theorem index_totient_factorization (i : PrimitiveIndex q)
    (hcop : Nat.Coprime i.1.val (q / i.1.val)) :
    q.totient = i.1.val.totient * (q / i.1.val).totient := by
  calc
    q.totient = (i.1.val * (q / i.1.val)).totient :=
      congrArg Nat.totient (Nat.mul_div_cancel' i.1.property).symm
    _ = _ := Nat.totient_mul hcop

/-- Exact normalized coefficient, with r/phi(r) kept rather than dropped. -/
theorem primitiveCoefficient_div_totient (i : PrimitiveIndex q) (N : ℕ) :
    primitiveCoefficient q i N / (q.totient : ℂ) =
      ((i.1.val : ℂ)/(i.1.val.totient : ℂ)) *
        complementCoefficient q i N * i.2.val (N : ZMod i.1.val) := by
  dsimp only [primitiveCoefficient, complementCoefficient]
  by_cases hcop : Nat.Coprime i.1.val (q / i.1.val)
  · simp only [if_pos hcop]
    rw [index_totient_factorization q i hcop, Nat.cast_mul]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  · simp only [if_neg hcop,
      zero_div, mul_zero, zero_mul]

/-- The full finite formula now matches the conjugation and totient convention
of the analytic L_r coefficient, while still making no analytic estimate. -/
theorem conjugate_factored_primitive_expansion (N : ℕ) (u : ZMod q) (hu : IsUnit u) :
    unitCharacterSum q ((N : ZMod q)-u) =
      ∑ i : PrimitiveIndex q,
        ((i.1.val : ℂ)/(i.1.val.totient : ℂ)) *
          complementCoefficient q i N * i.2.val (N : ZMod i.1.val) *
            star (i.2.val (ZMod.cast u : ZMod i.1.val)) := by
  rw [normalized_primitive_parent_expansion q N u hu, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_div_assoc, primitiveCoefficient_div_totient q i N,
    primitive_parent_inverse_conjugate q i u hu]
  ring

end GoldbachCircleMethodTotientConjugateMatchV18116
