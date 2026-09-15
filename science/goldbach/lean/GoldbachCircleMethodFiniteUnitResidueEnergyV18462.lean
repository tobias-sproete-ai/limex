import GoldbachCircleMethodFullCharacterUnitEnergyV18461

/-!
# Goldbach V1.8.462: finite coefficients grouped by unit residue classes

This module transports the exact full-character energy bound from coefficient
families on `(ZMod q)ˣ` to an arbitrary finite coefficient family equipped with
a map into the unit residue classes.  The regrouping is an exact finite
identity.  No interval multiplicity estimate, arithmetic distribution estimate
or Goldbach conclusion is asserted.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodFiniteUnitResidueEnergyV18462

open GoldbachCircleMethodFullCharacterUnitParsevalV18460
open GoldbachCircleMethodFullCharacterUnitEnergyV18461

variable (q : ℕ) [NeZero q]

/-- Aggregate a finite coefficient family over one unit residue class. -/
noncomputable def unitResidueAggregate
    {ι : Type*} [Fintype ι] (r : ι → (ZMod q)ˣ) (a : ι → ℂ)
    (u : (ZMod q)ˣ) : ℂ :=
  ∑ i : {i : ι // r i = u}, a i

/-- Exact regrouping of a finite character sum by its unit residue classes. -/
theorem unitCharacterTransform_aggregate_eq
    {ι : Type*} [Fintype ι] (r : ι → (ZMod q)ˣ) (a : ι → ℂ)
    (chi : DirichletCharacter ℂ q) :
    unitCharacterTransform q (unitResidueAggregate q r a) chi =
      ∑ i : ι, a i * chi (r i : ZMod q) := by
  unfold unitCharacterTransform unitResidueAggregate
  rw [← Fintype.sum_fiberwise r
    (fun i : ι => a i * chi (r i : ZMod q))]
  apply Finset.sum_congr rfl
  intro u _hu
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [i.property]

/-- Any decidable character subfamily is controlled by the exact energy of the
unit-residue aggregates.  In particular this applies to primitive character
slots without a crude count of those slots. -/
theorem filtered_finite_unit_character_energy_le
    {ι : Type*} [Fintype ι] (r : ι → (ZMod q)ˣ) (a : ι → ℂ)
    (P : DirichletCharacter ℂ q → Prop) [DecidablePred P] :
    (∑ chi ∈ (Finset.univ.filter P),
        ‖∑ i : ι, a i * chi (r i : ZMod q)‖ ^ 2) ≤
      (q.totient : ℝ) *
        ∑ u : (ZMod q)ˣ, ‖unitResidueAggregate q r a u‖ ^ 2 := by
  simpa only [unitCharacterTransform_aggregate_eq q r a] using
    filtered_character_unit_energy_le q (unitResidueAggregate q r a) P

end GoldbachCircleMethodFiniteUnitResidueEnergyV18462
