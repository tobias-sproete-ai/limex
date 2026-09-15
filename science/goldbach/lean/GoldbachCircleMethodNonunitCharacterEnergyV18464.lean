import GoldbachCircleMethodResidueCollisionEnergyV18463

/-!
# Goldbach V1.8.464: removal of nonunit character terms

Dirichlet characters vanish on nonunits.  This module turns that fact into an
exact finite adapter from arbitrary residues in `ZMod q` to the unit-residue
energy estimate of V1.8.463.  The fiber-cardinality estimate remains an
explicit premise and no interval geometry is asserted here.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

open scoped BigOperators Classical

namespace GoldbachCircleMethodNonunitCharacterEnergyV18464

open GoldbachCircleMethodResidueCollisionEnergyV18463

variable (q : ℕ)

/-- The finite subtype of indices whose residue is a unit modulo `q`. -/
abbrev UnitIndex {ι : Type*} (z : ι → ZMod q) :=
  {i : ι // IsUnit (z i)}

/-- Canonical unit residue attached to an index in `UnitIndex`. -/
noncomputable def unitResidueOf
    {ι : Type*} (z : ι → ZMod q) (i : UnitIndex q z) : (ZMod q)ˣ :=
  i.property.unit

theorem coe_unitResidueOf
    {ι : Type*} (z : ι → ZMod q) (i : UnitIndex q z) :
    ((unitResidueOf q z i : (ZMod q)ˣ) : ZMod q) = z i := by
  exact i.property.unit_spec

/-- Exact deletion of nonunit terms from a finite Dirichlet-character sum. -/
theorem character_sum_eq_unit_subtype
    {ι : Type*} [Fintype ι] (z : ι → ZMod q) (a : ι → ℂ)
    (chi : DirichletCharacter ℂ q) :
    (∑ i : ι, a i * chi (z i)) =
      ∑ i : UnitIndex q z, a i * chi (z i) := by
  classical
  rw [← Finset.sum_subtype (Finset.univ.filter (fun i => IsUnit (z i)))
    (by simp) (fun i => a i * chi (z i))]
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro i _hi hnot
  have hnonunit : ¬IsUnit (z i) := by
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hnot
  rw [chi.map_nonunit hnonunit, mul_zero]

/-- Exact unit-valued reformulation of the retained character sum. -/
theorem character_sum_eq_unit_residues
    {ι : Type*} [Fintype ι] (z : ι → ZMod q) (a : ι → ℂ)
    (chi : DirichletCharacter ℂ q) :
    (∑ i : ι, a i * chi (z i)) =
      ∑ i : UnitIndex q z,
        a i * chi (unitResidueOf q z i : ZMod q) := by
  rw [character_sum_eq_unit_subtype q z a chi]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [coe_unitResidueOf q z i]

/-- Character energy before deleting nonunit residues.  The definition keeps
the expensive dependent subtype out of downstream theorem signatures. -/
noncomputable def fullResidueCharacterEnergy
    {ι : Type*} [Fintype ι]
    (z : ι → ZMod q) (a : ι → ℂ)
    (P : DirichletCharacter ℂ q → Prop) [DecidablePred P] : ℝ :=
  ∑ chi ∈ (Finset.univ.filter P), ‖∑ i : ι, a i * chi (z i)‖ ^ 2

/-- The same energy after exact restriction to unit residues. -/
noncomputable def retainedUnitCharacterEnergy
    {ι : Type*} [Fintype ι]
    (z : ι → ZMod q) (aUnit : UnitIndex q z → ℂ)
    (P : DirichletCharacter ℂ q → Prop) [DecidablePred P] : ℝ :=
  ∑ chi ∈ (Finset.univ.filter P),
    ‖∑ i : UnitIndex q z,
      aUnit i * chi (unitResidueOf q z i : ZMod q)‖ ^ 2

/-- Deleting nonunit residues preserves the entire filtered character energy. -/
theorem fullResidueCharacterEnergy_eq_retained
    {ι : Type*} [Fintype ι]
    (z : ι → ZMod q) (a : ι → ℂ)
    (P : DirichletCharacter ℂ q → Prop) [DecidablePred P] :
    fullResidueCharacterEnergy q z a P =
      retainedUnitCharacterEnergy q z (fun i => a i) P := by
  unfold fullResidueCharacterEnergy retainedUnitCharacterEnergy
  apply Finset.sum_congr rfl
  intro chi _hchi
  exact congrArg (fun x : ℂ => ‖x‖ ^ 2)
    (character_sum_eq_unit_residues q z a chi)

end GoldbachCircleMethodNonunitCharacterEnergyV18464
