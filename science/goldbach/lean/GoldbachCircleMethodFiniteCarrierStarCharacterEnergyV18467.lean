import GoldbachCircleMethodConjugateCharacterEnergyV18466

/-!
# Goldbach V1.8.467: finite natural-carrier conjugate character energy

This module composes four already isolated finite facts: conjugation preserves
the character-sum norm, Dirichlet characters delete nonunit residues, unit
residue aggregates satisfy character Parseval, and an interval below `L` has
at most `L / q + 1` representatives in one residue class.  No prime
distribution estimate enters.
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000

open scoped BigOperators Classical

namespace GoldbachCircleMethodFiniteCarrierStarCharacterEnergyV18467

open GoldbachCircleMethodConjugateCharacterEnergyV18466
open GoldbachCircleMethodNonunitCharacterEnergyV18464
open GoldbachCircleMethodResidueCollisionEnergyV18463
open GoldbachCircleMethodFiniteRangeResidueMultiplicityV18465

abbrev NaturalUnitIndex (q : ℕ) (I : Finset ℕ) :=
  UnitIndex q (fun n : ↥I => (n.val : ZMod q))

noncomputable abbrev naturalUnitResidue
    (q : ℕ) (I : Finset ℕ) (i : NaturalUnitIndex q I) : (ZMod q)ˣ :=
  unitResidueOf q (fun n : ↥I => (n.val : ZMod q)) i

noncomputable def conjugateCharacterEnergy
    (q : ℕ) (I : Finset ℕ) (a : ↥I → ℂ)
    (P : DirichletCharacter ℂ q → Prop) [DecidablePred P] : ℝ :=
  ∑ chi ∈ (Finset.univ.filter P),
    ‖∑ i : ↥I, a i * star (chi (i.val : ZMod q))‖ ^ 2

noncomputable def starredFullResidueEnergy
    (q : ℕ) (I : Finset ℕ) (a : ↥I → ℂ)
    (P : DirichletCharacter ℂ q → Prop) [DecidablePred P] : ℝ :=
  fullResidueCharacterEnergy q (fun i : ↥I => (i.val : ZMod q))
    (fun i => star (a i)) P

noncomputable def starredRetainedUnitEnergy
    (q : ℕ) (I : Finset ℕ) (a : ↥I → ℂ)
    (P : DirichletCharacter ℂ q → Prop) [DecidablePred P] : ℝ :=
  ∑ chi ∈ (Finset.univ.filter P),
    ‖∑ i : NaturalUnitIndex q I,
      star (a i) * chi (naturalUnitResidue q I i : ZMod q)‖ ^ 2

theorem conjugateCharacterEnergy_eq_full
    (q : ℕ) (I : Finset ℕ) (a : ↥I → ℂ)
    (P : DirichletCharacter ℂ q → Prop) [DecidablePred P] :
    conjugateCharacterEnergy q I a P =
      starredFullResidueEnergy q I a P := by
  unfold conjugateCharacterEnergy starredFullResidueEnergy
  rw [filtered_star_character_energy_eq q
    (fun i : ↥I => (i.val : ZMod q)) a P]
  rfl

theorem starredFullResidueEnergy_eq_retained
    (q : ℕ) (I : Finset ℕ) (a : ↥I → ℂ)
    (P : DirichletCharacter ℂ q → Prop) [DecidablePred P] :
    starredFullResidueEnergy q I a P =
      starredRetainedUnitEnergy q I a P := by
  unfold starredFullResidueEnergy starredRetainedUnitEnergy
  exact fullResidueCharacterEnergy_eq_retained q
    (fun i : ↥I => (i.val : ZMod q)) (fun i => star (a i)) P

theorem natural_unit_fiber_card_le
    (q L : ℕ) [NeZero q] (I : Finset ℕ)
    (hI : ∀ n ∈ I, n < L) (u : (ZMod q)ˣ) :
    Fintype.card {i : NaturalUnitIndex q I //
      naturalUnitResidue q I i = u} ≤ L / q + 1 := by
  exact finset_unit_fiber_card_le q L I hI u

theorem unit_coefficient_energy_le
    (q : ℕ) (I : Finset ℕ) (a : ↥I → ℂ) :
    (∑ i : NaturalUnitIndex q I, ‖a i‖ ^ 2) ≤
      ∑ i : ↥I, ‖a i‖ ^ 2 := by
  rw [← Finset.sum_subtype
    (Finset.univ.filter (fun i : ↥I => IsUnit (i.val : ZMod q)))
    (by simp) (fun i => ‖a i‖ ^ 2)]
  exact Finset.sum_le_univ_sum_of_nonneg (fun i => sq_nonneg ‖a i‖)

end GoldbachCircleMethodFiniteCarrierStarCharacterEnergyV18467
