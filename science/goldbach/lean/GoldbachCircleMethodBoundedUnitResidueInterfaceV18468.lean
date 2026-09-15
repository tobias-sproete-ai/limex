import GoldbachCircleMethodFiniteCarrierStarCharacterEnergyV18467

/-!
# Goldbach V1.8.468: bounded unit-residue interface

The canonical unit residue is placed behind a named definition before the
collision theorem is instantiated.  This leaves the mathematics unchanged but
prevents repeated elaborator expansion of the nested subtype expression.
-/

set_option autoImplicit false
set_option maxHeartbeats 1800000

open scoped BigOperators Classical

namespace GoldbachCircleMethodBoundedUnitResidueInterfaceV18468

open GoldbachCircleMethodFiniteCarrierStarCharacterEnergyV18467
open GoldbachCircleMethodNonunitCharacterEnergyV18464
open GoldbachCircleMethodResidueCollisionEnergyV18463

noncomputable def boundedUnitResidue
    (q : ℕ) (I : Finset ℕ) (i : NaturalUnitIndex q I) : (ZMod q)ˣ :=
  naturalUnitResidue q I i

theorem boundedUnitResidue_eq
    (q : ℕ) (I : Finset ℕ) (i : NaturalUnitIndex q I) :
    boundedUnitResidue q I i = naturalUnitResidue q I i := by
  rfl

theorem bounded_unit_fiber_card_le
    (q L : ℕ) [NeZero q] (I : Finset ℕ)
    (hI : ∀ n ∈ I, n < L) (u : (ZMod q)ˣ) :
    Fintype.card {i : NaturalUnitIndex q I //
      boundedUnitResidue q I i = u} ≤ L / q + 1 := by
  unfold boundedUnitResidue
  exact natural_unit_fiber_card_le q L I hI u

noncomputable def boundedRetainedStarEnergy
    (q : ℕ) (I : Finset ℕ) (a : ↥I → ℂ)
    (P : DirichletCharacter ℂ q → Prop) [DecidablePred P] : ℝ :=
  ∑ chi ∈ (Finset.univ.filter P),
    ‖∑ i : NaturalUnitIndex q I,
      star (a i) * chi (boundedUnitResidue q I i : ZMod q)‖ ^ 2

theorem retained_eq_bounded
    (q : ℕ) (I : Finset ℕ) (a : ↥I → ℂ)
    (P : DirichletCharacter ℂ q → Prop) [DecidablePred P] :
    starredRetainedUnitEnergy q I a P =
      boundedRetainedStarEnergy q I a P := by
  unfold starredRetainedUnitEnergy boundedRetainedStarEnergy
  apply Finset.sum_congr rfl
  intro chi _hchi
  congr 3

end GoldbachCircleMethodBoundedUnitResidueInterfaceV18468
