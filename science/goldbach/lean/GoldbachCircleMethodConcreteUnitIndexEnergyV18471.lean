import GoldbachCircleMethodActualPrimitiveSourceNormalizationV18470

/-!
# Goldbach V1.8.471: concrete unit-index energy carrier

Lean's elaborator repeatedly expanded the nested subtype used by the canonical
unit-index representation.  This module introduces an isomorphic named
structure.  Its equivalence to the canonical carrier is proved explicitly;
the character collision theorem can then be instantiated without changing any
index or coefficient.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

open scoped BigOperators Classical

namespace GoldbachCircleMethodConcreteUnitIndexEnergyV18471

open GoldbachCircleMethodFiniteCarrierStarCharacterEnergyV18467
open GoldbachCircleMethodResidueCollisionEnergyV18463

structure ConcreteUnitIndex (q : ℕ) (I : Finset ℕ) where
  index : ↥I
  isUnit : IsUnit (index.val : ZMod q)

noncomputable def concreteUnitIndexEquiv (q : ℕ) (I : Finset ℕ) :
    ConcreteUnitIndex q I ≃ NaturalUnitIndex q I where
  toFun i := ⟨i.index, i.isUnit⟩
  invFun i := ⟨i.val, i.property⟩
  left_inv i := by cases i; rfl
  right_inv i := by cases i; rfl

noncomputable instance concreteUnitIndexFintype (q : ℕ) (I : Finset ℕ) :
    Fintype (ConcreteUnitIndex q I) :=
  Fintype.ofEquiv (NaturalUnitIndex q I) (concreteUnitIndexEquiv q I).symm

noncomputable def concreteUnitResidue
    (q : ℕ) (I : Finset ℕ) (i : ConcreteUnitIndex q I) : (ZMod q)ˣ :=
  i.isUnit.unit

theorem concreteUnitResidue_compatible
    (q : ℕ) (I : Finset ℕ) (i : ConcreteUnitIndex q I) :
    naturalUnitResidue q I (concreteUnitIndexEquiv q I i) =
      concreteUnitResidue q I i := by
  rfl

theorem concrete_unit_fiber_card_le
    (q L : ℕ) [NeZero q] (I : Finset ℕ)
    (hI : ∀ n ∈ I, n < L) (u : (ZMod q)ˣ) :
    Fintype.card {i : ConcreteUnitIndex q I //
      concreteUnitResidue q I i = u} ≤ L / q + 1 := by
  let e :
      {i : ConcreteUnitIndex q I // concreteUnitResidue q I i = u} ≃
        {j : NaturalUnitIndex q I // naturalUnitResidue q I j = u} :=
    { toFun := fun i =>
        ⟨concreteUnitIndexEquiv q I i.val, by
          rw [concreteUnitResidue_compatible]
          exact i.property⟩
      invFun := fun j =>
        ⟨(concreteUnitIndexEquiv q I).symm j.val, by
          calc
            concreteUnitResidue q I ((concreteUnitIndexEquiv q I).symm j.val) =
                naturalUnitResidue q I
                  (concreteUnitIndexEquiv q I
                    ((concreteUnitIndexEquiv q I).symm j.val)) :=
              (concreteUnitResidue_compatible q I
                ((concreteUnitIndexEquiv q I).symm j.val)).symm
            _ = naturalUnitResidue q I j.val := by
              rw [(concreteUnitIndexEquiv q I).apply_symm_apply]
            _ = u := j.property⟩
      left_inv := by
        intro i
        apply Subtype.ext
        exact (concreteUnitIndexEquiv q I).symm_apply_apply i.val
      right_inv := by
        intro j
        apply Subtype.ext
        exact (concreteUnitIndexEquiv q I).apply_symm_apply j.val }
  rw [Fintype.card_congr e]
  exact natural_unit_fiber_card_le q L I hI u

noncomputable def concreteRetainedStarEnergy
    (q : ℕ) (I : Finset ℕ) (a : ↥I → ℂ)
    (P : DirichletCharacter ℂ q → Prop) [DecidablePred P] : ℝ :=
  ∑ chi ∈ (Finset.univ.filter P),
    ‖∑ i : ConcreteUnitIndex q I,
      star (a i.index) * chi (concreteUnitResidue q I i : ZMod q)‖ ^ 2

theorem concreteRetainedStarEnergy_le
    (q L : ℕ) [NeZero q] (I : Finset ℕ)
    (hI : ∀ n ∈ I, n < L) (a : ↥I → ℂ)
    (P : DirichletCharacter ℂ q → Prop) [DecidablePred P] :
    concreteRetainedStarEnergy q I a P ≤
      (q.totient : ℝ) * ((L / q + 1 : ℕ) : ℝ) *
        ∑ i : ConcreteUnitIndex q I, ‖star (a i.index)‖ ^ 2 := by
  unfold concreteRetainedStarEnergy
  exact filtered_character_energy_le_totient_mul_collision q
    (concreteUnitResidue q I)
    (fun i : ConcreteUnitIndex q I => star (a i.index)) (L / q + 1)
    (concrete_unit_fiber_card_le q L I hI) P

end GoldbachCircleMethodConcreteUnitIndexEnergyV18471
