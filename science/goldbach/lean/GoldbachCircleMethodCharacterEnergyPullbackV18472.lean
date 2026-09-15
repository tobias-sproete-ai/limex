import GoldbachCircleMethodConcreteUnitIndexEnergyV18471

/-!
# Goldbach V1.8.472: pullback to the literal finite carrier

The V1.8.471 collision bound is transported through the explicit equivalence
between the concrete and canonical unit-index carriers.  The final theorem is
the desired fixed-modulus estimate for arbitrary finite natural carriers below
`L`, including conjugated primitive-character sums.
-/

set_option autoImplicit false
set_option maxHeartbeats 1800000

open scoped BigOperators Classical

namespace GoldbachCircleMethodCharacterEnergyPullbackV18472

open GoldbachCircleMethodFiniteCarrierStarCharacterEnergyV18467
open GoldbachCircleMethodConcreteUnitIndexEnergyV18471

theorem retainedStarEnergy_eq_concrete
    (q : ℕ) (I : Finset ℕ) (a : ↥I → ℂ)
    (P : DirichletCharacter ℂ q → Prop) [DecidablePred P] :
    starredRetainedUnitEnergy q I a P =
      concreteRetainedStarEnergy q I a P := by
  unfold starredRetainedUnitEnergy concreteRetainedStarEnergy
  apply Finset.sum_congr rfl
  intro chi _hchi
  apply congrArg (fun z : ℂ => ‖z‖ ^ 2)
  apply Fintype.sum_equiv (concreteUnitIndexEquiv q I).symm
  intro i
  have hidx : ((concreteUnitIndexEquiv q I).symm i).index = i.val := rfl
  rw [hidx]
  congr 2

theorem concrete_coefficient_energy_eq_natural
    (q : ℕ) (I : Finset ℕ) (a : ↥I → ℂ) :
    (∑ i : ConcreteUnitIndex q I, ‖star (a i.index)‖ ^ 2) =
      ∑ i : NaturalUnitIndex q I, ‖a i‖ ^ 2 := by
  calc
    _ = ∑ i : NaturalUnitIndex q I, ‖star (a i)‖ ^ 2 := by
      apply Fintype.sum_equiv (concreteUnitIndexEquiv q I)
      intro i
      rfl
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _hi
      rw [norm_star]

theorem concrete_coefficient_energy_le_full
    (q : ℕ) (I : Finset ℕ) (a : ↥I → ℂ) :
    (∑ i : ConcreteUnitIndex q I, ‖star (a i.index)‖ ^ 2) ≤
      ∑ i : ↥I, ‖a i‖ ^ 2 := by
  calc
    _ = ∑ i : NaturalUnitIndex q I, ‖a i‖ ^ 2 :=
      concrete_coefficient_energy_eq_natural q I a
    _ ≤ ∑ i : ↥I, ‖a i‖ ^ 2 := by
      rw [← Finset.sum_subtype
        (Finset.univ.filter (fun i : ↥I => IsUnit (i.val : ZMod q)))
        (by simp) (fun i => ‖a i‖ ^ 2)]
      exact Finset.sum_le_univ_sum_of_nonneg (fun i => sq_nonneg ‖a i‖)

/-- Closed fixed-modulus estimate on the original carrier. -/
theorem conjugateCharacterEnergy_le
    (q L : ℕ) [NeZero q] (I : Finset ℕ)
    (hI : ∀ n ∈ I, n < L) (a : ↥I → ℂ)
    (P : DirichletCharacter ℂ q → Prop) [DecidablePred P] :
    conjugateCharacterEnergy q I a P ≤
      (q.totient : ℝ) * ((L / q + 1 : ℕ) : ℝ) *
        ∑ i : ↥I, ‖a i‖ ^ 2 := by
  calc
    conjugateCharacterEnergy q I a P =
        concreteRetainedStarEnergy q I a P :=
      ((conjugateCharacterEnergy_eq_full q I a P).trans
        (starredFullResidueEnergy_eq_retained q I a P)).trans
          (retainedStarEnergy_eq_concrete q I a P)
    _ ≤ (q.totient : ℝ) * ((L / q + 1 : ℕ) : ℝ) *
        ∑ i : ConcreteUnitIndex q I, ‖star (a i.index)‖ ^ 2 :=
      concreteRetainedStarEnergy_le q L I hI a P
    _ ≤ (q.totient : ℝ) * ((L / q + 1 : ℕ) : ℝ) *
        ∑ i : ↥I, ‖a i‖ ^ 2 := by
      have hC : 0 ≤ (q.totient : ℝ) * ((L / q + 1 : ℕ) : ℝ) := by
        positivity
      exact mul_le_mul_of_nonneg_left
        (concrete_coefficient_energy_le_full q I a) hC

end GoldbachCircleMethodCharacterEnergyPullbackV18472
