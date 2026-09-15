import GoldbachCircleMethodFiniteRangeResidueMultiplicityV18465

/-!
# Goldbach V1.8.466: conjugate-character energy adapter

The actual centered source contains `star (chi z)` rather than `chi z`.
Complex conjugation transfers that finite sum to the ordinary character form
without changing its norm.  This is an exact algebraic identity, not a
distribution estimate.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodConjugateCharacterEnergyV18466

/-- Conjugating every coefficient turns a conjugated-character sum into the
ordinary character sum, with exactly the same norm. -/
theorem norm_sum_mul_star_character_eq
    (q : ℕ) {ι : Type*} [Fintype ι]
    (z : ι → ZMod q) (a : ι → ℂ) (chi : DirichletCharacter ℂ q) :
    ‖∑ i : ι, a i * star (chi (z i))‖ =
      ‖∑ i : ι, star (a i) * chi (z i)‖ := by
  calc
    ‖∑ i : ι, a i * star (chi (z i))‖ =
        ‖star (∑ i : ι, a i * star (chi (z i)))‖ :=
      (norm_star _).symm
    _ = ‖∑ i : ι, star (a i) * chi (z i)‖ := by
      congr 1
      change (starRingEnd ℂ) (∑ i : ι, a i * star (chi (z i))) = _
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro i _hi
      simp

/-- The exact norm identity survives summation over any finite filtered
character family. -/
theorem filtered_star_character_energy_eq
    (q : ℕ) {ι : Type*} [Fintype ι]
    (z : ι → ZMod q) (a : ι → ℂ)
    (P : DirichletCharacter ℂ q → Prop) [DecidablePred P] :
    (∑ chi ∈ (Finset.univ.filter P),
        ‖∑ i : ι, a i * star (chi (z i))‖ ^ 2) =
      ∑ chi ∈ (Finset.univ.filter P),
        ‖∑ i : ι, star (a i) * chi (z i)‖ ^ 2 := by
  apply Finset.sum_congr rfl
  intro chi _hchi
  rw [norm_sum_mul_star_character_eq q z a chi]

end GoldbachCircleMethodConjugateCharacterEnergyV18466
