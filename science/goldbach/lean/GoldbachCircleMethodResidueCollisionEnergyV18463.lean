import GoldbachCircleMethodFiniteUnitResidueEnergyV18462

/-!
# Goldbach V1.8.463: collision-multiplicity energy bound

The squared energy of residue-class aggregates is bounded by the largest fiber
cardinality times the original coefficient energy.  This is a finite
Cauchy--Schwarz statement and is independent of any number-theoretic estimate.
The sharp interval-specific fiber-cardinality bound remains a later adapter.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodResidueCollisionEnergyV18463

open GoldbachCircleMethodFiniteUnitResidueEnergyV18462

/-- One fiber aggregate obeys finite Cauchy--Schwarz with its exact cardinality. -/
theorem fiber_aggregate_norm_sq_le_card_mul_energy
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (r : ι → κ) (a : ι → ℂ) (u : κ) :
    ‖∑ i : {i : ι // r i = u}, a i‖ ^ 2 ≤
      (Fintype.card {i : ι // r i = u} : ℝ) *
        ∑ i : {i : ι // r i = u}, ‖a i‖ ^ 2 := by
  let F := {i : ι // r i = u}
  have hnorm :
      ‖∑ i : F, a i‖ ≤ ∑ i : F, ‖a i‖ := norm_sum_le _ _
  have hleft : 0 ≤ ‖∑ i : F, a i‖ := norm_nonneg _
  have hright : 0 ≤ ∑ i : F, ‖a i‖ :=
    Finset.sum_nonneg (fun i _hi => norm_nonneg _)
  have hsq : ‖∑ i : F, a i‖ ^ 2 ≤ (∑ i : F, ‖a i‖) ^ 2 :=
    (sq_le_sq₀ hleft hright).mpr hnorm
  apply hsq.trans
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun _i : F => (1 : ℝ)) (fun i : F => ‖a i‖)
  simpa [F] using hcs

/-- If every residue fiber has cardinality at most `K`, the total aggregate
energy is at most `K` times the original coefficient energy. -/
theorem residue_aggregate_energy_le_of_fiber_card_le
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (r : ι → κ) (a : ι → ℂ) (K : ℕ)
    (hcard : ∀ u : κ, Fintype.card {i : ι // r i = u} ≤ K) :
    (∑ u : κ, ‖∑ i : {i : ι // r i = u}, a i‖ ^ 2) ≤
      (K : ℝ) * ∑ i : ι, ‖a i‖ ^ 2 := by
  calc
    _ ≤ ∑ u : κ, (K : ℝ) *
        ∑ i : {i : ι // r i = u}, ‖a i‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro u _hu
      refine (fiber_aggregate_norm_sq_le_card_mul_energy r a u).trans ?_
      have hcard_real :
          (Fintype.card {i : ι // r i = u} : ℝ) ≤ (K : ℝ) := by
        exact_mod_cast hcard u
      exact mul_le_mul_of_nonneg_right hcard_real
        (Finset.sum_nonneg (fun i _hi => sq_nonneg ‖a i‖))
    _ = (K : ℝ) * ∑ u : κ,
        ∑ i : {i : ι // r i = u}, ‖a i‖ ^ 2 := by
      rw [Finset.mul_sum]
    _ = _ := by
      rw [Fintype.sum_fiberwise r (fun i : ι => ‖a i‖ ^ 2)]

/-- Combined character-orthogonality and collision-multiplicity estimate for an
arbitrary finite family mapped into unit residues. -/
theorem filtered_character_energy_le_totient_mul_collision
    (q : ℕ) [NeZero q]
    {ι : Type*} [Fintype ι]
    (r : ι → (ZMod q)ˣ) (a : ι → ℂ) (K : ℕ)
    (hcard : ∀ u : (ZMod q)ˣ, Fintype.card {i : ι // r i = u} ≤ K)
    (P : DirichletCharacter ℂ q → Prop) [DecidablePred P] :
    (∑ chi ∈ (Finset.univ.filter P),
        ‖∑ i : ι, a i * chi (r i : ZMod q)‖ ^ 2) ≤
      (q.totient : ℝ) * (K : ℝ) * ∑ i : ι, ‖a i‖ ^ 2 := by
  calc
    _ ≤ (q.totient : ℝ) *
        ∑ u : (ZMod q)ˣ, ‖unitResidueAggregate q r a u‖ ^ 2 :=
      filtered_finite_unit_character_energy_le q r a P
    _ ≤ (q.totient : ℝ) * ((K : ℝ) * ∑ i : ι, ‖a i‖ ^ 2) := by
      apply mul_le_mul_of_nonneg_left
      · simpa only [unitResidueAggregate] using
          residue_aggregate_energy_le_of_fiber_card_le r a K hcard
      · positivity
    _ = _ := by ring

end GoldbachCircleMethodResidueCollisionEnergyV18463
