import GoldbachCircleMethodCollisionLiteralSliceEnergyV18551

/-!
# Goldbach V1.8.552: total literal collision-block energy

The actual collision branch is bounded by one finite energy over the unchanged
target and primitive-character carriers.  V1.8.551 contributes the single
product-denominator factor `Q`; the remaining factors are exact carrier
cardinalities.  No energy decay or absorptivity is asserted.
-/

set_option autoImplicit false

open scoped BigOperators Classical ComplexConjugate

namespace GoldbachCircleMethodCollisionLiteralBlockEnergyV18552

open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodCollisionLiteralSliceEnergyV18551
open GoldbachCircleMethodCrossDenominatorCollisionPartitionV18547
open GoldbachCircleMethodLogCutoffPresieveBindingV18120

/-- Exact weighted energy of all collision slices in one conductor pair. -/
noncomputable def collisionLiteralBlockEnergy
    (Q B : ℕ) (H : ℝ) (w : ℕ → ℂ)
    (r s : PositiveLevel Q) : ℝ :=
  ∑ N ∈ blockCarrier B,
    ∑ ψ : {ψ : DirichletCharacter ℂ s.val // ψ.IsPrimitive},
      ∑ χ : {χ : DirichletCharacter ℂ r.val // χ.IsPrimitive},
        collisionLiteralSliceEnergy B N H w r s χ ψ

/-- Finite Cauchy--Schwarz over one explicit carrier and two finite type
carriers. -/
theorem nested_three_sum_sq_le_card_mul_energy
    {ι κ τ : Type*} [DecidableEq ι] [Fintype κ] [Fintype τ]
    (J : Finset ι) (a : ι → κ → τ → ℝ) :
    (∑ i ∈ J, ∑ j : κ, ∑ k : τ, a i j k) ^ 2 ≤
      (J.card : ℝ) * (Fintype.card κ : ℝ) * (Fintype.card τ : ℝ) *
        ∑ i ∈ J, ∑ j : κ, ∑ k : τ, (a i j k) ^ 2 := by
  have hτ (i : ι) (j : κ) :
      (∑ k : τ, a i j k) ^ 2 ≤
        (Fintype.card τ : ℝ) * ∑ k : τ, (a i j k) ^ 2 := by
    simpa only [Finset.card_univ] using
      (sq_sum_le_card_mul_sum_sq
        (s := (Finset.univ : Finset τ)) (f := fun k => a i j k))
  have hκ (i : ι) :
      (∑ j : κ, ∑ k : τ, a i j k) ^ 2 ≤
        (Fintype.card κ : ℝ) * (Fintype.card τ : ℝ) *
          ∑ j : κ, ∑ k : τ, (a i j k) ^ 2 := by
    have hcs := sq_sum_le_card_mul_sum_sq
      (s := (Finset.univ : Finset κ))
      (f := fun j => ∑ k : τ, a i j k)
    calc
      _ ≤ (Fintype.card κ : ℝ) *
          ∑ j : κ, (∑ k : τ, a i j k) ^ 2 := by
        simpa only [Finset.card_univ] using hcs
      _ ≤ (Fintype.card κ : ℝ) *
          ∑ j : κ, (Fintype.card τ : ℝ) *
            ∑ k : τ, (a i j k) ^ 2 := by
        apply mul_le_mul_of_nonneg_left
        · exact Finset.sum_le_sum fun j _hj => hτ i j
        · positivity
      _ = (Fintype.card κ : ℝ) * (Fintype.card τ : ℝ) *
          ∑ j : κ, ∑ k : τ, (a i j k) ^ 2 := by
        simp_rw [← Finset.mul_sum]
        ring
  have houter := sq_sum_le_card_mul_sum_sq
    (s := J) (f := fun i => ∑ j : κ, ∑ k : τ, a i j k)
  calc
    _ ≤ (J.card : ℝ) *
        ∑ i ∈ J, (∑ j : κ, ∑ k : τ, a i j k) ^ 2 := houter
    _ ≤ (J.card : ℝ) *
        ∑ i ∈ J, (Fintype.card κ : ℝ) * (Fintype.card τ : ℝ) *
          ∑ j : κ, ∑ k : τ, (a i j k) ^ 2 := by
      apply mul_le_mul_of_nonneg_left
      · exact Finset.sum_le_sum fun i _hi => hκ i
      · positivity
    _ = (J.card : ℝ) * (Fintype.card κ : ℝ) *
        (Fintype.card τ : ℝ) *
          ∑ i ∈ J, ∑ j : κ, ∑ k : τ, (a i j k) ^ 2 := by
      simp_rw [← Finset.mul_sum]
      ring

/-- The total actual collision block is controlled by its exact weighted
energy.  Product-denominator sparsity costs only one factor `Q`; no second
complement-carrier factor is introduced. -/
theorem collisionLiteralCrossBlockCorrelation_sq_le_energy
    (Q B : ℕ) (H : ℝ) (w : ℕ → ℂ)
    (r s : PositiveLevel Q) :
    (collisionLiteralCrossBlockCorrelation Q B H w r s) ^ 2 ≤
      (blockCarrier B).card *
        (Fintype.card {ψ : DirichletCharacter ℂ s.val // ψ.IsPrimitive} : ℝ) *
        (Fintype.card {χ : DirichletCharacter ℂ r.val // χ.IsPrimitive} : ℝ) *
        (Q : ℝ) * collisionLiteralBlockEnergy Q B H w r s := by
  rw [collisionLiteralCrossBlockCorrelation_eq_sum_slices]
  have houter := nested_three_sum_sq_le_card_mul_energy
    (blockCarrier B)
    (fun N
      (ψ : {ψ : DirichletCharacter ℂ s.val // ψ.IsPrimitive})
      (χ : {χ : DirichletCharacter ℂ r.val // χ.IsPrimitive}) =>
        collisionLiteralSlice B N H w r s χ ψ)
  have hslices :
      (∑ N ∈ blockCarrier B,
        ∑ ψ : {ψ : DirichletCharacter ℂ s.val // ψ.IsPrimitive},
          ∑ χ : {χ : DirichletCharacter ℂ r.val // χ.IsPrimitive},
            (collisionLiteralSlice B N H w r s χ ψ) ^ 2) ≤
      (Q : ℝ) * collisionLiteralBlockEnergy Q B H w r s := by
    unfold collisionLiteralBlockEnergy
    calc
      _ ≤ ∑ N ∈ blockCarrier B,
          ∑ ψ : {ψ : DirichletCharacter ℂ s.val // ψ.IsPrimitive},
            ∑ χ : {χ : DirichletCharacter ℂ r.val // χ.IsPrimitive},
              (Q : ℝ) * collisionLiteralSliceEnergy B N H w r s χ ψ := by
        apply Finset.sum_le_sum
        intro N _hN
        apply Finset.sum_le_sum
        intro ψ _hψ
        apply Finset.sum_le_sum
        intro χ _hχ
        exact collisionLiteralSlice_sq_le_cutoff_mul_energy B N H w r s χ ψ
      _ = (Q : ℝ) *
          ∑ N ∈ blockCarrier B,
            ∑ ψ : {ψ : DirichletCharacter ℂ s.val // ψ.IsPrimitive},
              ∑ χ : {χ : DirichletCharacter ℂ r.val // χ.IsPrimitive},
                collisionLiteralSliceEnergy B N H w r s χ ψ := by
        simp only [Finset.mul_sum]
  have hfactor : 0 ≤
      (blockCarrier B).card *
        (Fintype.card {ψ : DirichletCharacter ℂ s.val // ψ.IsPrimitive} : ℝ) *
        (Fintype.card {χ : DirichletCharacter ℂ r.val // χ.IsPrimitive} : ℝ) := by
    positivity
  calc
    _ ≤ (blockCarrier B).card *
        (Fintype.card {ψ : DirichletCharacter ℂ s.val // ψ.IsPrimitive} : ℝ) *
        (Fintype.card {χ : DirichletCharacter ℂ r.val // χ.IsPrimitive} : ℝ) *
        (∑ N ∈ blockCarrier B,
          ∑ ψ : {ψ : DirichletCharacter ℂ s.val // ψ.IsPrimitive},
            ∑ χ : {χ : DirichletCharacter ℂ r.val // χ.IsPrimitive},
              (collisionLiteralSlice B N H w r s χ ψ) ^ 2) := houter
    _ ≤ (blockCarrier B).card *
        (Fintype.card {ψ : DirichletCharacter ℂ s.val // ψ.IsPrimitive} : ℝ) *
        (Fintype.card {χ : DirichletCharacter ℂ r.val // χ.IsPrimitive} : ℝ) *
        ((Q : ℝ) * collisionLiteralBlockEnergy Q B H w r s) :=
      mul_le_mul_of_nonneg_left hslices hfactor
    _ = _ := by ring

end GoldbachCircleMethodCollisionLiteralBlockEnergyV18552
