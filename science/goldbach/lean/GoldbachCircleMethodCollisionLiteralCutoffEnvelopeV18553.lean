import GoldbachCircleMethodCollisionLiteralBlockEnergyV18552

/-!
# Goldbach V1.8.553: cutoff envelope for the literal collision block

The exact target and primitive-character cardinalities in V1.8.552 are
bounded by their genuine carriers.  The block has cardinality at most `B`,
each primitive-character family has cardinality at most its conductor and
hence at most `Q`, and the product-denominator collision itself costs the
single `Q` from V1.8.550.  The resulting squared envelope is `B * Q^3` times
the literal collision energy.  No decay of that energy is asserted.
-/

set_option autoImplicit false

open scoped BigOperators Classical ComplexConjugate

namespace GoldbachCircleMethodCollisionLiteralCutoffEnvelopeV18553

open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodCollisionLiteralBlockEnergyV18552
open GoldbachCircleMethodCollisionLiteralSliceEnergyV18551
open GoldbachCircleMethodCrossDenominatorCollisionPartitionV18547
open GoldbachCircleMethodLogCutoffPresieveBindingV18120
open GoldbachCircleMethodRemovedCharacterWindowNormV18124

/-- Coarse but explicit cutoff envelope for one actual conductor-pair
collision block.  The bound records exactly one complement-pair factor `Q`.
-/
theorem collisionLiteralCrossBlockCorrelation_sq_le_B_mul_Q_cubed_energy
    (Q B : ℕ) (H : ℝ) (w : ℕ → ℂ)
    (r s : PositiveLevel Q) :
    (collisionLiteralCrossBlockCorrelation Q B H w r s) ^ 2 ≤
      (B : ℝ) * (Q : ℝ) ^ 3 *
        collisionLiteralBlockEnergy Q B H w r s := by
  have hB : ((blockCarrier B).card : ℝ) ≤ (B : ℝ) := by
    exact_mod_cast (show (blockCarrier B).card ≤ B by
      simp only [blockCarrier, Nat.card_Ioc]
      omega)
  have hs :
      (Fintype.card {ψ : DirichletCharacter ℂ s.val // ψ.IsPrimitive} : ℝ) ≤
        (Q : ℝ) := by
    exact_mod_cast ((primitive_character_card_le s.val).trans
      (Finset.mem_Icc.mp s.property).2)
  have hr :
      (Fintype.card {χ : DirichletCharacter ℂ r.val // χ.IsPrimitive} : ℝ) ≤
        (Q : ℝ) := by
    exact_mod_cast ((primitive_character_card_le r.val).trans
      (Finset.mem_Icc.mp r.property).2)
  have henergy : 0 ≤ collisionLiteralBlockEnergy Q B H w r s := by
    unfold collisionLiteralBlockEnergy collisionLiteralSliceEnergy
    positivity
  calc
    _ ≤ ((blockCarrier B).card : ℝ) *
        (Fintype.card {ψ : DirichletCharacter ℂ s.val // ψ.IsPrimitive} : ℝ) *
        (Fintype.card {χ : DirichletCharacter ℂ r.val // χ.IsPrimitive} : ℝ) *
        (Q : ℝ) * collisionLiteralBlockEnergy Q B H w r s :=
      collisionLiteralCrossBlockCorrelation_sq_le_energy Q B H w r s
    _ ≤ (B : ℝ) * (Q : ℝ) * (Q : ℝ) * (Q : ℝ) *
        collisionLiteralBlockEnergy Q B H w r s := by
      gcongr
    _ = (B : ℝ) * (Q : ℝ) ^ 3 *
        collisionLiteralBlockEnergy Q B H w r s := by ring

end GoldbachCircleMethodCollisionLiteralCutoffEnvelopeV18553
