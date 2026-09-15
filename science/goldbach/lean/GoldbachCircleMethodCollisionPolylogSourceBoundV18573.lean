import GoldbachCircleMethodCollisionLinearMomentTransferV18572
import GoldbachCircleMethodUniformSharpSourceCapV18531

/-!
# Goldbach V1.8.573: polylogarithmic source-product bound

At the admitted window scale `1 ≤ H` and `Q ≤ H`, the two primitive source
families in the collision envelope are bounded independently by the already
checked sharp source cap.  The result is explicit and retains the actual block
cardinality.  It does not claim that the resulting collision bound is small.
-/

set_option autoImplicit false

open scoped BigOperators Classical ComplexConjugate

namespace GoldbachCircleMethodCollisionPolylogSourceBoundV18573

open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodCollisionLinearMomentTransferV18572
open GoldbachCircleMethodLogCutoffPresieveBindingV18120
open GoldbachCircleMethodNonprincipalConductorAlignedCorrelationV18527
open GoldbachCircleMethodPrimitiveBaseSlotEnergyV18474
open GoldbachCircleMethodSharpNonprincipalBlockEnvelopeV18530
open GoldbachCircleMethodUniformSharpSourceCapV18531

noncomputable def collisionSourcePolylogCap (B : ℕ) : ℝ :=
  (9 / 4 : ℝ) * (Real.log (B : ℝ)) ^ 2

theorem collisionSourcePolylogCap_nonneg (B : ℕ) :
    0 ≤ collisionSourcePolylogCap B := by
  unfold collisionSourcePolylogCap
  positivity

theorem conductorPrimitiveSourceEnergy_le_polylog_cap
    (Q B N : ℕ) (H : ℝ) (q : PositiveLevel Q)
    (hB : 2 ≤ B) (hH : 1 ≤ H) (hQH : (Q : ℝ) ≤ H) :
    conductorPrimitiveSourceEnergy Q B N H q ≤
      collisionSourcePolylogCap B := by
  have hH0 : 0 ≤ H := zero_le_one.trans hH
  exact (conductorPrimitiveSourceEnergy_le_sharp_cap
      Q B N H q hB hH0).trans
    ((sharpPrimitiveSourceCap_le_uniform H q hH0).trans
      (by
        unfold collisionSourcePolylogCap
        exact uniformSharpPrimitiveSourceCap_le_nine_fourths_log_sq
          Q B H hH hQH))

theorem fixed_target_collision_source_product_le_polylog
    (Q B N : ℕ) (H V : ℝ) (r s : PositiveLevel Q)
    (hB : 2 ≤ B) (hH : 1 ≤ H) (hQH : (Q : ℝ) ≤ H) :
    (∑ ψ : {ψ : DirichletCharacter ℂ s.val // ψ.IsPrimitive},
      ∑ χ : {χ : DirichletCharacter ℂ r.val // χ.IsPrimitive},
        V ^ 4 *
          ‖primitiveBaseSlotSource Q B N H ⟨r, χ⟩‖ ^ 2 *
          ‖primitiveBaseSlotSource Q B N H ⟨s, ψ⟩‖ ^ 2) ≤
      V ^ 4 * (collisionSourcePolylogCap B) ^ 2 := by
  let Cr := conductorPrimitiveSourceEnergy Q B N H r
  let Cs := conductorPrimitiveSourceEnergy Q B N H s
  let L := collisionSourcePolylogCap B
  have hCr : Cr ≤ L :=
    conductorPrimitiveSourceEnergy_le_polylog_cap
      Q B N H r hB hH hQH
  have hCs : Cs ≤ L :=
    conductorPrimitiveSourceEnergy_le_polylog_cap
      Q B N H s hB hH hQH
  have hCr0 : 0 ≤ Cr := by
    unfold Cr conductorPrimitiveSourceEnergy
    positivity
  have hCs0 : 0 ≤ Cs := by
    unfold Cs conductorPrimitiveSourceEnergy
    positivity
  have hL0 : 0 ≤ L := by
    exact collisionSourcePolylogCap_nonneg B
  have hfactor :
      (∑ ψ : {ψ : DirichletCharacter ℂ s.val // ψ.IsPrimitive},
        ∑ χ : {χ : DirichletCharacter ℂ r.val // χ.IsPrimitive},
          V ^ 4 *
            ‖primitiveBaseSlotSource Q B N H ⟨r, χ⟩‖ ^ 2 *
            ‖primitiveBaseSlotSource Q B N H ⟨s, ψ⟩‖ ^ 2) =
        V ^ 4 * Cr * Cs := by
    unfold Cr Cs conductorPrimitiveSourceEnergy
    calc
      (∑ ψ : {ψ : DirichletCharacter ℂ s.val // ψ.IsPrimitive},
        ∑ χ : {χ : DirichletCharacter ℂ r.val // χ.IsPrimitive},
          V ^ 4 *
            ‖primitiveBaseSlotSource Q B N H ⟨r, χ⟩‖ ^ 2 *
            ‖primitiveBaseSlotSource Q B N H ⟨s, ψ⟩‖ ^ 2) =
          ∑ ψ : {ψ : DirichletCharacter ℂ s.val // ψ.IsPrimitive},
            (V ^ 4 * ‖primitiveBaseSlotSource Q B N H ⟨s, ψ⟩‖ ^ 2) *
              ∑ χ : {χ : DirichletCharacter ℂ r.val // χ.IsPrimitive},
                ‖primitiveBaseSlotSource Q B N H ⟨r, χ⟩‖ ^ 2 := by
            apply Finset.sum_congr rfl
            intro ψ _hψ
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro χ _hχ
            ring
      _ = V ^ 4 *
          (∑ χ : {χ : DirichletCharacter ℂ r.val // χ.IsPrimitive},
            ‖primitiveBaseSlotSource Q B N H ⟨r, χ⟩‖ ^ 2) *
          (∑ ψ : {ψ : DirichletCharacter ℂ s.val // ψ.IsPrimitive},
            ‖primitiveBaseSlotSource Q B N H ⟨s, ψ⟩‖ ^ 2) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro ψ _hψ
        ring
  rw [hfactor]
  have hV : 0 ≤ V ^ 4 := by positivity
  calc
    V ^ 4 * Cr * Cs ≤ V ^ 4 * L * Cs := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hCr hV) hCs0
    _ ≤ V ^ 4 * L * L := by
      exact mul_le_mul_of_nonneg_left hCs (mul_nonneg hV hL0)
    _ = V ^ 4 * L ^ 2 := by ring

/-- The complete source-product envelope is bounded by the number of actual
targets times the squared polylogarithmic cap. -/
theorem collisionPrimitiveSourceProductEnergy_le_block_polylog
    (Q B : ℕ) (H V : ℝ) (r s : PositiveLevel Q)
    (hB : 2 ≤ B) (hH : 1 ≤ H) (hQH : (Q : ℝ) ≤ H) :
    collisionPrimitiveSourceProductEnergy Q B H V r s ≤
      ((blockCarrier B).card : ℝ) *
        (V ^ 4 * (collisionSourcePolylogCap B) ^ 2) := by
  unfold collisionPrimitiveSourceProductEnergy
  calc
    (∑ N ∈ blockCarrier B,
      ∑ ψ : {ψ : DirichletCharacter ℂ s.val // ψ.IsPrimitive},
        ∑ χ : {χ : DirichletCharacter ℂ r.val // χ.IsPrimitive},
          V ^ 4 *
            ‖primitiveBaseSlotSource Q B N H ⟨r, χ⟩‖ ^ 2 *
            ‖primitiveBaseSlotSource Q B N H ⟨s, ψ⟩‖ ^ 2) ≤
        ∑ _N ∈ blockCarrier B,
          V ^ 4 * (collisionSourcePolylogCap B) ^ 2 := by
      exact Finset.sum_le_sum (fun N _hN =>
        fixed_target_collision_source_product_le_polylog
          Q B N H V r s hB hH hQH)
    _ = ((blockCarrier B).card : ℝ) *
          (V ^ 4 * (collisionSourcePolylogCap B) ^ 2) := by simp

end GoldbachCircleMethodCollisionPolylogSourceBoundV18573
