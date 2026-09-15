import GoldbachCircleMethodDecayingExceptionalChannelSplitV18526
import GoldbachCircleMethodNonprincipalPrimitiveConductorDecompositionV18507

/-!
# Goldbach V1.8.527: conductor-aligned nonprincipal correlation

The nonprincipal primitive correlation is reindexed exactly by conductor.
Cauchy--Schwarz is then applied inside each conductor family before the outer
conductor sum is estimated.  This replaces the previous cross-conductor
product of two global energies by an aligned sum of conductor-local products.
No decay or analytic conductor estimate is asserted.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodNonprincipalConductorAlignedCorrelationV18527

open GoldbachCircleMethodActiveExceptionalCenteringV18129
open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodHybridCenteredCorrelationEnergyV18501
open GoldbachCircleMethodHybridCenteredSourceSplitV18500
open GoldbachCircleMethodPrincipalWindowBoundaryV18121
open GoldbachCircleMethodPrimitiveBaseSlotEnergyV18474
open GoldbachCircleMethodRemovedConvolutionNormV18123

/-- Coefficient energy restricted to one primitive conductor family. -/
noncomputable def conductorCoefficientEnergy
    {Q : ℕ} (N : ℕ) (w : ℕ → ℂ) (q : PositiveLevel Q) : ℝ :=
  ∑ chi : {chi : DirichletCharacter ℂ q.val // chi.IsPrimitive},
    ‖windowCoefficient q N w chi‖ ^ 2

/-- Primitive source energy restricted to one conductor family. -/
noncomputable def conductorPrimitiveSourceEnergy
    (Q B N : ℕ) (H : ℝ) (q : PositiveLevel Q) : ℝ :=
  ∑ chi : {chi : DirichletCharacter ℂ q.val // chi.IsPrimitive},
    ‖primitiveBaseSlotSource Q B N H ⟨q, chi⟩‖ ^ 2

/-- Nonprincipal correlation at one conductor.  The conductor-one atom is
removed literally rather than estimated. -/
noncomputable def nonprincipalConductorCorrelation
    (Q B N : ℕ) (H : ℝ) (w : ℕ → ℂ) (q : PositiveLevel Q) : ℂ :=
  if q.val = 1 then 0 else
    ∑ chi : {chi : DirichletCharacter ℂ q.val // chi.IsPrimitive},
      windowCoefficient q N w chi *
        primitiveBaseSlotSource Q B N H ⟨q, chi⟩

/-- Exact conductor decomposition of the nonprincipal primitive correlation. -/
theorem nonprincipalPrimitiveCorrelation_eq_sum_conductors
    (Q B N : ℕ) (H : ℝ) (w : ℕ → ℂ) :
    nonprincipalPrimitiveCorrelation Q B N H w =
      ∑ q : PositiveLevel Q,
        nonprincipalConductorCorrelation Q B N H w q := by
  unfold nonprincipalPrimitiveCorrelation nonprincipalPrimitiveSlotSource
    nonprincipalConductorCorrelation
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro q _hq
  by_cases hqOne : q.val = 1
  · simp [hqOne]
  · simp [hqOne]

/-- Cauchy--Schwarz is paid only inside one primitive conductor family. -/
theorem nonprincipalConductorCorrelation_sq_le_local_product
    (Q B N : ℕ) (H : ℝ) (w : ℕ → ℂ) (q : PositiveLevel Q) :
    ‖nonprincipalConductorCorrelation Q B N H w q‖ ^ 2 ≤
      conductorCoefficientEnergy N w q *
        conductorPrimitiveSourceEnergy Q B N H q := by
  by_cases hqOne : q.val = 1
  · rw [nonprincipalConductorCorrelation, if_pos hqOne]
    norm_num
    unfold conductorCoefficientEnergy conductorPrimitiveSourceEnergy
    apply mul_nonneg
    · exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    · exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  · rw [nonprincipalConductorCorrelation, if_neg hqOne]
    have htriangle :
        ‖∑ chi : {chi : DirichletCharacter ℂ q.val // chi.IsPrimitive},
            windowCoefficient q N w chi *
              primitiveBaseSlotSource Q B N H ⟨q, chi⟩‖ ≤
          ∑ chi : {chi : DirichletCharacter ℂ q.val // chi.IsPrimitive},
            ‖windowCoefficient q N w chi‖ *
              ‖primitiveBaseSlotSource Q B N H ⟨q, chi⟩‖ := by
      calc
        _ ≤ ∑ chi : {chi : DirichletCharacter ℂ q.val // chi.IsPrimitive},
              ‖windowCoefficient q N w chi *
                primitiveBaseSlotSource Q B N H ⟨q, chi⟩‖ :=
            norm_sum_le _ _
        _ = _ := by
          apply Finset.sum_congr rfl
          intro chi _hchi
          rw [norm_mul]
    have hsq := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr htriangle
    apply hsq.trans
    unfold conductorCoefficientEnergy conductorPrimitiveSourceEnergy
    exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun chi : {chi : DirichletCharacter ℂ q.val // chi.IsPrimitive} =>
        ‖windowCoefficient q N w chi‖)
      (fun chi : {chi : DirichletCharacter ℂ q.val // chi.IsPrimitive} =>
        ‖primitiveBaseSlotSource Q B N H ⟨q, chi⟩‖)

/-- The outer conductor sum costs only the number of conductors and retains
the aligned coefficient/source products.  It does not manufacture a
cross-conductor energy product. -/
theorem nonprincipalPrimitiveCorrelation_sq_le_conductor_aligned
    (Q B N : ℕ) (H : ℝ) (w : ℕ → ℂ) :
    ‖nonprincipalPrimitiveCorrelation Q B N H w‖ ^ 2 ≤
      (Q : ℝ) *
        ∑ q : PositiveLevel Q,
          conductorCoefficientEnergy N w q *
            conductorPrimitiveSourceEnergy Q B N H q := by
  rw [nonprincipalPrimitiveCorrelation_eq_sum_conductors]
  have htriangle :
      ‖∑ q : PositiveLevel Q,
          nonprincipalConductorCorrelation Q B N H w q‖ ≤
        ∑ q : PositiveLevel Q,
          ‖nonprincipalConductorCorrelation Q B N H w q‖ :=
    norm_sum_le _ _
  have hsq := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr htriangle
  apply hsq.trans
  have hcs := sq_sum_le_card_mul_sum_sq
    (s := Finset.univ)
    (f := fun q : PositiveLevel Q =>
      ‖nonprincipalConductorCorrelation Q B N H w q‖)
  apply hcs.trans
  rw [Finset.card_univ, positive_level_card]
  gcongr with q
  exact nonprincipalConductorCorrelation_sq_le_local_product Q B N H w q

end GoldbachCircleMethodNonprincipalConductorAlignedCorrelationV18527
