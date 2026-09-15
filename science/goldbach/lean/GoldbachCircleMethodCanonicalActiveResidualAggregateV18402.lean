import GoldbachCircleMethodCanonicalSourceAggregateTransferV18401

/-!
# Goldbach V1.8.402: canonical active-residual aggregate

The averaged-square active-residual estimate is transferred to the exact
canonical even target sweep used by V1.8.401.  The target map is proved
injective and its image is proved to lie in the unchanged complete moment
carrier `[0,2B]` at `B=4m`.

This is a finite Cauchy--Schwarz transfer.  It does not assert that the
resulting power bound is below the explicit V1.8.401 reserve; that numeric
absorption remains a separate scale obligation.
-/

set_option autoImplicit false

open scoped BigOperators Classical ContDiff

namespace GoldbachCircleMethodCanonicalActiveResidualAggregateV18402

open GoldbachCircleMethodActiveExceptionalCenteringV18129
open GoldbachCircleMethodActiveResidualExactDecompositionV18251
open GoldbachCircleMethodActualInputModelResidualV18138
open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodCanonicalBumpPrincipalFloorV18220
open GoldbachCircleMethodCanonicalBumpResidualMomentsV18222
open GoldbachCircleMethodCanonicalSourceAggregateTransferV18401
open GoldbachCircleMethodLogCutoffPresieveBindingV18120
open GoldbachCircleMethodRealApproximationMinorAdapterV1873
open GoldbachCircleMethodSupportedModelErrorConvolutionV18182
open GoldbachCircleMethodSupportedResidualParsevalV18190
open GoldbachCircleMethodStructurallyAdmissibleActiveSlotV18258

/-- Integer target used by the canonical even sweep. -/
def canonicalTargetIndex (m i : ℕ) : ℤ :=
  ((4 * m + 2 + 2 * i : ℕ) : ℤ)

/-- Image of the canonical target sweep, retained as a finite integer set. -/
def canonicalTargetSet (m : ℕ) : Finset ℤ :=
  (Finset.range (2 * m)).image (canonicalTargetIndex m)

theorem canonicalTargetIndex_in_full_moment
    (m i : ℕ) (hi : i ∈ Finset.range (2 * m)) :
    canonicalTargetIndex m i ∈ Finset.Icc (0 : ℤ) (2 * (4 * m) : ℕ) := by
  rw [Finset.mem_Icc]
  simp only [canonicalTargetIndex]
  simp only [Finset.mem_range] at hi
  constructor <;> omega

theorem canonicalTargetIndex_injective (m : ℕ) :
    Function.Injective (canonicalTargetIndex m) := by
  intro i j hij
  simp only [canonicalTargetIndex] at hij
  omega

theorem canonicalTargetSet_subset_full_moment (m : ℕ) :
    canonicalTargetSet m ⊆ Finset.Icc (0 : ℤ) (2 * (4 * m) : ℕ) := by
  intro k hk
  rw [canonicalTargetSet, Finset.mem_image] at hk
  obtain ⟨i, hi, rfl⟩ := hk
  exact canonicalTargetIndex_in_full_moment m i hi

/-- The energy on the canonical target sweep is bounded by the complete
integer moment.  No analytic estimate enters this reindexing theorem. -/
theorem canonical_target_active_residual_energy_le_full_moment
    (m : ℕ) (rho : ℝ)
    (hR2 : 2 ≤ ((4 * m : ℕ) : ℝ) ^ rho) (b : ℝ)
    (e : CharacterSlot ⌊(((4 * m : ℕ) : ℝ) ^ rho) ^ 2⌋₊) :
    (∑ i ∈ Finset.range (2 * m),
      ‖canonicalActiveResidualAt (4 * m) rho hR2 b e
        (canonicalTargetIndex m i)‖ ^ 2) ≤
      ∑ k ∈ Finset.Icc (0 : ℤ) (2 * (4 * m) : ℕ),
        ‖canonicalActiveResidualAt (4 * m) rho hR2 b e k‖ ^ 2 := by
  have himage :
      (∑ k ∈ canonicalTargetSet m,
        ‖canonicalActiveResidualAt (4 * m) rho hR2 b e k‖ ^ 2) =
      ∑ i ∈ Finset.range (2 * m),
        ‖canonicalActiveResidualAt (4 * m) rho hR2 b e
          (canonicalTargetIndex m i)‖ ^ 2 := by
    exact Finset.sum_image
      (Set.injOn_of_injective (canonicalTargetIndex_injective m))
  rw [← himage]
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (canonicalTargetSet_subset_full_moment m)
    (fun k _hk _hnot => sq_nonneg
      ‖canonicalActiveResidualAt (4 * m) rho hR2 b e k‖)

/-- Cauchy--Schwarz on the exact canonical target aggregate, followed by the
injective target-to-moment transfer. -/
theorem canonical_active_residual_target_sum_sq_le_full_moment
    (m : ℕ) (rho : ℝ)
    (hR2 : 2 ≤ ((4 * m : ℕ) : ℝ) ^ rho) (b : ℝ)
    (e : StructurallyAdmissibleActiveSlot
      ⌊(((4 * m : ℕ) : ℝ) ^ rho) ^ 2⌋₊) :
    (canonicalActiveResidualTargetSum m rho hR2 b e) ^ 2 ≤
      (2 * m : ℝ) *
        ∑ k ∈ Finset.Icc (0 : ℤ) (2 * (4 * m) : ℕ),
          ‖canonicalActiveResidualAt (4 * m) rho hR2 b e.val k‖ ^ 2 := by
  unfold canonicalActiveResidualTargetSum
  have hcs := sq_sum_le_card_mul_sum_sq
    (s := Finset.range (2 * m))
    (f := fun i =>
      (canonicalActiveResidualAt (4 * m) rho hR2 b e.val
        (canonicalTargetIndex m i)).re)
  have hpoint (i : ℕ) :
      ((canonicalActiveResidualAt (4 * m) rho hR2 b e.val
        (canonicalTargetIndex m i)).re) ^ 2 ≤
      ‖canonicalActiveResidualAt (4 * m) rho hR2 b e.val
        (canonicalTargetIndex m i)‖ ^ 2 := by
    rw [← sq_abs]
    exact (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).mpr
      (Complex.abs_re_le_norm _)
  calc
    (∑ i ∈ Finset.range (2 * m),
        (canonicalActiveResidualAt (4 * m) rho hR2 b e.val
          (canonicalTargetIndex m i)).re) ^ 2
        ≤ ((Finset.range (2 * m)).card : ℝ) *
          ∑ i ∈ Finset.range (2 * m),
            ((canonicalActiveResidualAt (4 * m) rho hR2 b e.val
              (canonicalTargetIndex m i)).re) ^ 2 := hcs
    _ ≤ (2 * m : ℝ) *
          ∑ i ∈ Finset.range (2 * m),
            ‖canonicalActiveResidualAt (4 * m) rho hR2 b e.val
              (canonicalTargetIndex m i)‖ ^ 2 := by
      simp only [Finset.card_range, Nat.cast_mul, Nat.cast_ofNat]
      exact mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum (fun i _hi => hpoint i)) (by positivity)
    _ ≤ (2 * m : ℝ) *
          ∑ k ∈ Finset.Icc (0 : ℤ) (2 * (4 * m) : ℕ),
            ‖canonicalActiveResidualAt (4 * m) rho hR2 b e.val k‖ ^ 2 :=
      mul_le_mul_of_nonneg_left
        (canonical_target_active_residual_energy_le_full_moment
          m rho hR2 b e.val) (by positivity)

/-- Direct specialization of the V1.8.222 active moment bound to the exact
canonical target aggregate.  The constant is chosen before `m`, `b`, and the
structurally admissible active slot. -/
theorem canonical_active_residual_target_sum_sq_power_bound
    (C rho : ℝ) (hC : 0 ≤ C) (hV : RealVaughanEstimate C)
    (hrho : 0 < rho) :
    ∃ Crho : ℝ, 0 ≤ Crho ∧ ∀ (m : ℕ), 6 ≤ 4 * m →
      ∀ (hR2 : 2 ≤ ((4 * m : ℕ) : ℝ) ^ rho),
      Real.exp (Real.sqrt (Real.log ((4 * m : ℕ) : ℝ))) ≤
          ((4 * m : ℕ) : ℝ) ^ rho →
      ((4 * m : ℕ) : ℝ) ^ rho ≤
          ((4 * m : ℕ) : ℝ) ^ ((1 : ℝ) / 10000) →
      ∀ b : ℝ, 0 ≤ b → b ≤ 1 →
      ∀ e : StructurallyAdmissibleActiveSlot
        ⌊(((4 * m : ℕ) : ℝ) ^ rho) ^ 2⌋₊,
      (canonicalActiveResidualTargetSum m rho hR2 b e) ^ 2 ≤
        (2 * m : ℝ) *
          (Crho * ((4 * m : ℕ) : ℝ) ^ 3 *
            (((4 * m : ℕ) : ℝ) ^ rho) ^ (-(5 : ℝ) / 8) *
            (Real.log ((4 * m : ℕ) : ℝ)) ^ 2) := by
  obtain ⟨Crho, hCrho, hmoment⟩ :=
    canonical_active_residual_moment_power_bound C rho hC hV hrho
  refine ⟨Crho, hCrho, ?_⟩
  intro m hB hR2 hlower hupper b hb hb1 e
  have hfull := hmoment (4 * m) hB hR2 hlower hupper b hb hb1 e.val
  have hfinite :=
    canonical_active_residual_target_sum_sq_le_full_moment
      m rho hR2 b e
  have hfactor : (0 : ℝ) ≤ 2 * m := by positivity
  exact hfinite.trans (mul_le_mul_of_nonneg_left hfull hfactor)

end GoldbachCircleMethodCanonicalActiveResidualAggregateV18402
