import GoldbachCircleMethodCanonicalCentralCenteredErrorAggregateV18405

/-!
# Goldbach V1.8.406: canonical central active-residual aggregate

The V1.8.222 active residual moment is restricted to the exact central target
sweep of V1.8.403--405.  Injectivity and containment in `[0,2B]` are proved
before finite Cauchy--Schwarz is applied.

The terminal `B^2/256` absorption is conditional only on the displayed
numeric power-budget inequality.  No asymptotic threshold is manufactured.
-/

set_option autoImplicit false

open scoped BigOperators Classical ContDiff

namespace GoldbachCircleMethodCanonicalCentralActiveResidualV18406

open GoldbachCircleMethodActiveExceptionalCenteringV18129
open GoldbachCircleMethodActiveResidualExactDecompositionV18251
open GoldbachCircleMethodActualInputModelResidualV18138
open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodCanonicalBumpResidualMomentsV18222
open GoldbachCircleMethodCanonicalCentralAdjustedPositiveV18403
open GoldbachCircleMethodCanonicalCentralSourceTransferV18404
open GoldbachCircleMethodRealApproximationMinorAdapterV1873
open GoldbachCircleMethodStructurallyAdmissibleActiveSlotV18258
open GoldbachCircleMethodSupportedModelErrorConvolutionV18182
open GoldbachCircleMethodSupportedResidualParsevalV18190

def centralTargetIndexInt (m i : ℕ) : ℤ :=
  ((centralTargetNat m i : ℕ) : ℤ)

def centralTargetSet (m : ℕ) : Finset ℤ :=
  (Finset.range (2 * m + 1)).image (centralTargetIndexInt m)

theorem centralTargetIndexInt_in_full_moment
    (m i : ℕ) (hi : i ∈ Finset.range (2 * m + 1)) :
    centralTargetIndexInt m i ∈
      Finset.Icc (0 : ℤ) (2 * (8 * m) : ℕ) := by
  rw [Finset.mem_Icc]
  simp only [centralTargetIndexInt, centralTargetNat]
  simp only [Finset.mem_range] at hi
  constructor <;> omega

theorem centralTargetIndexInt_injective (m : ℕ) :
    Function.Injective (centralTargetIndexInt m) := by
  intro i j hij
  simp only [centralTargetIndexInt, centralTargetNat] at hij
  omega

theorem centralTargetSet_subset_full_moment (m : ℕ) :
    centralTargetSet m ⊆ Finset.Icc (0 : ℤ) (2 * (8 * m) : ℕ) := by
  intro k hk
  rw [centralTargetSet, Finset.mem_image] at hk
  obtain ⟨i, hi, rfl⟩ := hk
  exact centralTargetIndexInt_in_full_moment m i hi

theorem central_target_active_residual_energy_le_full_moment
    (m : ℕ) (rho : ℝ)
    (hR2 : 2 ≤ ((8 * m : ℕ) : ℝ) ^ rho) (b : ℝ)
    (e : CharacterSlot ⌊(((8 * m : ℕ) : ℝ) ^ rho) ^ 2⌋₊) :
    (∑ i ∈ Finset.range (2 * m + 1),
      ‖canonicalActiveResidualAt (8 * m) rho hR2 b e
        (centralTargetIndexInt m i)‖ ^ 2) ≤
      ∑ k ∈ Finset.Icc (0 : ℤ) (2 * (8 * m) : ℕ),
        ‖canonicalActiveResidualAt (8 * m) rho hR2 b e k‖ ^ 2 := by
  have himage :
      (∑ k ∈ centralTargetSet m,
        ‖canonicalActiveResidualAt (8 * m) rho hR2 b e k‖ ^ 2) =
      ∑ i ∈ Finset.range (2 * m + 1),
        ‖canonicalActiveResidualAt (8 * m) rho hR2 b e
          (centralTargetIndexInt m i)‖ ^ 2 := by
    exact Finset.sum_image
      (Set.injOn_of_injective (centralTargetIndexInt_injective m))
  rw [← himage]
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (centralTargetSet_subset_full_moment m)
    (fun k _hk _hnot => sq_nonneg
      ‖canonicalActiveResidualAt (8 * m) rho hR2 b e k‖)

theorem central_active_residual_target_sum_sq_le_full_moment
    (m : ℕ) (rho : ℝ)
    (hR2 : 2 ≤ ((8 * m : ℕ) : ℝ) ^ rho) (b : ℝ)
    (e : StructurallyAdmissibleActiveSlot
      ⌊(((8 * m : ℕ) : ℝ) ^ rho) ^ 2⌋₊) :
    (centralActiveResidualTargetSum m rho hR2 b e) ^ 2 ≤
      (2 * m + 1 : ℝ) *
        ∑ k ∈ Finset.Icc (0 : ℤ) (2 * (8 * m) : ℕ),
          ‖canonicalActiveResidualAt (8 * m) rho hR2 b e.val k‖ ^ 2 := by
  unfold centralActiveResidualTargetSum
  have hcs := sq_sum_le_card_mul_sum_sq
    (s := Finset.range (2 * m + 1))
    (f := fun i =>
      (canonicalActiveResidualAt (8 * m) rho hR2 b e.val
        (centralTargetIndexInt m i)).re)
  have hpoint (i : ℕ) :
      ((canonicalActiveResidualAt (8 * m) rho hR2 b e.val
        (centralTargetIndexInt m i)).re) ^ 2 ≤
      ‖canonicalActiveResidualAt (8 * m) rho hR2 b e.val
        (centralTargetIndexInt m i)‖ ^ 2 := by
    rw [← sq_abs]
    exact (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).mpr
      (Complex.abs_re_le_norm _)
  calc
    (∑ i ∈ Finset.range (2 * m + 1),
        (canonicalActiveResidualAt (8 * m) rho hR2 b e.val
          (centralTargetIndexInt m i)).re) ^ 2
        ≤ ((Finset.range (2 * m + 1)).card : ℝ) *
          ∑ i ∈ Finset.range (2 * m + 1),
            ((canonicalActiveResidualAt (8 * m) rho hR2 b e.val
              (centralTargetIndexInt m i)).re) ^ 2 := hcs
    _ ≤ (2 * m + 1 : ℝ) *
          ∑ i ∈ Finset.range (2 * m + 1),
            ‖canonicalActiveResidualAt (8 * m) rho hR2 b e.val
              (centralTargetIndexInt m i)‖ ^ 2 := by
      simp only [Finset.card_range, Nat.cast_add, Nat.cast_mul,
        Nat.cast_one, Nat.cast_ofNat]
      exact mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum (fun i _hi => hpoint i)) (by positivity)
    _ ≤ (2 * m + 1 : ℝ) *
          ∑ k ∈ Finset.Icc (0 : ℤ) (2 * (8 * m) : ℕ),
            ‖canonicalActiveResidualAt (8 * m) rho hR2 b e.val k‖ ^ 2 :=
      mul_le_mul_of_nonneg_left
        (central_target_active_residual_energy_le_full_moment
          m rho hR2 b e.val) (by positivity)

theorem central_active_residual_target_sum_sq_power_bound
    (C rho : ℝ) (hC : 0 ≤ C) (hV : RealVaughanEstimate C)
    (hrho : 0 < rho) :
    ∃ Crho : ℝ, 0 ≤ Crho ∧ ∀ (m : ℕ), 6 ≤ 8 * m →
      ∀ (hR2 : 2 ≤ ((8 * m : ℕ) : ℝ) ^ rho),
      Real.exp (Real.sqrt (Real.log ((8 * m : ℕ) : ℝ))) ≤
          ((8 * m : ℕ) : ℝ) ^ rho →
      ((8 * m : ℕ) : ℝ) ^ rho ≤
          ((8 * m : ℕ) : ℝ) ^ ((1 : ℝ) / 10000) →
      ∀ b : ℝ, 0 ≤ b → b ≤ 1 →
      ∀ e : StructurallyAdmissibleActiveSlot
        ⌊(((8 * m : ℕ) : ℝ) ^ rho) ^ 2⌋₊,
      (centralActiveResidualTargetSum m rho hR2 b e) ^ 2 ≤
        (2 * m + 1 : ℝ) *
          (Crho * ((8 * m : ℕ) : ℝ) ^ 3 *
            (((8 * m : ℕ) : ℝ) ^ rho) ^ (-(5 : ℝ) / 8) *
            (Real.log ((8 * m : ℕ) : ℝ)) ^ 2) := by
  obtain ⟨Crho, hCrho, hmoment⟩ :=
    canonical_active_residual_moment_power_bound C rho hC hV hrho
  refine ⟨Crho, hCrho, ?_⟩
  intro m hB hR2 hlower hupper b hb hb1 e
  have hfull := hmoment (8 * m) hB hR2 hlower hupper b hb hb1 e.val
  have hfinite := central_active_residual_target_sum_sq_le_full_moment
    m rho hR2 b e
  exact hfinite.trans
    (mul_le_mul_of_nonneg_left hfull (by positivity))

/-- The displayed power budget is exactly the remaining numeric scale gate
for a `B^2/256` active-residual absorption. -/
theorem central_active_residual_target_sum_abs_lt_one_over_256
    (m : ℕ) (rho Crho b : ℝ)
    (hR2 : 2 ≤ ((8 * m : ℕ) : ℝ) ^ rho)
    (e : StructurallyAdmissibleActiveSlot
      ⌊(((8 * m : ℕ) : ℝ) ^ rho) ^ 2⌋₊)
    (hsq :
      (centralActiveResidualTargetSum m rho hR2 b e) ^ 2 ≤
        (2 * m + 1 : ℝ) *
          (Crho * ((8 * m : ℕ) : ℝ) ^ 3 *
            (((8 * m : ℕ) : ℝ) ^ rho) ^ (-(5 : ℝ) / 8) *
            (Real.log ((8 * m : ℕ) : ℝ)) ^ 2))
    (hbudget :
      (2 * m + 1 : ℝ) *
          (Crho * ((8 * m : ℕ) : ℝ) ^ 3 *
            (((8 * m : ℕ) : ℝ) ^ rho) ^ (-(5 : ℝ) / 8) *
            (Real.log ((8 * m : ℕ) : ℝ)) ^ 2) <
        (((8 * m : ℕ) : ℝ) ^ 2 / 256) ^ 2) :
    |centralActiveResidualTargetSum m rho hR2 b e| <
      ((8 * m : ℕ) : ℝ) ^ 2 / 256 := by
  have hsq' :
      (centralActiveResidualTargetSum m rho hR2 b e) ^ 2 <
        (((8 * m : ℕ) : ℝ) ^ 2 / 256) ^ 2 := hsq.trans_lt hbudget
  have habssq :
      |centralActiveResidualTargetSum m rho hR2 b e| ^ 2 <
        (((8 * m : ℕ) : ℝ) ^ 2 / 256) ^ 2 := by
    simpa only [sq_abs] using hsq'
  have htarget : 0 ≤ ((8 * m : ℕ) : ℝ) ^ 2 / 256 := by positivity
  nlinarith [sq_nonneg
    (|centralActiveResidualTargetSum m rho hR2 b e| +
      ((8 * m : ℕ) : ℝ) ^ 2 / 256)]

end GoldbachCircleMethodCanonicalCentralActiveResidualV18406

