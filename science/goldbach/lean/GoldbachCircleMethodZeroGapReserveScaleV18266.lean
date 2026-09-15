import GoldbachCircleMethodZeroGapNonGoldbachForcingV18265

/-!
# Goldbach V1.8.266: zero-gap reserve scale and uniform-floor obstruction

The active exceptional-character reserve scale is kept proportional to
`min 1 ((1-beta) * log N)`.  The final theorem proves that the interval
constraints `0 < beta < 1` alone cannot imply a positive beta-independent
floor for this scale.
-/

open scoped Classical BigOperators

set_option autoImplicit false

namespace GoldbachCircleMethodZeroGapReserveScaleV18266

open GoldbachCircleMethodStructurallyAdmissibleActiveSlotV18258
open GoldbachCircleMethodExceptionalZeroGapAttestationRepairV18263

noncomputable def zeroGapReserveScale (gap : ℝ) (N : ℕ) : ℝ :=
  min 1 (gap * Real.log N)

theorem zeroGapReserveScale_nonneg
    (gap : ℝ) (N : ℕ) (hgap : 0 ≤ gap) (hN : 1 ≤ N) :
    0 ≤ zeroGapReserveScale gap N := by
  unfold zeroGapReserveScale
  apply le_min
  · norm_num
  · exact mul_nonneg hgap (Real.log_nonneg (by exact_mod_cast hN))

theorem zeroGapReserveScale_pos
    (gap : ℝ) (N : ℕ) (hgap : 0 < gap) (hN : 1 < N) :
    0 < zeroGapReserveScale gap N := by
  unfold zeroGapReserveScale
  apply lt_min
  · norm_num
  · exact mul_pos hgap (Real.log_pos (by exact_mod_cast hN))

theorem zeroGapReserveScale_le_one (gap : ℝ) (N : ℕ) :
    zeroGapReserveScale gap N ≤ 1 := by
  exact min_le_left _ _

theorem zeroGapReserveScale_le_gap_log (gap : ℝ) (N : ℕ) :
    zeroGapReserveScale gap N ≤ gap * Real.log N := by
  exact min_le_right _ _

theorem attestedZeroGapReserveScale_pos
    {Q : ℕ}
    {ExceptionalZeroAt : StructurallyAdmissibleActiveSlot Q → ℝ → Prop}
    (d : ExceptionalZeroGapAttestation Q ExceptionalZeroAt)
    (N : ℕ) (hN : 1 < N) :
    0 < zeroGapReserveScale d.zeroGap N := by
  exact zeroGapReserveScale_pos d.zeroGap N (zeroGap_pos d) hN

/-- No positive floor uniform in the bare zero gap follows from `0 < gap < 1`.
This is an obstruction to replacing the sign-aware theta scale by a fixed
positive constant without importing a quantitative zero-free hypothesis. -/
theorem exists_admissible_gap_below_any_positive_floor
    (N : ℕ) (hN : 1 < N) (c : ℝ) (hc : 0 < c) :
    ∃ gap : ℝ, 0 < gap ∧ gap < 1 ∧ zeroGapReserveScale gap N < c := by
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast hN)
  let gap : ℝ := min (1 / 2) (c / (2 * Real.log N))
  have hgap_pos : 0 < gap := by
    dsimp [gap]
    apply lt_min
    · norm_num
    · positivity
  have hgap_lt : gap < 1 := by
    calc
      gap ≤ 1 / 2 := min_le_left _ _
      _ < 1 := by norm_num
  have hmul : gap * Real.log N ≤ c / 2 := by
    calc
      gap * Real.log N ≤ (c / (2 * Real.log N)) * Real.log N :=
        mul_le_mul_of_nonneg_right (min_le_right _ _) hlog.le
      _ = c / 2 := by field_simp [ne_of_gt hlog]
  refine ⟨gap, hgap_pos, hgap_lt, ?_⟩
  calc
    zeroGapReserveScale gap N ≤ gap * Real.log N :=
      zeroGapReserveScale_le_gap_log gap N
    _ ≤ c / 2 := hmul
    _ < c := by linarith

theorem no_positive_uniform_zeroGapReserveScale_floor
    (N : ℕ) (hN : 1 < N) :
    ¬ ∃ c : ℝ, 0 < c ∧
      ∀ gap : ℝ, 0 < gap → gap < 1 → c ≤ zeroGapReserveScale gap N := by
  rintro ⟨c, hc, hfloor⟩
  obtain ⟨gap, hgap_pos, hgap_lt, hsmall⟩ :=
    exists_admissible_gap_below_any_positive_floor N hN c hc
  exact (not_lt_of_ge (hfloor gap hgap_pos hgap_lt)) hsmall

end GoldbachCircleMethodZeroGapReserveScaleV18266

