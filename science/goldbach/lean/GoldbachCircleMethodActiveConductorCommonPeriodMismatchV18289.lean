import GoldbachCircleMethodAdjustedModelPeriodicFrozenBindingV18288

/-!
# Goldbach V1.8.289: active-conductor/common-period mismatch

The period used by the local character kernel is the active conductor `r`.
The actual finite companions have a different contract: their readback period
must be divisible by every denominator level up to `Q`.  This module gives a
finite constructive witness that the two periods cannot be identified
uniformly.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodActiveConductorCommonPeriodMismatchV18289

open GoldbachCircleMethodBoundedConductorReindexV18117

/-- The active conductor two is an admissible positive level at cutoff three. -/
def levelTwoAtThree : PositiveLevel 3 :=
  ⟨2, by simp⟩

/-- Denominator three is also present in the same finite companion family. -/
def levelThreeAtThree : PositiveLevel 3 :=
  ⟨3, by simp⟩

/-- The active conductor `2` is not a common period for all denominator levels
at cutoff `Q=3`, since the present denominator `3` does not divide it. -/
theorem levelTwo_not_commonPeriod_at_cutoff_three :
    ¬ (∀ l : PositiveLevel 3, l.val ∣ levelTwoAtThree.val) := by
  intro h
  have h32 := h levelThreeAtThree
  norm_num [levelTwoAtThree, levelThreeAtThree] at h32

/-- There is no theorem identifying every active conductor with a common
finite-companion readback period over its full cutoff family. -/
theorem no_uniform_active_conductor_common_period :
    ¬ (∀ (Q : ℕ) (r : PositiveLevel Q),
      ∀ l : PositiveLevel Q, l.val ∣ r.val) := by
  intro h
  exact levelTwo_not_commonPeriod_at_cutoff_three (h 3 levelTwoAtThree)

/-- Witness-bearing form for audit systems that record failed universal
period substitutions as data. -/
theorem exists_active_conductor_period_mismatch :
    ∃ (Q : ℕ) (r : PositiveLevel Q),
      ¬ (∀ l : PositiveLevel Q, l.val ∣ r.val) := by
  exact ⟨3, levelTwoAtThree, levelTwo_not_commonPeriod_at_cutoff_three⟩

end GoldbachCircleMethodActiveConductorCommonPeriodMismatchV18289

