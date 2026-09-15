import GoldbachCircleMethodPrincipalBlockExplicitBoundV18499

/-!
# Goldbach V1.8.500: hybrid centered-source split

V1.8.479 separated the primitive source and the principal subtraction before
the energy estimate.  That split is exact but loses the arithmetic
`blockInput - 1` cancellation on the conductor-one slot.  This module replaces
it by an exact hybrid partition: the principal primitive term stays paired
with its centering subtraction, while only nonprincipal primitive slots are
separated.  No decay estimate is asserted.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodHybridCenteredSourceSplitV18500

open GoldbachCircleMethodActiveExceptionalCenteringV18129
open GoldbachCircleMethodAdjustedCharacterSlotL2AdapterV18449
open GoldbachCircleMethodAdjustedSourceThreeTermDecompositionV18479
open GoldbachCircleMethodFiniteWindowConvolutionV18119
open GoldbachCircleMethodLogCutoffPresieveBindingV18120
open GoldbachCircleMethodPrimitiveBaseSlotEnergyV18474
open GoldbachCircleMethodPrincipalExceptionalSourceEnergyV18480

/-- The principal primitive source and its `-1` centering term remain in the
same atom, so their cancellation is not destroyed by a triangle inequality. -/
noncomputable def centeredPrincipalSlotSource
    (Q B N : ℕ) (H : ℝ) (t : CharacterSlot Q) : ℂ :=
  if t.1.val = 1 then
    primitiveBaseSlotSource Q B N H t + principalSlotSource Q B N H t
  else 0

/-- Only the genuinely nonprincipal primitive slots enter this channel. -/
noncomputable def nonprincipalPrimitiveSlotSource
    (Q B N : ℕ) (H : ℝ) (t : CharacterSlot Q) : ℂ :=
  if t.1.val = 1 then 0 else primitiveBaseSlotSource Q B N H t

/-- Exact replacement for the over-separated V1.8.479 decomposition. -/
theorem adjustedSlotSource_eq_hybrid_terms
    (Q B N : ℕ) (H b : ℝ) (e t : CharacterSlot Q) :
    adjustedSlotSource Q B N H b (blockInput B) e t =
      centeredPrincipalSlotSource Q B N H t +
        nonprincipalPrimitiveSlotSource Q B N H t +
          exceptionalPowerSlotSource Q B N H b e t := by
  rw [adjustedSlotSource_eq_three_terms]
  by_cases hprincipal : t.1.val = 1
  · simp [centeredPrincipalSlotSource, nonprincipalPrimitiveSlotSource,
      hprincipal]
  · have hzero := principalSlotSource_eq_zero_of_level_ne_one
      Q B N H t hprincipal
    simp [centeredPrincipalSlotSource, nonprincipalPrimitiveSlotSource,
      hprincipal, hzero]

/-- The two deterministic source channels have disjoint level support. -/
theorem centeredPrincipal_or_nonprincipal_zero
    (Q B N : ℕ) (H : ℝ) (t : CharacterSlot Q) :
    centeredPrincipalSlotSource Q B N H t = 0 ∨
      nonprincipalPrimitiveSlotSource Q B N H t = 0 := by
  by_cases hprincipal : t.1.val = 1
  · exact Or.inr (by simp [nonprincipalPrimitiveSlotSource, hprincipal])
  · exact Or.inl (by simp [centeredPrincipalSlotSource, hprincipal])

/-- Exact level-one readback: the hybrid principal atom is the normalized
finite character sum of `blockInput - 1`. -/
theorem centeredPrincipalSlotSource_eq_centered_sum
    (Q B N : ℕ) (H : ℝ) (t : CharacterSlot Q)
    (hprincipal : t.1.val = 1) :
    centeredPrincipalSlotSource Q B N H t =
      (2 * (H : ℂ))⁻¹ *
        ∑ U ∈ centeredWindow (blockCarrier B) N H,
          (blockInput B U * star (t.2.val (U : ZMod t.1.val)) - 1) := by
  unfold centeredPrincipalSlotSource primitiveBaseSlotSource principalSlotSource
  rw [if_pos hprincipal]
  simp only [hprincipal, if_true, Finset.sum_sub_distrib]
  simp only [Finset.sum_const, nsmul_eq_mul]
  ring

end GoldbachCircleMethodHybridCenteredSourceSplitV18500
