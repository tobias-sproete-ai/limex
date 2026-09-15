import GoldbachCircleMethodExplicitJordanParitySplitV18652

/-!
# V1.8.660: exact coordinate-parity split of the even Jordan channel

This append-only module refines only the off-diagonal even-pair-sum channel
from V1.8.652.  Since an even sum has coordinates of equal parity, that
carrier is the disjoint union of its even-even and odd-odd coordinate
subchannels.

The diagonal reserve is kept as a third, separate term.  It cannot be assigned
definitionally to the odd-odd subchannel: even-even diagonal pairs exist (for
example `2 + 2 = 4`), and von-Mangoldt weights do not erase powers of two.
No density claim about diagonal pairs is made.

All identities below are finite-sum identities.  The final inequalities only
locate the harmful one-sided positive parts; they do not estimate either
subchannel.

`proof_status = NO_PROOF`.
-/
set_option autoImplicit false

open scoped BigOperators Classical
open GoldbachCircleMethodActualOneSidedKernelLeakageV18648
open GoldbachCircleMethodExplicitOffDiagonalKernelLeakageV18649
open GoldbachCircleMethodExplicitJordanDeficitV18651
open GoldbachCircleMethodExplicitJordanParitySplitV18652

namespace GoldbachCircleMethodEvenSubchannelSplitV18660

/-- The unchanged off-diagonal pair carrier from V1.8.649--V1.8.652. -/
private def offDiagonalPairCarrier (M N : Nat) : Finset (Nat × Nat) :=
  ((Finset.range M.succ).product (Finset.range M.succ)).filter
    (fun ab => ab.1 + ab.2 ≠ N)

/-- Even-even part of the positive off-diagonal even-sum mass. -/
noncomputable def explicitPositiveEvenEvenMass
    (M P R N : Nat) : Real :=
  ∑ ab ∈ (offDiagonalPairCarrier M N).filter
      (fun ab => Even ab.1 ∧ Even ab.2),
    lambdaPairWeight ab *
      GoldbachCircleMethodExceptionalTransferV1823.negativePart
        (explicitMajorMaskSincKernel M P R
          ((N : Int) - (ab.1 : Int) - (ab.2 : Int))).re

/-- Odd-odd part of the positive off-diagonal even-sum mass. -/
noncomputable def explicitPositiveOddOddMass
    (M P R N : Nat) : Real :=
  ∑ ab ∈ (offDiagonalPairCarrier M N).filter
      (fun ab => Odd ab.1 ∧ Odd ab.2),
    lambdaPairWeight ab *
      GoldbachCircleMethodExceptionalTransferV1823.negativePart
        (explicitMajorMaskSincKernel M P R
          ((N : Int) - (ab.1 : Int) - (ab.2 : Int))).re

/-- Even-even part of the negative off-diagonal even-sum mass. -/
noncomputable def explicitNegativeEvenEvenMass
    (M P R N : Nat) : Real :=
  ∑ ab ∈ (offDiagonalPairCarrier M N).filter
      (fun ab => Even ab.1 ∧ Even ab.2),
    lambdaPairWeight ab *
      positivePart
        (explicitMajorMaskSincKernel M P R
          ((N : Int) - (ab.1 : Int) - (ab.2 : Int))).re

/-- Odd-odd part of the negative off-diagonal even-sum mass. -/
noncomputable def explicitNegativeOddOddMass
    (M P R N : Nat) : Real :=
  ∑ ab ∈ (offDiagonalPairCarrier M N).filter
      (fun ab => Odd ab.1 ∧ Odd ab.2),
    lambdaPairWeight ab *
      positivePart
        (explicitMajorMaskSincKernel M P R
          ((N : Int) - (ab.1 : Int) - (ab.2 : Int))).re

theorem explicitPositiveEvenEvenMass_nonneg (M P R N : Nat) :
    0 ≤ explicitPositiveEvenEvenMass M P R N := by
  unfold explicitPositiveEvenEvenMass
  exact Finset.sum_nonneg fun ab _ =>
    mul_nonneg (lambdaPairWeight_nonneg ab) (negativePart_nonneg _)

theorem explicitPositiveOddOddMass_nonneg (M P R N : Nat) :
    0 ≤ explicitPositiveOddOddMass M P R N := by
  unfold explicitPositiveOddOddMass
  exact Finset.sum_nonneg fun ab _ =>
    mul_nonneg (lambdaPairWeight_nonneg ab) (negativePart_nonneg _)

theorem explicitNegativeEvenEvenMass_nonneg (M P R N : Nat) :
    0 ≤ explicitNegativeEvenEvenMass M P R N := by
  unfold explicitNegativeEvenEvenMass
  exact Finset.sum_nonneg fun ab _ =>
    mul_nonneg (lambdaPairWeight_nonneg ab) (positivePart_nonneg _)

theorem explicitNegativeOddOddMass_nonneg (M P R N : Nat) :
    0 ≤ explicitNegativeOddOddMass M P R N := by
  unfold explicitNegativeOddOddMass
  exact Finset.sum_nonneg fun ab _ =>
    mul_nonneg (lambdaPairWeight_nonneg ab) (positivePart_nonneg _)

/-- Coordinates on an even diagonal have equal parity.  This theorem does not
select one of the two cases. -/
theorem even_diagonal_coordinates_same_parity
    {a b N : Nat} (hEven : Even N) (hab : a + b = N) :
    (Even a ∧ Even b) ∨ (Odd a ∧ Odd b) := by
  have hsum : Even (a + b) := hab ▸ hEven
  have hoddIff : Odd a ↔ Odd b := Nat.even_add'.mp hsum
  by_cases haOdd : Odd a
  · exact Or.inr ⟨haOdd, hoddIff.mp haOdd⟩
  · have haEven : Even a := Nat.not_odd_iff_even.mp haOdd
    have hbNotOdd : ¬ Odd b := by
      intro hbOdd
      exact haOdd (hoddIff.mpr hbOdd)
    exact Or.inl ⟨haEven, Nat.not_odd_iff_even.mp hbNotOdd⟩

/-- Finite counterexample to assigning every even diagonal to odd-odd. -/
theorem even_diagonal_not_universally_oddOdd :
    ¬ (∀ a b N : Nat, Even N → a + b = N → Odd a ∧ Odd b) := by
  intro h
  have hbad := h 2 2 4 (by norm_num) (by norm_num)
  norm_num at hbad

/-- Exact coordinate split of the positive off-diagonal even channel. -/
theorem explicitPositiveEvenSumMass_eq_evenEven_add_oddOdd
    (M P R N : Nat) :
    explicitPositiveEvenSumMass M P R N =
      explicitPositiveEvenEvenMass M P R N +
        explicitPositiveOddOddMass M P R N := by
  classical
  unfold explicitPositiveEvenSumMass explicitPositiveEvenEvenMass
    explicitPositiveOddOddMass offDiagonalPairCarrier
  let base :=
    ((Finset.range M.succ).product (Finset.range M.succ)).filter
      (fun ab : Nat × Nat => ab.1 + ab.2 ≠ N)
  let f := fun ab : Nat × Nat =>
    lambdaPairWeight ab *
      GoldbachCircleMethodExceptionalTransferV1823.negativePart
        (explicitMajorMaskSincKernel M P R
          ((N : Int) - (ab.1 : Int) - (ab.2 : Int))).re
  change
    (∑ ab ∈ base.filter (fun ab => Even (ab.1 + ab.2)), f ab) =
      (∑ ab ∈ base.filter (fun ab => Even ab.1 ∧ Even ab.2), f ab) +
        ∑ ab ∈ base.filter (fun ab => Odd ab.1 ∧ Odd ab.2), f ab
  rw [← Finset.sum_filter_add_sum_filter_not
    (base.filter (fun ab => Even (ab.1 + ab.2)))
    (fun ab => Even ab.1) f]
  congr 1
  · apply Finset.sum_congr
    · ext ab
      simp only [base, Finset.mem_filter]
      constructor
      · rintro ⟨⟨hoff, hsum⟩, haEven⟩
        have hoddIff : Odd ab.1 ↔ Odd ab.2 := Nat.even_add'.mp hsum
        have haNotOdd : ¬ Odd ab.1 := Nat.not_odd_iff_even.mpr haEven
        have hbNotOdd : ¬ Odd ab.2 := fun hb => haNotOdd (hoddIff.mpr hb)
        exact ⟨hoff, haEven, Nat.not_odd_iff_even.mp hbNotOdd⟩
      · rintro ⟨hoff, haEven, hbEven⟩
        exact ⟨⟨hoff, haEven.add hbEven⟩, haEven⟩
    · intro ab _
      rfl
  · apply Finset.sum_congr
    · ext ab
      simp only [base, Finset.mem_filter]
      constructor
      · rintro ⟨⟨hoff, hsum⟩, haNotEven⟩
        have haOdd : Odd ab.1 := Nat.not_even_iff_odd.mp haNotEven
        have hoddIff : Odd ab.1 ↔ Odd ab.2 := Nat.even_add'.mp hsum
        exact ⟨hoff, haOdd, hoddIff.mp haOdd⟩
      · rintro ⟨hoff, haOdd, hbOdd⟩
        exact ⟨⟨hoff, Nat.even_add'.mpr ⟨fun _ => hbOdd, fun _ => haOdd⟩⟩,
          Nat.not_even_iff_odd.mpr haOdd⟩
    · intro ab _
      rfl

/-- Exact coordinate split of the negative off-diagonal even channel. -/
theorem explicitNegativeEvenSumMass_eq_evenEven_add_oddOdd
    (M P R N : Nat) :
    explicitNegativeEvenSumMass M P R N =
      explicitNegativeEvenEvenMass M P R N +
        explicitNegativeOddOddMass M P R N := by
  classical
  unfold explicitNegativeEvenSumMass explicitNegativeEvenEvenMass
    explicitNegativeOddOddMass offDiagonalPairCarrier
  let base :=
    ((Finset.range M.succ).product (Finset.range M.succ)).filter
      (fun ab : Nat × Nat => ab.1 + ab.2 ≠ N)
  let f := fun ab : Nat × Nat =>
    lambdaPairWeight ab *
      positivePart
        (explicitMajorMaskSincKernel M P R
          ((N : Int) - (ab.1 : Int) - (ab.2 : Int))).re
  change
    (∑ ab ∈ base.filter (fun ab => Even (ab.1 + ab.2)), f ab) =
      (∑ ab ∈ base.filter (fun ab => Even ab.1 ∧ Even ab.2), f ab) +
        ∑ ab ∈ base.filter (fun ab => Odd ab.1 ∧ Odd ab.2), f ab
  rw [← Finset.sum_filter_add_sum_filter_not
    (base.filter (fun ab => Even (ab.1 + ab.2)))
    (fun ab => Even ab.1) f]
  congr 1
  · apply Finset.sum_congr
    · ext ab
      simp only [base, Finset.mem_filter]
      constructor
      · rintro ⟨⟨hoff, hsum⟩, haEven⟩
        have hoddIff : Odd ab.1 ↔ Odd ab.2 := Nat.even_add'.mp hsum
        have haNotOdd : ¬ Odd ab.1 := Nat.not_odd_iff_even.mpr haEven
        have hbNotOdd : ¬ Odd ab.2 := fun hb => haNotOdd (hoddIff.mpr hb)
        exact ⟨hoff, haEven, Nat.not_odd_iff_even.mp hbNotOdd⟩
      · rintro ⟨hoff, haEven, hbEven⟩
        exact ⟨⟨hoff, haEven.add hbEven⟩, haEven⟩
    · intro ab _
      rfl
  · apply Finset.sum_congr
    · ext ab
      simp only [base, Finset.mem_filter]
      constructor
      · rintro ⟨⟨hoff, hsum⟩, haNotEven⟩
        have haOdd : Odd ab.1 := Nat.not_even_iff_odd.mp haNotEven
        have hoddIff : Odd ab.1 ↔ Odd ab.2 := Nat.even_add'.mp hsum
        exact ⟨hoff, haOdd, hoddIff.mp haOdd⟩
      · rintro ⟨hoff, haOdd, hbOdd⟩
        exact ⟨⟨hoff, Nat.even_add'.mpr ⟨fun _ => hbOdd, fun _ => haOdd⟩⟩,
          Nat.not_even_iff_odd.mpr haOdd⟩
    · intro ab _
      rfl

/-- Signed even-even off-diagonal deficit. -/
noncomputable def explicitEvenEvenSubchannelDeficit
    (M P R N : Nat) : Real :=
  explicitNegativeEvenEvenMass M P R N -
    explicitPositiveEvenEvenMass M P R N

/-- Signed odd-odd off-diagonal deficit. -/
noncomputable def explicitOddOddSubchannelDeficit
    (M P R N : Nat) : Real :=
  explicitNegativeOddOddMass M P R N -
    explicitPositiveOddOddMass M P R N

/-- Exact refinement of the V1.8.652 even deficit.  The diagonal reserve is
retained as a separate subtractive term. -/
theorem explicitEvenChannelDeficit_eq_subchannels_sub_diagonal
    (M P R N : Nat) :
    explicitEvenChannelDeficit M P R N =
      explicitEvenEvenSubchannelDeficit M P R N +
        explicitOddOddSubchannelDeficit M P R N -
          explicitDiagonalPositiveReserve M P R N := by
  unfold explicitEvenChannelDeficit
  rw [explicitNegativeEvenSumMass_eq_evenEven_add_oddOdd]
  rw [explicitPositiveEvenSumMass_eq_evenEven_add_oddOdd]
  unfold explicitEvenEvenSubchannelDeficit
    explicitOddOddSubchannelDeficit
  ring

/-- The diagonal reserve can only decrease the harmful positive part. -/
theorem positivePart_explicitEvenChannelDeficit_le_subchannels
    (M P R N : Nat) :
    positivePart (explicitEvenChannelDeficit M P R N) ≤
      positivePart (explicitEvenEvenSubchannelDeficit M P R N) +
        positivePart (explicitOddOddSubchannelDeficit M P R N) := by
  rw [explicitEvenChannelDeficit_eq_subchannels_sub_diagonal]
  unfold positivePart
  apply max_le
  · have hdiag := explicitDiagonalPositiveReserve_nonneg M P R N
    have hee : explicitEvenEvenSubchannelDeficit M P R N ≤
        max (explicitEvenEvenSubchannelDeficit M P R N) 0 := le_max_left _ _
    have hoo : explicitOddOddSubchannelDeficit M P R N ≤
        max (explicitOddOddSubchannelDeficit M P R N) 0 := le_max_left _ _
    linarith
  · exact add_nonneg (le_max_right _ _) (le_max_right _ _)

/-- The harmful even-even deficit is controlled by its negative mass alone. -/
theorem positivePart_evenEvenSubchannelDeficit_le_negativeMass
    (M P R N : Nat) :
    positivePart (explicitEvenEvenSubchannelDeficit M P R N) ≤
      explicitNegativeEvenEvenMass M P R N := by
  unfold explicitEvenEvenSubchannelDeficit positivePart
  apply max_le
  · have hpos := explicitPositiveEvenEvenMass_nonneg M P R N
    linarith
  · exact explicitNegativeEvenEvenMass_nonneg M P R N

/-- The harmful odd-odd deficit is controlled by its negative mass alone. -/
theorem positivePart_oddOddSubchannelDeficit_le_negativeMass
    (M P R N : Nat) :
    positivePart (explicitOddOddSubchannelDeficit M P R N) ≤
      explicitNegativeOddOddMass M P R N := by
  unfold explicitOddOddSubchannelDeficit positivePart
  apply max_le
  · have hpos := explicitPositiveOddOddMass_nonneg M P R N
    linarith
  · exact explicitNegativeOddOddMass_nonneg M P R N

/-- Final one-sided localization: only the two negative coordinate masses can
contribute to a harmful even-channel deficit.  No numerical estimate follows. -/
theorem positivePart_explicitEvenChannelDeficit_le_negativeSubchannelMasses
    (M P R N : Nat) :
    positivePart (explicitEvenChannelDeficit M P R N) ≤
      explicitNegativeEvenEvenMass M P R N +
        explicitNegativeOddOddMass M P R N := by
  exact (positivePart_explicitEvenChannelDeficit_le_subchannels M P R N).trans
    (add_le_add
      (positivePart_evenEvenSubchannelDeficit_le_negativeMass M P R N)
      (positivePart_oddOddSubchannelDeficit_le_negativeMass M P R N))

end GoldbachCircleMethodEvenSubchannelSplitV18660
