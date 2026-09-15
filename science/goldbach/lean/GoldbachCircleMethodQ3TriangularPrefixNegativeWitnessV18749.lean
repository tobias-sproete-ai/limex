import GoldbachCircleMethodActualQ3PairResidueSignedTriangularGateV18748

/-!
# V1.8.749: negative witness for automatic q=3 triangular-prefix control

V1.8.748 isolates the actual denominator-three remainder with its real sign.
This append-only module tests whether two already available endpoint facts --
zero total mass and zero complete q=3 transform -- could by themselves force
that triangular remainder to be bounded.

They cannot.  On a three-point carrier the mean-zero source `(0,-A,A)` has
zero complete q=3 transform at target residue zero.  A fixed terminal-step
weight nevertheless makes the exact Abel triangular remainder equal `-A`.
Its adverse sign debit is therefore `A` and is unbounded.

The witness is a method-class obstruction.  Its weight is not claimed to be
the actual sinc weight and its source is not the actual von-Mangoldt source.
It proves no statement about Goldbach.  `proof_status = NO_PROOF`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

open scoped BigOperators Classical

namespace GoldbachCircleMethodQ3TriangularPrefixNegativeWitnessV18749

open GoldbachCircleMethodFiniteResiduePrefixV1866
open GoldbachCircleMethodActualCenteredQ3ResidueObstructionV18730

/-- Mean-zero three-point source used by the negative witness. -/
noncomputable def q3TriangularWitnessSource (A : Real) (s : Nat) : Complex :=
  if s = 1 then (-A : Real) else if s = 2 then (A : Real) else 0

/-- Fixed terminal-step weight. -/
noncomputable def q3TriangularWitnessWeight (s : Nat) : Complex :=
  if s = 2 then 1 else 0

/-- Exact Abel triangular remainder for the witness carrier. -/
noncomputable def q3TriangularWitnessRemainder (A : Real) : Complex :=
  -(∑ a ∈ Finset.range 2,
      (q3TriangularWitnessWeight (a + 1) -
        q3TriangularWitnessWeight a) *
      q3EvenStepTransform (q3TriangularWitnessSource A) 0 (a + 1))

/-- Adverse real-part debit of the witness remainder. -/
noncomputable def q3TriangularWitnessSignDebit (A : Real) : Real :=
  max 0 (-(q3TriangularWitnessRemainder A).re)

theorem q3TriangularWitnessSource_total_eq_zero (A : Real) :
    (∑ s ∈ Finset.range 3, q3TriangularWitnessSource A s) = 0 := by
  norm_num [Finset.sum_range_succ, q3TriangularWitnessSource]

/-- The complete q=3 endpoint also vanishes exactly. -/
theorem q3TriangularWitness_fullTransform_eq_zero (A : Real) :
    q3EvenStepTransform (q3TriangularWitnessSource A) 0 3 = 0 := by
  rw [q3EvenStepTransform_eq_three_mul_residueMass_sub_total]
  rw [q3TriangularWitnessSource_total_eq_zero]
  have htwo : (2 : ZMod 3) ≠ 0 := by decide
  norm_num [Finset.sum_range_succ, q3ResidueMass,
    q3TriangularWitnessSource, sameResidueThree, htwo]

/-- The intermediate prefix survives and has the unfavorable sign. -/
theorem q3TriangularWitness_prefix_two_eq (A : Real) :
    q3EvenStepTransform (q3TriangularWitnessSource A) 0 2 = (A : Complex) := by
  rw [q3EvenStepTransform_eq_three_mul_residueMass_sub_total]
  norm_num [Finset.sum_range_succ, q3ResidueMass,
    q3TriangularWitnessSource, sameResidueThree]

/-- Despite both endpoint cancellations, the triangular remainder is exactly
`-A`. -/
theorem q3TriangularWitnessRemainder_eq_neg (A : Real) :
    q3TriangularWitnessRemainder A = (-A : Real) := by
  have htwo : (2 : ZMod 3) ≠ 0 := by decide
  have hunit :
      @unitCharacterSum 3 ⟨by norm_num⟩ (2 : ZMod 3) = -1 := by
    rw [unitCharacterSum_three_eq_if_zero]
    simp [htwo]
  unfold q3TriangularWitnessRemainder q3TriangularWitnessWeight
  norm_num [Finset.sum_range_succ, q3TriangularWitness_prefix_two_eq,
    q3EvenStepTransform, q3TriangularWitnessSource, hunit]

theorem q3TriangularWitnessSignDebit_eq
    {A : Real} (hA : 0 ≤ A) :
    q3TriangularWitnessSignDebit A = A := by
  rw [q3TriangularWitnessSignDebit, q3TriangularWitnessRemainder_eq_neg]
  simp [hA]

/-- No requested ceiling can be deduced from the two endpoint cancellations
alone: the adverse triangular debit can exceed it. -/
theorem exists_zeroTotal_zeroEndpoint_triangularDebit_gt
    (B : Real) :
    ∃ A : Real,
      0 ≤ A ∧
      (∑ s ∈ Finset.range 3, q3TriangularWitnessSource A s) = 0 ∧
      q3EvenStepTransform (q3TriangularWitnessSource A) 0 3 = 0 ∧
      B < q3TriangularWitnessSignDebit A := by
  let A : Real := |B| + 1
  have hA : 0 ≤ A := by
    dsimp [A]
    positivity
  have hB : B ≤ |B| := le_abs_self B
  refine ⟨A, hA, q3TriangularWitnessSource_total_eq_zero A,
    q3TriangularWitness_fullTransform_eq_zero A, ?_⟩
  rw [q3TriangularWitnessSignDebit_eq hA]
  dsimp [A]
  linarith

/-- Universal triangular control from those endpoint facts is therefore
false as a method-class claim. -/
theorem not_forall_zeroTotal_zeroEndpoint_triangularDebit_le
    (B : Real) :
    ¬ ∀ A : Real,
      0 ≤ A →
      (∑ s ∈ Finset.range 3, q3TriangularWitnessSource A s) = 0 →
      q3EvenStepTransform (q3TriangularWitnessSource A) 0 3 = 0 →
      q3TriangularWitnessSignDebit A ≤ B := by
  intro h
  obtain ⟨A, hA, hTotal, hEndpoint, hLarge⟩ :=
    exists_zeroTotal_zeroEndpoint_triangularDebit_gt B
  exact (not_lt_of_ge (h A hA hTotal hEndpoint)) hLarge

end GoldbachCircleMethodQ3TriangularPrefixNegativeWitnessV18749
