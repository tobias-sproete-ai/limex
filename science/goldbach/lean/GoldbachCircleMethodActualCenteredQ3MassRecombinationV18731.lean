import GoldbachCircleMethodActualCenteredQ3ResidueObstructionV18730

/-!
# V1.8.731: exact denominator-three mass recombination and pointwise witness

This append-only module resolves the first question left open by V1.8.730.
The three residue-class masses form an exact partition of the full finite
coefficient mass.  Consequently, the three denominator-three class transforms
sum to zero.  This is a mass-preserving recombination across target residue
classes, not a pointwise cancellation theorem.

An explicit two-point coefficient source has total mass zero but a nonzero
denominator-three transform.  Thus global centering plus recombination cannot,
by itself, establish the pointwise incomplete-prefix estimate required by the
minor-arc route.

The result is exact finite algebra.  It proves no estimate for the actual
Lambda-pair residue masses, no minor-arc bound, and no Goldbach conclusion.
`proof_status = NO_PROOF`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

open scoped BigOperators Classical

namespace GoldbachCircleMethodActualCenteredQ3MassRecombinationV18731

open GoldbachCircleMethodActualCenteredQ3ResidueObstructionV18730
open GoldbachCircleMethodExactLambdaPairSourceMeanSplitV18716

/-- Coefficient mass in one literal residue class modulo three. -/
noncomputable def q3ClassMass
    (z : Nat → Complex) (r : ZMod 3) (k : Nat) : Complex :=
  ∑ s ∈ Finset.range k, if (s : ZMod 3) = r then z s else 0

/-- The natural-target mass of V1.8.730 is the corresponding class mass. -/
theorem q3ResidueMass_eq_q3ClassMass
    (z : Nat → Complex) (n k : Nat) :
    q3ResidueMass z n k = q3ClassMass z (n : ZMod 3) k := by
  unfold q3ResidueMass q3ClassMass
  apply Finset.sum_congr rfl
  intro s _hs
  by_cases hres : (s : ZMod 3) = (n : ZMod 3)
  · simp [sameResidueThree, hres]
  · simp [sameResidueThree, hres]

/-- The three residue classes partition the finite coefficient mass exactly. -/
theorem sum_q3ClassMass_eq_total
    (z : Nat → Complex) (k : Nat) :
    (∑ r : ZMod 3, q3ClassMass z r k) =
      ∑ s ∈ Finset.range k, z s := by
  unfold q3ClassMass
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _hs
  simp

/-- The class-indexed denominator-three transform after extracting its exact
residue formula. -/
noncomputable def q3ClassTransform
    (z : Nat → Complex) (r : ZMod 3) (k : Nat) : Complex :=
  3 * q3ClassMass z r k - ∑ s ∈ Finset.range k, z s

/-- The natural-target transform of V1.8.730 factors through the target class. -/
theorem q3EvenStepTransform_eq_q3ClassTransform
    (z : Nat → Complex) (n k : Nat) :
    q3EvenStepTransform z n k =
      q3ClassTransform z (n : ZMod 3) k := by
  rw [q3EvenStepTransform_eq_three_mul_residueMass_sub_total]
  rw [q3ResidueMass_eq_q3ClassMass]
  rfl

/-- Exact mass-preserving recombination: the three class transforms cancel
only after summing over all target residue classes. -/
theorem sum_q3ClassTransform_eq_zero
    (z : Nat → Complex) (k : Nat) :
    (∑ r : ZMod 3, q3ClassTransform z r k) = 0 := by
  unfold q3ClassTransform
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum,
    sum_q3ClassMass_eq_total]
  simp

/-- The definitionally fixed actual centered class mass. -/
noncomputable def actualCenteredQ3ClassMass
    (M : Nat) (r : ZMod 3) : Complex :=
  q3ClassMass
    (fun s => (centeredActualLambdaPairSource M s : Complex)) r M.succ

/-- The three actual centered class masses sum to zero because the source was
centered only at the level of its full finite mass. -/
theorem sum_actualCenteredQ3ClassMass_eq_zero (M : Nat) :
    (∑ r : ZMod 3, actualCenteredQ3ClassMass M r) = 0 := by
  have hpartition :
      (∑ r : ZMod 3, actualCenteredQ3ClassMass M r) =
      ∑ s ∈ Finset.range M.succ,
        (centeredActualLambdaPairSource M s : Complex) := by
    exact sum_q3ClassMass_eq_total
      (fun s => (centeredActualLambdaPairSource M s : Complex)) M.succ
  rw [hpartition]
  exact_mod_cast sum_centeredActualLambdaPairSource_eq_zero M

/-- A finite centered two-point source used as a negative witness. -/
def q3TwoPointWitness (s : Nat) : Complex :=
  if s = 0 then 1 else if s = 1 then -1 else 0

/-- The witness has exactly zero total mass on its complete support. -/
theorem sum_q3TwoPointWitness_eq_zero :
    (∑ s ∈ Finset.range 2, q3TwoPointWitness s) = 0 := by
  norm_num [q3TwoPointWitness, Finset.sum_range_succ]

/-- Its target-zero residue mass is nevertheless exactly one. -/
theorem q3TwoPointWitness_residueMass_zero_eq_one :
    q3ResidueMass q3TwoPointWitness 0 2 = 1 := by
  norm_num [q3ResidueMass, sameResidueThree, q3TwoPointWitness,
    Finset.sum_range_succ]

/-- Explicit obstruction: a globally centered finite source can carry a
nonzero denominator-three pointwise transform. -/
theorem q3TwoPointWitness_transform_zero_eq_three :
    q3EvenStepTransform q3TwoPointWitness 0 2 = 3 := by
  rw [q3EvenStepTransform_eq_three_mul_residueMass_sub_total,
    q3TwoPointWitness_residueMass_zero_eq_one,
    sum_q3TwoPointWitness_eq_zero]
  norm_num

theorem q3TwoPointWitness_transform_zero_ne_zero :
    q3EvenStepTransform q3TwoPointWitness 0 2 ≠ 0 := by
  rw [q3TwoPointWitness_transform_zero_eq_three]
  norm_num

end GoldbachCircleMethodActualCenteredQ3MassRecombinationV18731
