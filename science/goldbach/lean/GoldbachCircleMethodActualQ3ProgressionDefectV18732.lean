import GoldbachCircleMethodActualCenteredQ3MassRecombinationV18731

/-!
# V1.8.732: source-bound denominator-three progression defect

V1.8.731 proves that averaging the three target residue classes cancels the
denominator-three profile but gives no pointwise estimate.  This append-only
module now identifies the exact arithmetic quantity that a pointwise estimate
would have to control for the definitionally fixed Lambda-pair source.

For each residue class, the centered mass is the uncentered source mass minus
the source mean times the exact finite class indicator mass.  Hence the q=3
actual Ramanujan prefix is exactly three times a finite arithmetic-progression
defect.  No generic global-centering argument can make that defect small.

No size estimate for the defect, no minor-arc estimate, and no Goldbach
conclusion is proved.  `proof_status = NO_PROOF`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

open scoped BigOperators Classical

namespace GoldbachCircleMethodActualQ3ProgressionDefectV18732

open GoldbachCircleMethodActualCenteredQ3ResidueObstructionV18730
open GoldbachCircleMethodActualCenteredQ3MassRecombinationV18731
open GoldbachCircleMethodExactLambdaPairSourceMeanSplitV18716
open GoldbachCircleMethodActualCenteredRamanujanPrefixAbelV18728
open GoldbachCircleMethodOddChannelEventualAbsorptionV18658
open GoldbachCircleMethodFullDenominatorFourClassPartitionV18688

/-- Exact finite indicator mass of one residue class modulo three. -/
noncomputable def q3ClassIndicatorMass (r : ZMod 3) (k : Nat) : Complex :=
  ∑ s ∈ Finset.range k, if (s : ZMod 3) = r then 1 else 0

/-- Centering an arbitrary finite complex source has an exact classwise cost:
the source mean is multiplied by the literal indicator mass of that class. -/
theorem q3ClassMass_centered_eq_sub_indicator
    (z : Nat → Complex) (mean : Complex) (r : ZMod 3) (k : Nat) :
    q3ClassMass (fun s => z s - mean) r k =
      q3ClassMass z r k - mean * q3ClassIndicatorMass r k := by
  unfold q3ClassMass q3ClassIndicatorMass
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro s _hs
  by_cases hres : (s : ZMod 3) = r
  · simp [hres]
  · simp [hres]

/-- Uncentered arithmetic source mass in one class modulo three. -/
noncomputable def actualQ3ClassMass (M : Nat) (r : ZMod 3) : Complex :=
  q3ClassMass (fun s => (actualLambdaPairSource M s : Complex)) r M.succ

/-- Exact classwise discrepancy of the actual arithmetic source from the
global finite source mean. -/
noncomputable def actualQ3ProgressionDefect
    (M : Nat) (r : ZMod 3) : Complex :=
  actualQ3ClassMass M r -
    (actualLambdaPairSourceMean M : Complex) *
      q3ClassIndicatorMass r M.succ

/-- The actual centered class mass is definitionally tied to the genuine
Lambda-pair progression defect. -/
theorem actualCenteredQ3ClassMass_eq_progressionDefect
    (M : Nat) (r : ZMod 3) :
    actualCenteredQ3ClassMass M r = actualQ3ProgressionDefect M r := by
  unfold actualCenteredQ3ClassMass actualQ3ProgressionDefect
    actualQ3ClassMass
  have h := q3ClassMass_centered_eq_sub_indicator
    (fun s => (actualLambdaPairSource M s : Complex))
    (actualLambdaPairSourceMean M : Complex) r M.succ
  simpa only [centeredActualLambdaPairSource, Complex.ofReal_sub] using h

/-- The natural-target residue mass in V1.8.730 is the same actual progression
defect, indexed by the target residue class. -/
theorem actualCenteredQ3ResidueMass_eq_progressionDefect
    (M n : Nat) :
    actualCenteredQ3ResidueMass M n =
      actualQ3ProgressionDefect M (n : ZMod 3) := by
  unfold actualCenteredQ3ResidueMass
  rw [q3ResidueMass_eq_q3ClassMass]
  exact actualCenteredQ3ClassMass_eq_progressionDefect M (n : ZMod 3)

/-- Exact source-bound q=3 formula for the canonical actual Ramanujan prefix. -/
theorem actualCenteredRamanujanPrefix_q3_eq_three_mul_progressionDefect
    (M : Nat)
    (q : PairedOddBase (oddProjectRadius M))
    (n : Nat)
    (hq : q.val.val = 3) :
    actualCenteredRamanujanPrefix M q n M.succ =
      3 * actualQ3ProgressionDefect M (n : ZMod 3) := by
  rw [actualCenteredRamanujanPrefix_q3_eq_three_mul_residueMass M q n hq]
  rw [actualCenteredQ3ResidueMass_eq_progressionDefect]

/-- The three genuine progression defects still recombine to zero.  This is
the complete average cancellation available from global centering alone. -/
theorem sum_actualQ3ProgressionDefect_eq_zero (M : Nat) :
    (∑ r : ZMod 3, actualQ3ProgressionDefect M r) = 0 := by
  rw [← show (∑ r : ZMod 3, actualCenteredQ3ClassMass M r) = 0 from
    sum_actualCenteredQ3ClassMass_eq_zero M]
  apply Finset.sum_congr rfl
  intro r _hr
  exact (actualCenteredQ3ClassMass_eq_progressionDefect M r).symm

end GoldbachCircleMethodActualQ3ProgressionDefectV18732
