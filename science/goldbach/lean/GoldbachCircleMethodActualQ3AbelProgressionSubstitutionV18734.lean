import GoldbachCircleMethodActualQ3ProgressionDefectV18732

/-!
# V1.8.734: exact q=3 substitution inside the actual Abel identity

V1.8.732 identifies only the complete q=3 prefix with three times the actual
arithmetic-progression defect.  The Abel formula of V1.8.728 also contains all
incomplete prefixes, where global centering does not make the scalar prefix
mass vanish.  This append-only module keeps that missing term exactly.

For every prefix length `k`, the q=3 Ramanujan prefix is three times the
source-bound progression defect minus the ordinary centered source prefix.
Substitution into the finite Abel formula therefore produces two explicit
quantities: a progression-defect Abel functional and a scalar-prefix
correction.  Neither is estimated here.

No prefix bound, no mixed-channel smallness, no minor-arc absorption, and no
Goldbach conclusion is proved.  `proof_status = NO_PROOF`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

open scoped BigOperators Classical

namespace GoldbachCircleMethodActualQ3AbelProgressionSubstitutionV18734

open GoldbachCircleMethodTwoScaleEvenBlockDefectReserveV1833
open GoldbachCircleMethodOddOddSignedFiberAdapterV18665
open GoldbachCircleMethodActualCenteredQ3ResidueObstructionV18730
open GoldbachCircleMethodActualCenteredQ3MassRecombinationV18731
open GoldbachCircleMethodActualQ3ProgressionDefectV18732
open GoldbachCircleMethodActualCenteredRamanujanPrefixAbelV18728
open GoldbachCircleMethodExactLambdaPairSourceMeanSplitV18716
open GoldbachCircleMethodActualLambdaPairSourceMeanV710AdapterV18717
open GoldbachCircleMethodActualDemodulatedOneFiberRelativeConvolutionV18710
open GoldbachCircleMethodSharpSourceSincVariationV18721
open GoldbachCircleMethodSelectedPairLocalPeriodAbelAdapterV18691
open GoldbachCircleMethodActualMixedChannelRamanujanFactorizationV18727
open GoldbachCircleMethodOddChannelEventualAbsorptionV18658
open GoldbachCircleMethodFullDenominatorFourClassPartitionV18688

/-- Raw actual Lambda-pair mass in one class modulo three, on an arbitrary
finite prefix. -/
noncomputable def actualQ3ClassMassPrefix
    (M : Nat) (r : ZMod 3) (k : Nat) : Complex :=
  q3ClassMass (fun s => (actualLambdaPairSource M s : Complex)) r k

/-- The exact actual arithmetic-progression defect on an arbitrary prefix. -/
noncomputable def actualQ3ProgressionDefectPrefix
    (M : Nat) (r : ZMod 3) (k : Nat) : Complex :=
  actualQ3ClassMassPrefix M r k -
    (actualLambdaPairSourceMean M : Complex) * q3ClassIndicatorMass r k

/-- Ordinary centered actual-source prefix.  Unlike the complete prefix, this
need not vanish. -/
noncomputable def actualCenteredSourcePrefix (M k : Nat) : Complex :=
  ∑ s ∈ Finset.range k, (centeredActualLambdaPairSource M s : Complex)

/-- Centering in one residue class produces exactly the source-bound prefix
defect. -/
theorem q3ClassMass_centered_eq_actualProgressionDefectPrefix
    (M : Nat) (r : ZMod 3) (k : Nat) :
    q3ClassMass
        (fun s => (centeredActualLambdaPairSource M s : Complex)) r k =
      actualQ3ProgressionDefectPrefix M r k := by
  unfold actualQ3ProgressionDefectPrefix actualQ3ClassMassPrefix
  have h := q3ClassMass_centered_eq_sub_indicator
    (fun s => (actualLambdaPairSource M s : Complex))
    (actualLambdaPairSourceMean M : Complex) r k
  simpa only [centeredActualLambdaPairSource, Complex.ofReal_sub] using h

/-- If the selected odd denominator is three, the canonical actual prefix is
the literal denominator-three transform for every prefix length. -/
theorem actualCenteredRamanujanPrefix_eq_q3EvenStepTransform_prefix
    (M : Nat)
    (q : PairedOddBase (oddProjectRadius M))
    (n k : Nat)
    (hq : q.val.val = 3) :
    actualCenteredRamanujanPrefix M q n k =
      q3EvenStepTransform
        (fun s => (centeredActualLambdaPairSource M s : Complex)) n k := by
  unfold actualCenteredRamanujanPrefix actualCenteredRamanujanAtom
    q3EvenStepTransform
  rcases q with ⟨⟨qv, hqv⟩, hclass⟩
  dsimp at hq ⊢
  subst qv
  apply Finset.sum_congr rfl
  intro s _hs
  rfl

/-- Exact arbitrary-prefix q=3 identity.  The scalar centered prefix is the
term that the complete-prefix specialization suppresses. -/
theorem actualCenteredRamanujanPrefix_q3_eq_three_mul_defect_sub_scalarPrefix
    (M : Nat)
    (q : PairedOddBase (oddProjectRadius M))
    (n k : Nat)
    (hq : q.val.val = 3) :
    actualCenteredRamanujanPrefix M q n k =
      3 * actualQ3ProgressionDefectPrefix M (n : ZMod 3) k -
        actualCenteredSourcePrefix M k := by
  rw [actualCenteredRamanujanPrefix_eq_q3EvenStepTransform_prefix M q n k hq]
  rw [q3EvenStepTransform_eq_three_mul_residueMass_sub_total]
  rw [q3ResidueMass_eq_q3ClassMass]
  rw [q3ClassMass_centered_eq_actualProgressionDefectPrefix]
  rfl

/-- The full progression-defect contribution after finite Abel summation. -/
noncomputable def actualQ3ProgressionDefectAbelFunctional
    (M : Nat)
    (q : PairedOddBase (oddProjectRadius M))
    (n : Nat) : Complex :=
  selectedPairSourceCoordinateSincWeight M q n M *
      actualQ3ProgressionDefectPrefix M (n : ZMod 3) M.succ -
    ∑ a ∈ Finset.range M,
      selectedPairSourceCoordinateSincVariation M q n a *
        actualQ3ProgressionDefectPrefix M (n : ZMod 3) (a + 1)

/-- The exact scalar-prefix correction left by incomplete centering. -/
noncomputable def actualCenteredScalarPrefixAbelCorrection
    (M : Nat)
    (q : PairedOddBase (oddProjectRadius M))
    (n : Nat) : Complex :=
  ∑ a ∈ Finset.range M,
    selectedPairSourceCoordinateSincVariation M q n a *
      actualCenteredSourcePrefix M (a + 1)

/-- The complete scalar centered prefix is exactly zero. -/
theorem actualCenteredSourcePrefix_full_eq_zero (M : Nat) :
    actualCenteredSourcePrefix M M.succ = 0 := by
  unfold actualCenteredSourcePrefix
  exact_mod_cast sum_centeredActualLambdaPairSource_eq_zero M

/-- Finite distributive identity used to keep both Abel budgets visible. -/
theorem sum_mul_three_sub
    {A : Type*}
    (s : Finset A)
    (v d t : A → Complex) :
    (∑ a ∈ s, v a * (3 * d a - t a)) =
      3 * (∑ a ∈ s, v a * d a) - ∑ a ∈ s, v a * t a := by
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a _ha
  ring

/-- Exact q=3 Abel substitution for the negative centered unit aggregate. -/
theorem selectedPairNegativeCenteredUnitAggregate_q3_eq_defectAbel_add_scalarCorrection
    (M : Nat)
    (q : PairedOddBase (oddProjectRadius M))
    (n : Nat)
    (hTarget : 2 * n ∈ evenTargetBlock M)
    (hq : q.val.val = 3) :
    selectedPairNegativeCenteredUnitAggregate M q n =
      3 * actualQ3ProgressionDefectAbelFunctional M q n +
        actualCenteredScalarPrefixAbelCorrection M q n := by
  rw [selectedPairNegativeCenteredUnitAggregate_eq_endpoint_sub_actualCenteredRamanujanPrefixes
    M q n hTarget]
  rw [actualCenteredRamanujanPrefix_q3_eq_three_mul_defect_sub_scalarPrefix
    M q n M.succ hq]
  simp_rw [actualCenteredRamanujanPrefix_q3_eq_three_mul_defect_sub_scalarPrefix
    M q n _ hq]
  rw [actualCenteredSourcePrefix_full_eq_zero]
  unfold actualQ3ProgressionDefectAbelFunctional
    actualCenteredScalarPrefixAbelCorrection
  rw [sum_mul_three_sub]
  ring

/-- The same exact source-bound decomposition for the independently retained
positive centered unit aggregate. -/
theorem selectedPairPositiveCenteredUnitAggregate_q3_eq_defectAbel_add_scalarCorrection
    (M : Nat)
    (q : PairedOddBase (oddProjectRadius M))
    (n : Nat)
    (hTarget : 2 * n ∈ evenTargetBlock M)
    (hq : q.val.val = 3) :
    selectedPairPositiveCenteredUnitAggregate M q n =
      3 * actualQ3ProgressionDefectAbelFunctional M q n +
        actualCenteredScalarPrefixAbelCorrection M q n := by
  rw [selectedPairPositiveCenteredUnitAggregate_eq_endpoint_sub_actualCenteredRamanujanPrefixes
    M q n hTarget]
  rw [actualCenteredRamanujanPrefix_q3_eq_three_mul_defect_sub_scalarPrefix
    M q n M.succ hq]
  simp_rw [actualCenteredRamanujanPrefix_q3_eq_three_mul_defect_sub_scalarPrefix
    M q n _ hq]
  rw [actualCenteredSourcePrefix_full_eq_zero]
  unfold actualQ3ProgressionDefectAbelFunctional
    actualCenteredScalarPrefixAbelCorrection
  rw [sum_mul_three_sub]
  ring

end GoldbachCircleMethodActualQ3AbelProgressionSubstitutionV18734
