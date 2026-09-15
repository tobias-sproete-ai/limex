import GoldbachCircleMethodActualSignedTargetResidueFiberCenteredEnergyV18696

/-!
# V1.8.697: actual signed target-residue variance/collision identity

This append-only module opens the quantitative obligation from V1.8.696
without supplying a synthetic estimate.  The exact centered target-residue
energy is identified with a same-residue collision sum over the original
finite target box minus the exact mean-square term.

The collision factors are the unchanged V1.8.695 signed residue-fiber weights,
so all imported target/fiber gates, moving notches, arithmetic fiber masses,
and sinc radii remain present.  No absolute aggregation, smallness estimate,
asymptotic statement, denominator summability, global triangle inequality,
global LCM, replacement weight, moment estimate, or Goldbach conclusion is
introduced.

`proof_status = NO_PROOF`.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodActualSignedTargetResidueVarianceCollisionIdentityV18697

open GoldbachCircleMethodOddChannelEventualAbsorptionV18658
open GoldbachCircleMethodFullDenominatorFourClassPartitionV18688
open GoldbachCircleMethodExactSignedResidueFiberAggregationBeforeGlobalTriangleV18695
open GoldbachCircleMethodActualSignedTargetResidueFiberCenteredEnergyV18696

/-- Generic exact finite variance identity over a nonempty finite type. -/
theorem finiteRealCenteredEnergy_eq_sum_sq_sub_mean_square
    {ι : Type} [Fintype ι] [Nonempty ι] (f : ι → Real) :
    (∑ i : ι,
        (f i - (∑ j : ι, f j) / (Fintype.card ι : Real)) ^ 2) =
      (∑ i : ι, f i ^ 2) -
        (∑ i : ι, f i) ^ 2 / (Fintype.card ι : Real) := by
  let S : Real := ∑ i : ι, f i
  let C : Real := Fintype.card ι
  have hC : C ≠ 0 := by
    dsimp [C]
    positivity
  calc
    (∑ i : ι, (f i - S / C) ^ 2) =
        ∑ i : ι, (f i ^ 2 - (2 * (S / C)) * f i + (S / C) ^ 2) := by
      apply Finset.sum_congr rfl
      intro i _hi
      ring
    _ = (∑ i : ι, f i ^ 2) -
          (2 * (S / C)) * (∑ i : ι, f i) +
            (Fintype.card ι : Real) * (S / C) ^ 2 := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
        Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [← Finset.mul_sum]
    _ = (∑ i : ι, f i ^ 2) - S ^ 2 / C := by
      dsimp only [S] at hC ⊢
      field_simp
      ring

/-- The V1.8.696 centered energy satisfies the exact finite variance formula
with the pair-local cardinality written explicitly as `q*r`. -/
theorem selectedPairCenteredTargetResidueFiberEnergy_eq_variance
    (M : Nat)
    (q r : PairedOddBase (oddProjectRadius M))
    (x : ZMod q.val.val) (y : ZMod r.val.val) :
    selectedPairCenteredTargetResidueFiberEnergy M q r x y =
      (∑ z : ZMod (q.val.val * r.val.val),
          selectedPairSignedTargetResidueFiber M q r x y z ^ 2) -
        (∑ z : ZMod (q.val.val * r.val.val),
          selectedPairSignedTargetResidueFiber M q r x y z) ^ 2 /
            (q.val.val * r.val.val : Real) := by
  unfold selectedPairCenteredTargetResidueFiberEnergy
    selectedPairCenteredTargetResidueFiber
    selectedPairSignedTargetResidueFiberMean
  simpa only [ZMod.card, Nat.cast_mul] using
    (finiteRealCenteredEnergy_eq_sum_sq_sub_mean_square
      (fun z : ZMod (q.val.val * r.val.val) =>
        selectedPairSignedTargetResidueFiber M q r x y z))

/-- Summing all target-residue fibers returns exactly the original finite
target sum of the unchanged signed residue-fiber weight. -/
theorem sum_signedTargetResidueFiber_eq_sum_signedResidueFiberWeight
    (M : Nat)
    (q r : PairedOddBase (oddProjectRadius M))
    (x : ZMod q.val.val) (y : ZMod r.val.val) :
    (∑ z : ZMod (q.val.val * r.val.val),
        selectedPairSignedTargetResidueFiber M q r x y z) =
      ∑ n ∈ Finset.range M.succ,
        selectedPairSignedResidueFiberWeight M q r n x y := by
  unfold selectedPairSignedTargetResidueFiber
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n _hn
  rw [Finset.sum_eq_single
    (n : ZMod (q.val.val * r.val.val))]
  · simp
  · intro z _hz hzne
    simp [Ne.symm hzne]
  · simp

/-- Squared actual target-residue fiber mass is exactly the signed collision
sum over pairs of targets in the same residue class modulo the pair-local
period `q*r`. -/
theorem sum_signedTargetResidueFiber_sq_eq_sameResidueCollision
    (M : Nat)
    (q r : PairedOddBase (oddProjectRadius M))
    (x : ZMod q.val.val) (y : ZMod r.val.val) :
    (∑ z : ZMod (q.val.val * r.val.val),
        selectedPairSignedTargetResidueFiber M q r x y z ^ 2) =
      ∑ n ∈ Finset.range M.succ,
        ∑ m ∈ Finset.range M.succ,
          if (n : ZMod (q.val.val * r.val.val)) =
              (m : ZMod (q.val.val * r.val.val)) then
            selectedPairSignedResidueFiberWeight M q r n x y *
              selectedPairSignedResidueFiberWeight M q r m x y
          else 0 := by
  unfold selectedPairSignedTargetResidueFiber
  simp_rw [pow_two, Finset.sum_mul, Finset.mul_sum]
  calc
    (∑ z : ZMod (q.val.val * r.val.val),
        ∑ n ∈ Finset.range M.succ,
          ∑ m ∈ Finset.range M.succ,
            (if (n : ZMod (q.val.val * r.val.val)) = z then
                selectedPairSignedResidueFiberWeight M q r n x y
              else 0) *
              (if (m : ZMod (q.val.val * r.val.val)) = z then
                selectedPairSignedResidueFiberWeight M q r m x y
              else 0)) =
      ∑ n ∈ Finset.range M.succ,
        ∑ z : ZMod (q.val.val * r.val.val),
          ∑ m ∈ Finset.range M.succ,
            (if (n : ZMod (q.val.val * r.val.val)) = z then
                selectedPairSignedResidueFiberWeight M q r n x y
              else 0) *
              (if (m : ZMod (q.val.val * r.val.val)) = z then
                selectedPairSignedResidueFiberWeight M q r m x y
              else 0) := by
        rw [Finset.sum_comm]
    _ = ∑ n ∈ Finset.range M.succ,
          ∑ m ∈ Finset.range M.succ,
            ∑ z : ZMod (q.val.val * r.val.val),
              (if (n : ZMod (q.val.val * r.val.val)) = z then
                  selectedPairSignedResidueFiberWeight M q r n x y
                else 0) *
                (if (m : ZMod (q.val.val * r.val.val)) = z then
                  selectedPairSignedResidueFiberWeight M q r m x y
                else 0) := by
        apply Finset.sum_congr rfl
        intro n _hn
        rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro n _hn
      apply Finset.sum_congr rfl
      intro m _hm
      by_cases hnm :
          (n : ZMod (q.val.val * r.val.val)) =
            (m : ZMod (q.val.val * r.val.val))
      · rw [if_pos hnm]
        rw [Finset.sum_eq_single
          (n : ZMod (q.val.val * r.val.val))]
        · simp [hnm]
        · intro z _hz hzne
          simp [Ne.symm hzne]
        · simp
      · rw [if_neg hnm]
        rw [Finset.sum_eq_single
          (n : ZMod (q.val.val * r.val.val))]
        · simp [Ne.symm hnm]
        · intro z _hz hzne
          simp [Ne.symm hzne]
        · simp

/-- Exact project identity: actual centered target-residue energy equals the
same-residue collision sum of the literal signed weights minus their exact
finite mean-square term. -/
theorem selectedPairCenteredTargetResidueFiberEnergy_eq_collision_sub_meanSquare
    (M : Nat)
    (q r : PairedOddBase (oddProjectRadius M))
    (x : ZMod q.val.val) (y : ZMod r.val.val) :
    selectedPairCenteredTargetResidueFiberEnergy M q r x y =
      (∑ n ∈ Finset.range M.succ,
        ∑ m ∈ Finset.range M.succ,
          if (n : ZMod (q.val.val * r.val.val)) =
              (m : ZMod (q.val.val * r.val.val)) then
            selectedPairSignedResidueFiberWeight M q r n x y *
              selectedPairSignedResidueFiberWeight M q r m x y
          else 0) -
        (∑ n ∈ Finset.range M.succ,
          selectedPairSignedResidueFiberWeight M q r n x y) ^ 2 /
            (q.val.val * r.val.val : Real) := by
  rw [selectedPairCenteredTargetResidueFiberEnergy_eq_variance]
  rw [sum_signedTargetResidueFiber_sq_eq_sameResidueCollision]
  rw [sum_signedTargetResidueFiber_eq_sum_signedResidueFiberWeight]

end GoldbachCircleMethodActualSignedTargetResidueVarianceCollisionIdentityV18697
