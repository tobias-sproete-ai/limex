import GoldbachCircleMethodActualSignedTargetResidueVarianceCollisionIdentityV18697

/-!
# V1.8.698: exact one-dimensional factorization of the signed residue weight

This append-only module exposes the genuine product structure already present
in the V1.8.692 literal gate.  It defines one one-dimensional half-weight for
each selected odd base, retaining the exact target gate, odd--odd fiber gate,
moving notch, arithmetic fiber mass, and the two denominator-specific sinc
radii belonging to that base.  The two-dimensional literal half-weight and
its signed base-residue fiber are then proved to factor exactly.

The V1.8.697 collision-minus-mean-square identity is specialized by this
factorization without absolute values, a global triangle inequality, a global
LCM, replacement weights, smallness, asymptotics, denominator summability,
moment estimates, or a Goldbach conclusion.

`proof_status = NO_PROOF`.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodSelectedPairSignedResidueWeightExactOneDimensionalFactorizationV18698

open GoldbachCircleMethodTwoScaleEvenBlockDefectReserveV1833
open GoldbachCircleMethodOddOddSignedFiberAdapterV18665
open GoldbachCircleMethodOddChannelEventualAbsorptionV18658
open GoldbachCircleMethodFullDenominatorFourClassPartitionV18688
open GoldbachCircleMethodSelectedPairLocalPeriodAbelAdapterV18691
open GoldbachCircleMethodSelectedPairEvenTargetReindexV18692
open GoldbachCircleMethodExactSignedResidueFiberAggregationBeforeGlobalTriangleV18695
open GoldbachCircleMethodActualSignedTargetResidueFiberCenteredEnergyV18696
open GoldbachCircleMethodActualSignedTargetResidueVarianceCollisionIdentityV18697

/-- Literal one-dimensional selected-base half-weight.  The exact target
carrier, one odd--odd fiber carrier, its moving notch, the real
`oddOddPairFiberMass`, and both sinc radii for this base are retained. -/
noncomputable def selectedPairOneFiberHalfWeight
    (M : Nat)
    (q : PairedOddBase (oddProjectRadius M))
    (n a : Nat) : Real :=
  if 2 * n ∈ evenTargetBlock M ∧
      2 * a ∈ oddOddSumCarrier M ∧ 2 * a ≠ 2 * n then
    selectedPairExactSincFiberWeight M q (2 * n) (2 * a)
  else 0

/-- Signed one-dimensional aggregation over exactly one base residue fiber. -/
noncomputable def selectedPairOneFiberSignedResidueWeight
    (M : Nat)
    (q : PairedOddBase (oddProjectRadius M))
    (n : Nat) (x : ZMod q.val.val) : Real :=
  ∑ a ∈ Finset.range M.succ,
    if (a : ZMod q.val.val) = x then
      selectedPairOneFiberHalfWeight M q n a
    else 0

/-- The exact V1.8.692 two-fiber half-weight is the product of its two literal
one-dimensional factors. -/
theorem selectedPairHalfExactWeight_eq_oneFiberHalfWeight_mul
    (M : Nat)
    (q r : PairedOddBase (oddProjectRadius M))
    (n a b : Nat) :
    selectedPairHalfExactWeight M q r n a b =
      selectedPairOneFiberHalfWeight M q n a *
        selectedPairOneFiberHalfWeight M r n b := by
  unfold selectedPairHalfExactWeight selectedPairOneFiberHalfWeight
  by_cases hN : 2 * n ∈ evenTargetBlock M
    <;> by_cases haCarrier : 2 * a ∈ oddOddSumCarrier M
    <;> by_cases haNotch : 2 * a ≠ 2 * n
    <;> by_cases hbCarrier : 2 * b ∈ oddOddSumCarrier M
    <;> by_cases hbNotch : 2 * b ≠ 2 * n
    <;> simp_all

/-- Exact factorization of the literal signed two-dimensional base-residue
fiber into the two actual one-dimensional signed residue fibers. -/
theorem selectedPairSignedResidueFiberWeight_eq_oneFiber_product
    (M : Nat)
    (q r : PairedOddBase (oddProjectRadius M))
    (n : Nat) (x : ZMod q.val.val) (y : ZMod r.val.val) :
    selectedPairSignedResidueFiberWeight M q r n x y =
      selectedPairOneFiberSignedResidueWeight M q n x *
        selectedPairOneFiberSignedResidueWeight M r n y := by
  unfold selectedPairSignedResidueFiberWeight
    selectedPairOneFiberSignedResidueWeight
  rw [Finset.product_eq_sprod, Finset.sum_product]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _haRange
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _hbRange
  rw [selectedPairHalfExactWeight_eq_oneFiberHalfWeight_mul]
  by_cases ha : (a : ZMod q.val.val) = x
  · by_cases hb : (b : ZMod r.val.val) = y
    · simp [ha, hb]
    · simp [ha, hb]
  · simp [ha]

/-- Exact specialization of the V1.8.697 project identity after the genuine
one-dimensional factorization.  Every factor remains signed. -/
theorem selectedPairCenteredTargetResidueFiberEnergy_eq_factorizedCollision_sub_meanSquare
    (M : Nat)
    (q r : PairedOddBase (oddProjectRadius M))
    (x : ZMod q.val.val) (y : ZMod r.val.val) :
    selectedPairCenteredTargetResidueFiberEnergy M q r x y =
      (∑ n ∈ Finset.range M.succ,
        ∑ m ∈ Finset.range M.succ,
          if (n : ZMod (q.val.val * r.val.val)) =
              (m : ZMod (q.val.val * r.val.val)) then
            (selectedPairOneFiberSignedResidueWeight M q n x *
                selectedPairOneFiberSignedResidueWeight M r n y) *
              (selectedPairOneFiberSignedResidueWeight M q m x *
                selectedPairOneFiberSignedResidueWeight M r m y)
          else 0) -
        (∑ n ∈ Finset.range M.succ,
          selectedPairOneFiberSignedResidueWeight M q n x *
            selectedPairOneFiberSignedResidueWeight M r n y) ^ 2 /
              (q.val.val * r.val.val : Real) := by
  rw [selectedPairCenteredTargetResidueFiberEnergy_eq_collision_sub_meanSquare]
  simp_rw [selectedPairSignedResidueFiberWeight_eq_oneFiber_product]

end GoldbachCircleMethodSelectedPairSignedResidueWeightExactOneDimensionalFactorizationV18698
