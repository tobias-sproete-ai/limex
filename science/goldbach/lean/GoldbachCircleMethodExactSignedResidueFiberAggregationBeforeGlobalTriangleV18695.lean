import GoldbachCircleMethodSelectedPairLiteralWeightVariationAdapterV18693

/-!
# V1.8.695: exact signed residue-fiber aggregation before global triangle

For one ordered pair of distinct selected odd bases, this append-only module
regroups the literal V1.8.692 half-grid fiber sum by the two base residues
`a mod q` and `b mod r` before any triangle inequality is applied.  The atom
is expressed on the pair-local product ring `ZMod (q*r)`, while the signed
fiber weight retains the exact target gate, both odd--odd carriers, both moving
notches, both arithmetic fiber masses, and all four original sinc radii.

No global LCM, model weight, absolute aggregation, residue-energy estimate,
denominator summability, moment estimate, exceptional-set theorem, or Goldbach
conclusion is introduced.

`proof_status = NO_PROOF`.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodExactSignedResidueFiberAggregationBeforeGlobalTriangleV18695

open GoldbachCircleMethodFiniteResiduePrefixV1866
open GoldbachCircleMethodTwoScaleEvenBlockDefectReserveV1833
open GoldbachCircleMethodOddOddSignedFiberAdapterV18665
open GoldbachCircleMethodOddChannelEventualAbsorptionV18658
open GoldbachCircleMethodFullDenominatorFourClassPartitionV18688
open GoldbachCircleMethodFullChannelPartitionedGramV18689
open GoldbachCircleMethodSelectedPairCrossCorrelationExpansionV18690
open GoldbachCircleMethodSelectedPairLocalPeriodAbelAdapterV18691
open GoldbachCircleMethodSelectedPairEvenTargetReindexV18692
open GoldbachCircleMethodSelectedPairLiteralWeightVariationAdapterV18693

/-- The exact signed pair-local atom after retaining only the base residues of
the two fiber indices.  The target coordinate remains in `ZMod (q*r)`. -/
noncomputable def selectedPairBaseResidueAtom
    {R : Nat} (q r : PairedOddBase R)
    (x : ZMod q.val.val) (y : ZMod r.val.val)
    (n : ZMod (q.val.val * r.val.val)) : Real :=
  let K := q.val.val * r.val.val
  let hq : q.val.val ∣ K := Nat.dvd_mul_right _ _
  let hr : r.val.val ∣ K := Nat.dvd_mul_left _ _
  (unitCharacterSum q.val.val
      ((2 : ZMod q.val.val) *
        (x - ZMod.castHom hq (ZMod q.val.val) n)) *
    unitCharacterSum r.val.val
      ((2 : ZMod r.val.val) *
        (ZMod.castHom hr (ZMod r.val.val) n - y))).re

/-- The V1.8.692 pair-local step-two atom depends on the fiber indices only
through `a mod q` and `b mod r`.  This is an exact identity, not an estimate. -/
theorem selectedPairEvenStepResidueAtom_eq_baseResidueAtom
    {R : Nat} (q r : PairedOddBase R)
    (a b n : ZMod (q.val.val * r.val.val)) :
    selectedPairEvenStepResidueAtom q r a b n =
      selectedPairBaseResidueAtom q r
        (ZMod.castHom (Nat.dvd_mul_right q.val.val r.val.val)
          (ZMod q.val.val) a)
        (ZMod.castHom (Nat.dvd_mul_left r.val.val q.val.val)
          (ZMod r.val.val) b)
        n := by
  unfold selectedPairEvenStepResidueAtom selectedPairBaseResidueAtom
    localPairMixedRamanujanRealAtom localPairMixedRamanujanAtom
  simp only [map_mul, map_sub, map_ofNat]
  congr 3
  · ring

/-- Natural-index specialization of the preceding residue identity. -/
theorem selectedPairEvenStepAtom_eq_baseResidueAtom
    {R : Nat} (q r : PairedOddBase R) (n a b : Nat) :
    selectedPairEvenStepAtom q r n a b =
      selectedPairBaseResidueAtom q r
        (a : ZMod q.val.val) (b : ZMod r.val.val)
        (n : ZMod (q.val.val * r.val.val)) := by
  rw [selectedPairEvenStepAtom_eq_residueAtom]
  rw [selectedPairEvenStepResidueAtom_eq_baseResidueAtom]
  simp

/-- Explicit atom invariance under the two base congruences. -/
theorem selectedPairEvenStepAtom_eq_of_baseResidues
    {R : Nat} (q r : PairedOddBase R) (n a b : Nat)
    (x : ZMod q.val.val) (y : ZMod r.val.val)
    (ha : (a : ZMod q.val.val) = x)
    (hb : (b : ZMod r.val.val) = y) :
    selectedPairEvenStepAtom q r n a b =
      selectedPairBaseResidueAtom q r x y
        (n : ZMod (q.val.val * r.val.val)) := by
  rw [selectedPairEvenStepAtom_eq_baseResidueAtom, ha, hb]

/-- Every fixed pair of base residue fibers inherits the exact complete-period
zero of the V1.8.692 step-two atom.  The representatives `x.val,y.val` are used
only to invoke the existing pair-local theorem; the result is representative
independent by the proved residue identity. -/
theorem selectedPairBaseResidueAtom_complete_period_eq_zero
    {R : Nat} (q r : PairedOddBase R)
    (hrErase : r ∈ Finset.univ.erase q)
    (x : ZMod q.val.val) (y : ZMod r.val.val) :
    ∑ n : ZMod (q.val.val * r.val.val),
      selectedPairBaseResidueAtom q r x y n = 0 := by
  have h := selectedPairEvenStepResidueAtom_complete_period_eq_zero
    q r hrErase
      (x.val : ZMod (q.val.val * r.val.val))
      (y.val : ZMod (q.val.val * r.val.val))
  calc
    (∑ n : ZMod (q.val.val * r.val.val),
        selectedPairBaseResidueAtom q r x y n) =
      ∑ n : ZMod (q.val.val * r.val.val),
        selectedPairEvenStepResidueAtom q r
          (x.val : ZMod (q.val.val * r.val.val))
          (y.val : ZMod (q.val.val * r.val.val)) n := by
      apply Finset.sum_congr rfl
      intro n _hn
      rw [selectedPairEvenStepResidueAtom_eq_baseResidueAtom]
      simp
    _ = 0 := h

/-- Signed aggregation of the literal half-grid weight over exactly one pair
of base residue fibers.  No absolute value is taken. -/
noncomputable def selectedPairSignedResidueFiberWeight
    (M : Nat)
    (q r : PairedOddBase (oddProjectRadius M))
    (n : Nat) (x : ZMod q.val.val) (y : ZMod r.val.val) : Real :=
  ∑ ab ∈ (Finset.range M.succ).product (Finset.range M.succ),
    if (ab.1 : ZMod q.val.val) = x ∧
        (ab.2 : ZMod r.val.val) = y then
      selectedPairHalfExactWeight M q r n ab.1 ab.2
    else 0

/-- Pure finite fiber-partition identity underlying the residue regrouping. -/
theorem sum_baseResidueAtom_mul_signedFiberWeight
    (M : Nat)
    (q r : PairedOddBase (oddProjectRadius M))
    (n : Nat) :
    (∑ x : ZMod q.val.val,
      ∑ y : ZMod r.val.val,
        selectedPairBaseResidueAtom q r x y
            (n : ZMod (q.val.val * r.val.val)) *
          selectedPairSignedResidueFiberWeight M q r n x y) =
      ∑ ab ∈ (Finset.range M.succ).product (Finset.range M.succ),
        selectedPairBaseResidueAtom q r
            (ab.1 : ZMod q.val.val) (ab.2 : ZMod r.val.val)
            (n : ZMod (q.val.val * r.val.val)) *
          selectedPairHalfExactWeight M q r n ab.1 ab.2 := by
  unfold selectedPairSignedResidueFiberWeight
  simp_rw [Finset.mul_sum]
  calc
    (∑ x : ZMod q.val.val,
      ∑ y : ZMod r.val.val,
        ∑ ab ∈ (Finset.range M.succ).product (Finset.range M.succ),
          selectedPairBaseResidueAtom q r x y
              (n : ZMod (q.val.val * r.val.val)) *
            (if (ab.1 : ZMod q.val.val) = x ∧
                (ab.2 : ZMod r.val.val) = y then
              selectedPairHalfExactWeight M q r n ab.1 ab.2
            else 0)) =
        ∑ x : ZMod q.val.val,
          ∑ ab ∈ (Finset.range M.succ).product (Finset.range M.succ),
            ∑ y : ZMod r.val.val,
              selectedPairBaseResidueAtom q r x y
                  (n : ZMod (q.val.val * r.val.val)) *
                (if (ab.1 : ZMod q.val.val) = x ∧
                    (ab.2 : ZMod r.val.val) = y then
                  selectedPairHalfExactWeight M q r n ab.1 ab.2
                else 0) := by
      apply Finset.sum_congr rfl
      intro x _hx
      rw [Finset.sum_comm]
    _ = ∑ ab ∈ (Finset.range M.succ).product (Finset.range M.succ),
          ∑ x : ZMod q.val.val,
            ∑ y : ZMod r.val.val,
              selectedPairBaseResidueAtom q r x y
                  (n : ZMod (q.val.val * r.val.val)) *
                (if (ab.1 : ZMod q.val.val) = x ∧
                    (ab.2 : ZMod r.val.val) = y then
                  selectedPairHalfExactWeight M q r n ab.1 ab.2
                else 0) := by
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro ab _hab
      rw [Finset.sum_eq_single (ab.1 : ZMod q.val.val)]
      · rw [Finset.sum_eq_single (ab.2 : ZMod r.val.val)]
        · simp
        · intro y _hy hyne
          simp [Ne.symm hyne]
        · simp
      · intro x _hx hxne
        simp [Ne.symm hxne]
      · simp

/-- Exact regrouping of one target slice by `(a mod q,b mod r)`.  Every signed
fiber weight is summed before any global triangle inequality. -/
theorem selectedPair_halfGrid_fiber_eq_signedResidueFibers
    (M : Nat)
    (q r : PairedOddBase (oddProjectRadius M))
    (n : Nat) :
    (∑ a ∈ Finset.range M.succ,
      ∑ b ∈ Finset.range M.succ,
        selectedPairHalfGridTerm M q r n a b) =
      ∑ x : ZMod q.val.val,
        ∑ y : ZMod r.val.val,
          selectedPairBaseResidueAtom q r x y
              (n : ZMod (q.val.val * r.val.val)) *
            selectedPairSignedResidueFiberWeight M q r n x y := by
  rw [sum_baseResidueAtom_mul_signedFiberWeight]
  rw [Finset.product_eq_sprod, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro a _ha
  apply Finset.sum_congr rfl
  intro b _hb
  unfold selectedPairHalfGridTerm
  rw [selectedPairEvenStepAtom_eq_baseResidueAtom]

/-- Exact fixed-pair correlation reindexing as a target sum of signed residue
fibers.  The original target box and all literal gates remain unchanged. -/
theorem selectedPairCrossFiberSum_eq_signedResidueFibers
    (M : Nat)
    (q r : PairedOddBase (oddProjectRadius M)) :
    (∑ N ∈ evenTargetBlock M,
      ∑ t ∈ oddOddOffDiagonalSumCarrier M N,
        ∑ u ∈ oddOddOffDiagonalSumCarrier M N,
          projectPairedBaseFiberTerm M q N t *
            projectPairedBaseFiberTerm M r N u) =
      ∑ n ∈ Finset.range M.succ,
        ∑ x : ZMod q.val.val,
          ∑ y : ZMod r.val.val,
            selectedPairBaseResidueAtom q r x y
                (n : ZMod (q.val.val * r.val.val)) *
              selectedPairSignedResidueFiberWeight M q r n x y := by
  rw [selectedPairCrossFiberSum_eq_halfGrid]
  apply Finset.sum_congr rfl
  intro n _hn
  exact selectedPair_halfGrid_fiber_eq_signedResidueFibers M q r n

/-- The full ordered off-diagonal Gram term inherits the exact residue-fiber
regrouping before every global triangle inequality. -/
theorem orderedOffDiagonalGram_eq_signedResidueFibers
    (M : Nat) :
    orderedOffDiagonalGram (evenTargetBlock M)
        (projectPairedBaseContribution M) =
      ∑ q : PairedOddBase (oddProjectRadius M),
        ∑ r ∈ Finset.univ.erase q,
          ∑ n ∈ Finset.range M.succ,
            ∑ x : ZMod q.val.val,
              ∑ y : ZMod r.val.val,
                selectedPairBaseResidueAtom q r x y
                    (n : ZMod (q.val.val * r.val.val)) *
                  selectedPairSignedResidueFiberWeight M q r n x y := by
  rw [orderedOffDiagonalGram_eq_qrntu]
  apply Finset.sum_congr rfl
  intro q _hq
  apply Finset.sum_congr rfl
  intro r _hr
  exact selectedPairCrossFiberSum_eq_signedResidueFibers M q r

end GoldbachCircleMethodExactSignedResidueFiberAggregationBeforeGlobalTriangleV18695
